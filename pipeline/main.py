#!/usr/bin/env python3
"""CLI entry point for the tactic spec + plan generation pipeline."""

import argparse
import sys
from pathlib import Path

# Ensure project root is on sys.path so 'pipeline' is importable as a package
_project_root = Path(__file__).parent.parent
if str(_project_root) not in sys.path:
    sys.path.insert(0, str(_project_root))

from pipeline import TacticGenerator, Config


def main():
    parser = argparse.ArgumentParser(
        description="Generate a Lean 4 tactic specification and milestone plan from an informal description.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python pipeline/main.py "A tactic that proves nonzero goals"
  python pipeline/main.py --provider openai "A tactic for Tendsto goals"
  python pipeline/main.py --provider openrouter --model google/gemini-pro "..."
  python pipeline/main.py -f request.txt
  python pipeline/main.py --batch pipeline/specifications.json
  python pipeline/main.py --batch pipeline/specifications.json --only Tendsto Nonzero
        """,
    )

    # Input options
    input_group = parser.add_mutually_exclusive_group(required=True)
    input_group.add_argument(
        "request",
        nargs="?",
        help="Informal description of the tactic",
    )
    input_group.add_argument(
        "-f", "--file",
        type=Path,
        help="Read request from a file",
    )
    input_group.add_argument(
        "--batch",
        type=Path,
        help="Run batch mode with a specifications JSON file",
    )

    # Model options
    parser.add_argument(
        "--provider",
        choices=["anthropic", "openai", "openrouter"],
        default="anthropic",
        help="LLM provider (default: anthropic)",
    )
    parser.add_argument(
        "--model",
        help="Specific model name (default: provider's default)",
    )

    # Output options
    parser.add_argument(
        "--output-dir",
        default="output",
        help="Output directory (default: output)",
    )

    # Batch mode filters
    parser.add_argument(
        "--only",
        nargs="+",
        help="(Batch mode) Only process these specification names",
    )
    parser.add_argument(
        "--skip",
        nargs="+",
        help="(Batch mode) Skip these specification names",
    )

    args = parser.parse_args()

    config = Config(
        model_provider=args.provider,
        model_name=args.model,
        output_dir=args.output_dir,
    )

    if args.batch:
        run_batch_mode(args, config)
        return

    # Get the request
    if args.file:
        if not args.file.exists():
            print(f"Error: File not found: {args.file}", file=sys.stderr)
            sys.exit(1)
        request = args.file.read_text().strip()
    else:
        request = args.request

    if not request:
        print("Error: Empty request", file=sys.stderr)
        sys.exit(1)

    print("=" * 60)
    print("Lean Tactic Pipeline — Spec + Plan Generation")
    print("=" * 60)
    print()
    print(f"Request: {request[:100]}{'...' if len(request) > 100 else ''}")
    print()

    try:
        generator = TacticGenerator(config)
        result = generator.generate(request)

        print("=" * 60)
        print("Done")
        print("=" * 60)
        print(f"Tactic : {result.tactic_name}")
        print(f"Spec   : {result.spec_path}")
        print(f"Plan   : {result.plan_path}")

    except ValueError as e:
        print(f"Configuration error: {e}", file=sys.stderr)
        sys.exit(1)
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        raise


def run_batch_mode(args, config: Config):
    """Run the generator in batch mode."""
    if not args.batch.exists():
        print(f"Error: Specifications file not found: {args.batch}", file=sys.stderr)
        sys.exit(1)

    specifications = TacticGenerator.load_specifications(args.batch)

    if args.only:
        specifications = {k: v for k, v in specifications.items() if k in args.only}
    if args.skip:
        specifications = {k: v for k, v in specifications.items() if k not in args.skip}

    if not specifications:
        print("No specifications to process after filtering.", file=sys.stderr)
        sys.exit(1)

    print("=" * 70)
    print("Lean Tactic Pipeline — Batch Mode")
    print("=" * 70)
    print()
    print(f"Specifications file : {args.batch}")
    print(f"Specifications      : {len(specifications)}")
    for name in specifications:
        print(f"  - {name}")
    print()

    try:
        generator = TacticGenerator(config)
        batch_results = generator.generate_batch(specifications)

        print()
        print("=" * 70)
        print("SUMMARY")
        print("=" * 70)
        total = sum(len(r.generation_results) for r in batch_results)
        print(f"Specifications processed : {len(batch_results)}")
        print(f"Tactics generated        : {total}")
        for r in batch_results:
            for gen in r.generation_results:
                print(f"  {gen.tactic_name}")
                print(f"    spec : {gen.spec_path}")
                print(f"    plan : {gen.plan_path}")

    except ValueError as e:
        print(f"Configuration error: {e}", file=sys.stderr)
        sys.exit(1)
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        raise


if __name__ == "__main__":
    main()
