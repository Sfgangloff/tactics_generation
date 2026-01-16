#!/usr/bin/env python3
"""CLI entry point for the tactic generation pipeline."""

import argparse
import sys
from pathlib import Path

from pipeline import TacticGenerator, Config


def main():
    parser = argparse.ArgumentParser(
        description="Generate Lean 4 tactics from informal descriptions.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python main.py "Create a tactic that simplifies boolean expressions"
  python main.py --provider openai --mathlib "Create a tactic for finding limits"
  python main.py -f request.txt --output my_tactic.lean
        """,
    )

    # Input options
    input_group = parser.add_mutually_exclusive_group(required=True)
    input_group.add_argument(
        "request",
        nargs="?",
        help="Informal description of the tactic to generate",
    )
    input_group.add_argument(
        "-f", "--file",
        type=Path,
        help="Read request from a file",
    )

    # Model options
    parser.add_argument(
        "--provider",
        choices=["anthropic", "openai"],
        default="anthropic",
        help="LLM provider to use (default: anthropic)",
    )
    parser.add_argument(
        "--model",
        help="Specific model name (default: provider's default)",
    )

    # Configuration options
    parser.add_argument(
        "--mathlib",
        action="store_true",
        help="Enable Mathlib imports in generated tactics",
    )
    parser.add_argument(
        "--max-rounds",
        type=int,
        default=4,
        help="Maximum repair rounds (default: 4)",
    )
    parser.add_argument(
        "--strict",
        action="store_true",
        help="Treat warnings as errors",
    )
    parser.add_argument(
        "--num-tests",
        type=int,
        default=10,
        help="Number of test theorems to generate (default: 10)",
    )

    # Output options
    parser.add_argument(
        "-o", "--output",
        help="Output filename (default: auto-generated from tactic name)",
    )
    parser.add_argument(
        "--output-dir",
        default="output",
        help="Output directory (default: output)",
    )

    args = parser.parse_args()

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

    # Create configuration
    config = Config(
        model_provider=args.provider,
        model_name=args.model,
        use_mathlib=args.mathlib,
        max_repair_rounds=args.max_rounds,
        treat_warnings_as_errors=args.strict,
        num_tests=args.num_tests,
        output_dir=args.output_dir,
    )

    # Run the generator
    print("=" * 60)
    print("Lean Tactic Generator")
    print("=" * 60)
    print()
    print(f"Request: {request[:100]}{'...' if len(request) > 100 else ''}")
    print()

    try:
        generator = TacticGenerator(config)
        result = generator.generate(request)

        print()
        print("=" * 60)
        print("Result")
        print("=" * 60)

        if result.success:
            print(f"Status: SUCCESS")
            print(f"Tactic: {result.tactic_name}")
            print(f"Output: {result.output_path}")
            print(f"Repair rounds: {result.repair_rounds}")
        else:
            print(f"Status: FAILED")
            print(f"Repair rounds: {result.repair_rounds}")
            print()
            print("Final errors:")
            print(result.final_validation.format_diagnostics())
            sys.exit(1)

    except ValueError as e:
        print(f"Configuration error: {e}", file=sys.stderr)
        sys.exit(1)
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
