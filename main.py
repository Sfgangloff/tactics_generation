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
  python main.py --provider openrouter --model google/gemini-pro "Create a tactic"
  python main.py -f request.txt --output my_tactic.lean
  python main.py --batch specifications.json
  python main.py --batch specifications.json --only Tendsto Nonzero
  python main.py --update output/my_tactic.lean --add-tests 5
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
    input_group.add_argument(
        "--batch",
        type=Path,
        help="Run batch mode with a specifications JSON file",
    )
    input_group.add_argument(
        "--update",
        type=Path,
        help="Update an existing tactic file by adding new tests",
    )

    # Model options
    parser.add_argument(
        "--provider",
        choices=["anthropic", "openai", "openrouter"],
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

    # Batch mode options
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
    parser.add_argument(
        "--report",
        type=Path,
        help="(Batch mode) Write JSON report to this file",
    )

    # Update mode options
    parser.add_argument(
        "--add-tests",
        type=int,
        default=5,
        help="(Update mode) Number of new tests to add (default: 5)",
    )

    args = parser.parse_args()

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

    # Handle batch mode
    if args.batch:
        run_batch_mode(args, config)
        return

    # Handle update mode
    if args.update:
        run_update_mode(args, config)
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


def run_batch_mode(args, config: Config):
    """Run the generator in batch mode."""
    import json
    from datetime import datetime

    if not args.batch.exists():
        print(f"Error: Specifications file not found: {args.batch}", file=sys.stderr)
        sys.exit(1)

    specifications = TacticGenerator.load_specifications(args.batch)

    # Filter specifications
    if args.only:
        specifications = {k: v for k, v in specifications.items() if k in args.only}
    if args.skip:
        specifications = {k: v for k, v in specifications.items() if k not in args.skip}

    if not specifications:
        print("No specifications to process after filtering.", file=sys.stderr)
        sys.exit(1)

    print("=" * 70)
    print("Lean Tactic Generator - Batch Mode")
    print("=" * 70)
    print()
    print(f"Specifications file: {args.batch}")
    print(f"Specifications to process: {len(specifications)}")
    for name in specifications:
        print(f"  - {name}")
    print()

    try:
        generator = TacticGenerator(config)
        batch_results = generator.generate_batch(specifications)

        # Print final summary
        print()
        print("=" * 70)
        print("FINAL SUMMARY")
        print("=" * 70)
        print()

        total_specs = len(batch_results)
        total_tactics = sum(r.total_tactics for r in batch_results)
        total_success = sum(r.successful_tactics for r in batch_results)
        total_failed = sum(r.failed_tactics for r in batch_results)

        print(f"Specifications processed: {total_specs}")
        print(f"Total tactics generated: {total_tactics}")
        print(f"Successful: {total_success}")
        print(f"Failed: {total_failed}")
        print()

        # Per-specification breakdown
        print("Per-specification breakdown:")
        print("-" * 50)
        for result in batch_results:
            status = "+" if result.failed_tactics == 0 else "-"
            print(f"  {status} {result.spec_name}: {result.successful_tactics}/{result.total_tactics} tactics")
            for gen_result in result.generation_results:
                tactic_status = "+" if gen_result.success else "-"
                print(f"      {tactic_status} {gen_result.tactic_name}")

        # Write report if requested
        if args.report:
            report = {
                "timestamp": datetime.now().isoformat(),
                "config": {
                    "provider": args.provider,
                    "model": args.model,
                    "mathlib": args.mathlib,
                    "max_rounds": args.max_rounds,
                    "num_tests": args.num_tests,
                },
                "summary": {
                    "total_specs": total_specs,
                    "total_tactics": total_tactics,
                    "successful": total_success,
                    "failed": total_failed,
                },
                "results": [
                    {
                        "spec_name": r.spec_name,
                        "is_multi_tactic": r.split_result.is_multi_tactic,
                        "split_reasoning": r.split_result.reasoning,
                        "tactics": [
                            {
                                "name": gen.tactic_name,
                                "success": gen.success,
                                "repair_rounds": gen.repair_rounds,
                                "output_path": str(gen.output_path) if gen.output_path else None,
                            }
                            for gen in r.generation_results
                        ],
                    }
                    for r in batch_results
                ],
            }
            with open(args.report, "w") as f:
                json.dump(report, f, indent=2)
            print()
            print(f"Report written to: {args.report}")

        # Exit with error if any failed
        if total_failed > 0:
            sys.exit(1)

    except ValueError as e:
        print(f"Configuration error: {e}", file=sys.stderr)
        sys.exit(1)
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        raise


def run_update_mode(args, config: Config):
    """Run the generator in update mode."""
    if not args.update.exists():
        print(f"Error: Lean file not found: {args.update}", file=sys.stderr)
        sys.exit(1)

    spec_file = args.update.with_suffix(".spec.md")
    if not spec_file.exists():
        print(f"Error: Specification file not found: {spec_file}", file=sys.stderr)
        print("Update mode requires a .spec.md file alongside the .lean file.", file=sys.stderr)
        sys.exit(1)

    print("=" * 60)
    print("Lean Tactic Generator - Update Mode")
    print("=" * 60)
    print()

    try:
        generator = TacticGenerator(config)
        result = generator.update(args.update, args.add_tests)

        print()
        print("=" * 60)
        print("Result")
        print("=" * 60)

        if result.success:
            print(f"Status: SUCCESS")
            print(f"Tactic: {result.tactic_name}")
            print(f"New tests added: {result.new_tests_added}")
            print(f"Repair rounds: {result.repair_rounds}")
            print(f"Output: {result.output_path}")
        else:
            print(f"Status: FAILED")
            print(f"Repair rounds: {result.repair_rounds}")
            print()
            print("Final errors:")
            print(result.final_validation.format_diagnostics())
            sys.exit(1)

    except ValueError as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        raise


if __name__ == "__main__":
    main()
