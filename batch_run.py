#!/usr/bin/env python3
"""Batch runner for processing specifications.json."""

import argparse
import sys
import json
from pathlib import Path
from datetime import datetime

from pipeline import TacticGenerator, Config


def main():
    parser = argparse.ArgumentParser(
        description="Generate Lean 4 tactics from specifications.json",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )

    # Input options
    parser.add_argument(
        "-s", "--specs",
        type=Path,
        default="specifications.json",
        help="Path to specifications JSON file (default: specifications.json)",
    )
    parser.add_argument(
        "--only",
        nargs="+",
        help="Only process these specification names",
    )
    parser.add_argument(
        "--skip",
        nargs="+",
        help="Skip these specification names",
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
        "--output-dir",
        default="output",
        help="Output directory (default: output)",
    )
    parser.add_argument(
        "--report",
        type=Path,
        help="Write JSON report to this file",
    )

    args = parser.parse_args()

    # Load specifications
    if not args.specs.exists():
        print(f"Error: Specifications file not found: {args.specs}", file=sys.stderr)
        sys.exit(1)

    specifications = TacticGenerator.load_specifications(args.specs)

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
    print(f"Specifications file: {args.specs}")
    print(f"Specifications to process: {len(specifications)}")
    for name in specifications:
        print(f"  - {name}")
    print()

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

    # Run batch generation
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
            status = "✓" if result.failed_tactics == 0 else "✗"
            print(f"  {status} {result.spec_name}: {result.successful_tactics}/{result.total_tactics} tactics")
            for gen_result in result.generation_results:
                tactic_status = "✓" if gen_result.success else "✗"
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


if __name__ == "__main__":
    main()
