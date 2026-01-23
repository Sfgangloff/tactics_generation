"""Main tactic generation orchestrator."""

import re
import json
from pathlib import Path
from dataclasses import dataclass, field
from typing import Optional

from .config import Config, DEFAULT_CONFIG
from .models.base import LLMModel
from .validator import LeanValidator, ValidationResult


@dataclass
class TacticSpec:
    """A single tactic specification extracted from a user request."""
    name: str
    description: str


@dataclass
class SplitResult:
    """Result of splitting a multi-tactic specification."""
    is_multi_tactic: bool
    tactics: list[TacticSpec]
    reasoning: str
    original_name: str
    original_description: str


@dataclass
class GenerationResult:
    """Result of tactic generation."""

    success: bool
    tactic_name: str
    code: str
    output_path: Optional[Path]
    repair_rounds: int
    final_validation: ValidationResult
    analysis: str
    test_algorithm: str  # The test generation algorithm
    spec_name: str = ""  # Original specification name (from JSON)


@dataclass
class BatchResult:
    """Result of batch generation from specifications.json."""
    spec_name: str
    split_result: SplitResult
    generation_results: list[GenerationResult] = field(default_factory=list)

    @property
    def total_tactics(self) -> int:
        return len(self.split_result.tactics)

    @property
    def successful_tactics(self) -> int:
        return sum(1 for r in self.generation_results if r.success)

    @property
    def failed_tactics(self) -> int:
        return sum(1 for r in self.generation_results if not r.success)


@dataclass
class UpdateResult:
    """Result of updating an existing tactic with new tests."""
    success: bool
    tactic_name: str
    code: str
    output_path: Path
    new_tests_added: int
    repair_rounds: int
    final_validation: ValidationResult


class TacticGenerator:
    """Orchestrates the tactic generation pipeline."""

    def __init__(self, config: Optional[Config] = None):
        """Initialize the generator.

        Args:
            config: Pipeline configuration. Uses defaults if not provided.
        """
        self.config = config or DEFAULT_CONFIG
        self.model: LLMModel = self.config.get_model()
        self.validator = LeanValidator(project_root=self.config.project_root)
        self._load_prompts()

    def _load_prompts(self):
        """Load prompt templates from files."""
        prompts_dir = Path(__file__).parent / "prompts"

        self.analyze_prompt = (prompts_dir / "analyze_request.txt").read_text()
        self.generate_prompt = (prompts_dir / "generate_tactic.txt").read_text()
        self.test_algorithm_prompt = (prompts_dir / "generate_test_algorithm.txt").read_text()
        self.generate_tests_prompt = (prompts_dir / "generate_tests.txt").read_text()
        self.fix_prompt = (prompts_dir / "fix_errors.txt").read_text()
        self.split_prompt = (prompts_dir / "split_specifications.txt").read_text()
        self.additional_tests_prompt = (prompts_dir / "generate_additional_tests.txt").read_text()
        self.update_tactic_prompt = (prompts_dir / "update_tactic.txt").read_text()

    def generate(self, informal_request: str) -> GenerationResult:
        """Generate a tactic from an informal request.

        Args:
            informal_request: Natural language description of the desired tactic.

        Returns:
            GenerationResult with the generated code and validation status.
        """
        print(f"Using model: {self.model.name}")
        print(f"Mathlib enabled: {self.config.use_mathlib}")
        print(f"Number of tests: {self.config.num_tests}")
        print()

        # Step 1: Analyze the informal request
        print("Step 1: Analyzing request...")
        analysis = self._analyze_request(informal_request)
        print("Analysis complete.")
        print()

        # Step 2: Generate test algorithm
        print("Step 2: Generating test algorithm...")
        test_algorithm = self._generate_test_algorithm(analysis)
        print("Test algorithm generated.")
        print()

        # Step 3: Generate tactic code (without tests)
        print("Step 3: Generating tactic code...")
        tactic_code = self._generate_tactic(analysis)
        print("Tactic code generated.")
        print()

        # Extract tactic name from analysis or code
        tactic_name = self._extract_tactic_name(analysis, tactic_code)
        filename = f"{tactic_name}.lean"

        # Step 4: Generate tests using the algorithm
        print(f"Step 4: Generating {self.config.num_tests} tests...")
        tests_code = self._generate_tests(tactic_name, analysis, test_algorithm)
        print("Tests generated.")
        print()

        # Step 5: Combine tactic and tests
        full_code = self._combine_tactic_and_tests(tactic_code, tests_code)

        # Step 6: Validate and repair
        print("Step 5: Validating code...")
        full_code, validation, repair_rounds = self._validate_and_repair(full_code, filename)

        # Determine output path and always save spec (useful for debugging failed attempts)
        output_path = self.validator.project_root / self.config.output_dir / filename
        spec_path = output_path.with_suffix(".spec.md")
        self._save_specification(spec_path, tactic_name, informal_request, analysis, test_algorithm)

        if validation.success:
            print(f"Success! Tactic saved to: {output_path}")
            print(f"Specification saved to: {spec_path}")
        else:
            print(f"Failed after {repair_rounds} repair rounds.")
            print(validation.format_diagnostics())
            print(f"Specification saved to: {spec_path}")
            output_path = None  # Mark as failed

        return GenerationResult(
            success=validation.success,
            tactic_name=tactic_name,
            code=full_code,
            output_path=output_path,
            repair_rounds=repair_rounds,
            final_validation=validation,
            analysis=analysis,
            test_algorithm=test_algorithm,
        )

    def _analyze_request(self, request: str) -> str:
        """Analyze the informal request to extract structured information."""
        prompt = self.analyze_prompt.replace("{request}", request)
        return self.model.generate(prompt)

    def _generate_test_algorithm(self, analysis: str) -> str:
        """Generate a test algorithm based on the specification."""
        # Use replace instead of format to handle curly braces in analysis
        prompt = self.test_algorithm_prompt.replace("{specification}", analysis)
        return self.model.generate(prompt)

    def _generate_tactic(self, analysis: str) -> str:
        """Generate tactic code from the structured analysis."""
        # Build mathlib section based on config
        if self.config.use_mathlib:
            mathlib_section = """
### Mathlib Integration

When using Mathlib, you can leverage:
- Existing tactics: `simp`, `ring`, `linarith`, `omega`, `aesop`, `norm_num`
- Type classes: `Ring`, `Field`, `TopologicalSpace`, etc.
- Common lemmas and theorems from the library

Import Mathlib modules as needed:
```lean
import Mathlib.Tactic
import Mathlib.Topology.Basic
-- etc.
```
"""
        else:
            mathlib_section = """
### Note: Mathlib Not Available

This tactic should only use:
- Core Lean 4 libraries
- The Batteries library (`import Batteries`)

Do not import Mathlib modules.
"""

        # Use replace instead of format to handle curly braces in analysis
        prompt = self.generate_prompt.replace("{specification}", analysis)
        prompt = prompt.replace("{use_mathlib}", "Yes" if self.config.use_mathlib else "No")
        prompt = prompt.replace("{mathlib_section}", mathlib_section)
        response = self.model.generate(prompt)

        # Clean up response (remove markdown code blocks if present)
        return self._clean_code(response)

    def _generate_tests(self, tactic_name: str, analysis: str, test_algorithm: str) -> str:
        """Generate test theorems using the test algorithm."""
        # Use replace instead of format to handle curly braces in analysis/algorithm
        prompt = self.generate_tests_prompt.replace("{num_tests}", str(self.config.num_tests))
        prompt = prompt.replace("{tactic_name}", tactic_name)
        prompt = prompt.replace("{specification}", analysis)
        prompt = prompt.replace("{test_algorithm}", test_algorithm)
        response = self.model.generate(prompt)
        return self._clean_code(response)

    def _combine_tactic_and_tests(self, tactic_code: str, tests_code: str) -> str:
        """Combine the tactic code with generated tests."""
        return f"{tactic_code}\n\n-- Generated tests\n{tests_code}"

    def _validate_and_repair(
        self, code: str, filename: str
    ) -> tuple[str, ValidationResult, int]:
        """Validate code and attempt repairs if needed."""
        repair_round = 0

        while repair_round <= self.config.max_repair_rounds:
            validation = self.validator.validate(code, filename)

            # Check if we need to repair
            needs_repair = validation.has_errors
            if self.config.treat_warnings_as_errors:
                needs_repair = needs_repair or validation.has_warnings

            if not needs_repair:
                return code, validation, repair_round

            if repair_round == self.config.max_repair_rounds:
                break

            # Attempt repair
            repair_round += 1
            print(f"  Repair round {repair_round}/{self.config.max_repair_rounds}...")
            code = self._repair_code(code, validation)

        return code, validation, repair_round

    def _repair_code(self, code: str, validation: ValidationResult) -> str:
        """Attempt to repair code based on compilation errors."""
        # Use replace instead of format to handle curly braces in code
        prompt = self.fix_prompt.replace("{code}", code)
        prompt = prompt.replace("{errors}", validation.format_diagnostics())
        response = self.model.generate(prompt)
        return self._clean_code(response)

    def _clean_code(self, code: str) -> str:
        """Remove markdown code blocks and clean up generated code."""
        # Remove ```lean ... ``` blocks
        code = re.sub(r"```lean\n?", "", code)
        code = re.sub(r"```\n?", "", code)
        return code.strip()

    def _extract_tactic_name(self, analysis: str, code: str) -> str:
        """Extract the tactic name from analysis or code."""
        # Try to find 'def xxx : TacticM' pattern in code
        match = re.search(r'def\s+(\w+)\s*:\s*TacticM', code)
        if match:
            return match.group(1)

        # Try to find 'elab "tactic_name"' pattern in code
        match = re.search(r'elab\s+"(\w+)"', code)
        if match:
            return match.group(1)

        # Try to find 'Tactic Name:' in analysis
        match = re.search(r"Tactic Name[:\s]+(\w+)", analysis, re.IGNORECASE)
        if match:
            return match.group(1)

        # Default name
        return "generated_tactic"

    def _save_specification(
        self,
        spec_path: Path,
        tactic_name: str,
        informal_request: str,
        analysis: str,
        test_algorithm: str,
    ) -> None:
        """Save the tactic specification to a markdown file."""
        content = f"""> **User Request:** {informal_request}

---

# Tactic Specification: {tactic_name}

## Analysis

{analysis}

## Test Generation Algorithm

{test_algorithm}
"""
        spec_path.write_text(content)

    def split_specification(self, spec_name: str, description: str) -> SplitResult:
        """Split a specification into individual tactic specifications if needed.

        Args:
            spec_name: Name of the specification (e.g., "PolynomialComputation")
            description: The user's description which may contain multiple tactics

        Returns:
            SplitResult containing individual tactic specifications
        """
        prompt = self.split_prompt.replace("{spec_name}", spec_name)
        prompt = prompt.replace("{description}", description)

        response = self.model.generate(prompt)

        # Parse JSON from response
        try:
            # Extract JSON from response (may be wrapped in markdown)
            json_match = re.search(r'```json\s*(.*?)\s*```', response, re.DOTALL)
            if json_match:
                json_str = json_match.group(1)
            else:
                # Try to find raw JSON
                json_str = response.strip()

            data = json.loads(json_str)

            tactics = [
                TacticSpec(name=t["name"], description=t["description"])
                for t in data["tactics"]
            ]

            return SplitResult(
                is_multi_tactic=data["is_multi_tactic"],
                tactics=tactics,
                reasoning=data.get("reasoning", ""),
                original_name=spec_name,
                original_description=description,
            )
        except (json.JSONDecodeError, KeyError) as e:
            # Fallback: treat as single tactic
            print(f"Warning: Failed to parse split response: {e}")
            return SplitResult(
                is_multi_tactic=False,
                tactics=[TacticSpec(name=spec_name, description=description)],
                reasoning="Fallback: could not parse LLM response",
                original_name=spec_name,
                original_description=description,
            )

    def generate_from_spec(self, tactic_spec: TacticSpec, parent_spec_name: str = "") -> GenerationResult:
        """Generate a tactic from a TacticSpec.

        Args:
            tactic_spec: The individual tactic specification
            parent_spec_name: Name of the parent specification (for grouping)

        Returns:
            GenerationResult for this tactic
        """
        result = self.generate(tactic_spec.description)
        result.spec_name = parent_spec_name or tactic_spec.name
        return result

    def generate_batch(self, specifications: dict[str, dict]) -> list[BatchResult]:
        """Generate tactics from a specifications dictionary.

        Args:
            specifications: Dictionary from specifications.json with format:
                {"SpecName": {"description": "..."}, ...}

        Returns:
            List of BatchResult, one per specification in the input
        """
        results = []

        for spec_name, spec_data in specifications.items():
            description = spec_data.get("description", "")
            if not description:
                print(f"Skipping {spec_name}: no description")
                continue

            print()
            print("=" * 70)
            print(f"Processing specification: {spec_name}")
            print("=" * 70)

            # Step 1: Split specification
            print("\nStep 0: Analyzing specification for multiple tactics...")
            split_result = self.split_specification(spec_name, description)

            if split_result.is_multi_tactic:
                print(f"  Found {len(split_result.tactics)} distinct tactics:")
                for t in split_result.tactics:
                    print(f"    - {t.name}")
            else:
                print(f"  Single tactic: {split_result.tactics[0].name}")

            batch_result = BatchResult(
                spec_name=spec_name,
                split_result=split_result,
            )

            # Step 2: Generate each tactic
            for i, tactic_spec in enumerate(split_result.tactics, 1):
                print()
                print("-" * 50)
                print(f"Generating tactic {i}/{len(split_result.tactics)}: {tactic_spec.name}")
                print("-" * 50)

                gen_result = self.generate_from_spec(tactic_spec, parent_spec_name=spec_name)
                batch_result.generation_results.append(gen_result)

            results.append(batch_result)

            # Summary for this specification
            print()
            print(f"Summary for {spec_name}:")
            print(f"  Total tactics: {batch_result.total_tactics}")
            print(f"  Successful: {batch_result.successful_tactics}")
            print(f"  Failed: {batch_result.failed_tactics}")

        return results

    @staticmethod
    def load_specifications(path: Path) -> dict[str, dict]:
        """Load specifications from a JSON file.

        Args:
            path: Path to specifications.json

        Returns:
            Dictionary of specifications
        """
        with open(path) as f:
            return json.load(f)

    def update(self, lean_file: Path, num_new_tests: int) -> UpdateResult:
        """Update an existing tactic by adding new tests and fixing the implementation.

        Args:
            lean_file: Path to the existing .lean tactic file
            num_new_tests: Number of new tests to add

        Returns:
            UpdateResult with the updated code and validation status
        """
        print(f"Using model: {self.model.name}")
        print(f"Lean file: {lean_file}")
        print(f"New tests to add: {num_new_tests}")
        print()

        # Load the existing code and specification
        if not lean_file.exists():
            raise ValueError(f"Lean file not found: {lean_file}")

        spec_file = lean_file.with_suffix(".spec.md")
        if not spec_file.exists():
            raise ValueError(f"Specification file not found: {spec_file}")

        current_code = lean_file.read_text()
        spec_content = spec_file.read_text()

        # Parse the specification file
        analysis, test_algorithm = self._parse_spec_file(spec_content)

        # Extract tactic name from code
        tactic_name = self._extract_tactic_name(analysis, current_code)
        print(f"Tactic name: {tactic_name}")
        print()

        # Extract existing tests from code
        existing_tests = self._extract_tests(current_code)
        print(f"Existing tests found: {len(existing_tests.splitlines())}")
        print()

        # Step 1: Generate additional tests
        print(f"Step 1: Generating {num_new_tests} additional tests...")
        new_tests = self._generate_additional_tests(
            tactic_name, analysis, test_algorithm, existing_tests, num_new_tests
        )
        print("Additional tests generated.")
        print()

        # Step 2: Append new tests to the code
        updated_code = self._append_tests(current_code, new_tests)

        # Step 3: Validate and repair
        print("Step 2: Validating updated code...")
        filename = lean_file.name
        updated_code, validation, repair_rounds = self._validate_and_repair_update(
            updated_code, filename, analysis
        )

        # Save the updated file
        if validation.success:
            lean_file.write_text(updated_code)
            print(f"Success! Updated tactic saved to: {lean_file}")
        else:
            print(f"Failed after {repair_rounds} repair rounds.")
            print(validation.format_diagnostics())

        return UpdateResult(
            success=validation.success,
            tactic_name=tactic_name,
            code=updated_code,
            output_path=lean_file,
            new_tests_added=num_new_tests,
            repair_rounds=repair_rounds,
            final_validation=validation,
        )

    def _parse_spec_file(self, spec_content: str) -> tuple[str, str]:
        """Parse a .spec.md file to extract analysis and test algorithm.

        Args:
            spec_content: Content of the .spec.md file

        Returns:
            Tuple of (analysis, test_algorithm)
        """
        # Extract Analysis section
        analysis_match = re.search(
            r'## Analysis\s*\n(.*?)(?=\n## |\Z)',
            spec_content,
            re.DOTALL
        )
        analysis = analysis_match.group(1).strip() if analysis_match else ""

        # Extract Test Generation Algorithm section
        algo_match = re.search(
            r'## Test Generation Algorithm\s*\n(.*?)(?=\n## |\Z)',
            spec_content,
            re.DOTALL
        )
        test_algorithm = algo_match.group(1).strip() if algo_match else ""

        return analysis, test_algorithm

    def _extract_tests(self, code: str) -> str:
        """Extract existing test theorems from the code.

        Args:
            code: The Lean source code

        Returns:
            String containing all theorem declarations
        """
        # Find all theorem/example declarations that use run_tac
        test_pattern = r'(theorem\s+\w+.*?:=\s*by\s+run_tac\s+\w+)'
        tests = re.findall(test_pattern, code, re.DOTALL)
        return "\n\n".join(tests)

    def _generate_additional_tests(
        self,
        tactic_name: str,
        analysis: str,
        test_algorithm: str,
        existing_tests: str,
        num_tests: int,
    ) -> str:
        """Generate additional non-duplicate tests.

        Args:
            tactic_name: Name of the tactic
            analysis: The tactic specification analysis
            test_algorithm: The test generation algorithm
            existing_tests: Existing tests in the file
            num_tests: Number of new tests to generate

        Returns:
            String containing new test theorems
        """
        prompt = self.additional_tests_prompt.replace("{specification}", analysis)
        prompt = prompt.replace("{test_algorithm}", test_algorithm)
        prompt = prompt.replace("{existing_tests}", existing_tests)
        prompt = prompt.replace("{num_tests}", str(num_tests))
        prompt = prompt.replace("{tactic_name}", tactic_name)

        response = self.model.generate(prompt)
        return self._clean_code(response)

    def _append_tests(self, code: str, new_tests: str) -> str:
        """Append new tests to the existing code.

        Args:
            code: The existing Lean code
            new_tests: New test theorems to add

        Returns:
            Updated code with new tests appended
        """
        return f"{code.rstrip()}\n\n-- Additional tests\n{new_tests}"

    def _validate_and_repair_update(
        self, code: str, filename: str, specification: str
    ) -> tuple[str, ValidationResult, int]:
        """Validate updated code and attempt repairs if needed.

        This uses a specialized repair prompt that understands the update context.
        """
        repair_round = 0

        while repair_round <= self.config.max_repair_rounds:
            validation = self.validator.validate(code, filename)

            # Check if we need to repair
            needs_repair = validation.has_errors
            if self.config.treat_warnings_as_errors:
                needs_repair = needs_repair or validation.has_warnings

            if not needs_repair:
                return code, validation, repair_round

            if repair_round == self.config.max_repair_rounds:
                break

            # Attempt repair using update-specific prompt
            repair_round += 1
            print(f"  Repair round {repair_round}/{self.config.max_repair_rounds}...")
            code = self._repair_update(code, validation, specification)

        return code, validation, repair_round

    def _repair_update(self, code: str, validation: ValidationResult, specification: str) -> str:
        """Attempt to repair updated code based on compilation errors.

        Uses the update-specific prompt that preserves file structure.
        """
        prompt = self.update_tactic_prompt.replace("{specification}", specification)
        prompt = prompt.replace("{current_code}", code)
        prompt = prompt.replace("{errors}", validation.format_diagnostics())
        response = self.model.generate(prompt)
        return self._clean_code(response)
