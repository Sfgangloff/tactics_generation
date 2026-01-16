"""Main tactic generation orchestrator."""

import re
from pathlib import Path
from dataclasses import dataclass
from typing import Optional

from .config import Config, DEFAULT_CONFIG
from .models.base import LLMModel
from .validator import LeanValidator, ValidationResult


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

        # Determine output path
        output_path = None
        if validation.success:
            output_path = self.validator.project_root / self.config.output_dir / filename
            # Also save the specification to a separate file
            spec_path = output_path.with_suffix(".spec.md")
            self._save_specification(spec_path, tactic_name, informal_request, analysis, test_algorithm)
            print(f"Success! Tactic saved to: {output_path}")
            print(f"Specification saved to: {spec_path}")
        else:
            print(f"Failed after {repair_rounds} repair rounds.")
            print(validation.format_diagnostics())

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
        content = f"""# Tactic Specification: {tactic_name}

## Original Request

{informal_request}

## Analysis

{analysis}

## Test Generation Algorithm

{test_algorithm}
"""
        spec_path.write_text(content)
