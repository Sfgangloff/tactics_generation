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
    analysis: str  # The structured analysis of the request


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
        print()

        # Step 1: Analyze the informal request
        print("Step 1: Analyzing request...")
        analysis = self._analyze_request(informal_request)
        print("Analysis complete.")
        print()

        # Step 2: Generate initial tactic code
        print("Step 2: Generating tactic code...")
        code = self._generate_tactic(analysis)
        print("Initial code generated.")
        print()

        # Extract tactic name from analysis or code
        tactic_name = self._extract_tactic_name(analysis, code)
        filename = f"{tactic_name}.lean"

        # Step 3: Validate and repair
        print("Step 3: Validating code...")
        code, validation, repair_rounds = self._validate_and_repair(code, filename)

        # Determine output path
        output_path = None
        if validation.success:
            output_path = self.validator.project_root / self.config.output_dir / filename
            print(f"Success! Tactic saved to: {output_path}")
        else:
            print(f"Failed after {repair_rounds} repair rounds.")
            print(validation.format_diagnostics())

        return GenerationResult(
            success=validation.success,
            tactic_name=tactic_name,
            code=code,
            output_path=output_path,
            repair_rounds=repair_rounds,
            final_validation=validation,
            analysis=analysis,
        )

    def _analyze_request(self, request: str) -> str:
        """Analyze the informal request to extract structured information."""
        prompt = self.analyze_prompt.format(request=request)
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

        prompt = self.generate_prompt.format(
            specification=analysis,
            use_mathlib="Yes" if self.config.use_mathlib else "No",
            mathlib_section=mathlib_section,
        )
        response = self.model.generate(prompt)

        # Clean up response (remove markdown code blocks if present)
        return self._clean_code(response)

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
        prompt = self.fix_prompt.format(
            code=code,
            errors=validation.format_diagnostics(),
        )
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
