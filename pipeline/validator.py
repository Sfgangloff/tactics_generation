"""Lean code validation via Lake compilation."""

import subprocess
import re
from pathlib import Path
from dataclasses import dataclass
from typing import Optional


@dataclass
class ValidationResult:
    """Result of Lean code validation."""

    success: bool
    errors: list[str]
    warnings: list[str]
    output: str

    @property
    def has_errors(self) -> bool:
        return len(self.errors) > 0

    @property
    def has_warnings(self) -> bool:
        return len(self.warnings) > 0

    def format_diagnostics(self) -> str:
        """Format errors and warnings for display."""
        lines = []
        if self.errors:
            lines.append("Errors:")
            for err in self.errors:
                lines.append(f"  {err}")
        if self.warnings:
            lines.append("Warnings:")
            for warn in self.warnings:
                lines.append(f"  {warn}")
        return "\n".join(lines)


class LeanValidator:
    """Validates Lean code by compiling with Lake."""

    def __init__(self, project_root: Optional[Path] = None):
        """Initialize the validator.

        Args:
            project_root: Path to the Lean project root (containing lakefile.toml).
                         If None, will search upward from current directory.
        """
        self.project_root = project_root or self._find_project_root()

    def _find_project_root(self) -> Path:
        """Find the Lean project root by searching for lakefile.toml."""
        current = Path.cwd()
        while current != current.parent:
            if (current / "lakefile.toml").exists() or (current / "lakefile.lean").exists():
                return current
            current = current.parent
        raise FileNotFoundError("Could not find Lean project root (lakefile.toml)")

    def validate(self, code: str, filename: str = "GeneratedTactic.lean") -> ValidationResult:
        """Validate Lean code by writing to file and compiling.

        Args:
            code: The Lean code to validate.
            filename: Name for the temporary Lean file.

        Returns:
            ValidationResult with success status and diagnostics.
        """
        # Write code to output directory
        output_dir = self.project_root / "output"
        output_dir.mkdir(exist_ok=True)
        file_path = output_dir / filename

        file_path.write_text(code)

        # Run lake env lean to compile
        try:
            result = subprocess.run(
                ["lake", "env", "lean", str(file_path)],
                cwd=self.project_root,
                capture_output=True,
                text=True,
                timeout=120,
            )
            output = result.stdout + result.stderr
            errors, warnings = self._parse_diagnostics(output)

            return ValidationResult(
                success=result.returncode == 0 and len(errors) == 0,
                errors=errors,
                warnings=warnings,
                output=output,
            )
        except subprocess.TimeoutExpired:
            return ValidationResult(
                success=False,
                errors=["Compilation timed out after 120 seconds"],
                warnings=[],
                output="",
            )
        except FileNotFoundError:
            return ValidationResult(
                success=False,
                errors=["Lake not found. Ensure Lean 4 is installed and in PATH."],
                warnings=[],
                output="",
            )

    def _parse_diagnostics(self, output: str) -> tuple[list[str], list[str]]:
        """Parse compilation output for errors and warnings."""
        errors = []
        warnings = []

        # Pattern: file:line:col: error/warning: message
        pattern = r"^(.+?):(\d+):(\d+):\s*(error|warning):\s*(.+)$"

        for line in output.split("\n"):
            match = re.match(pattern, line)
            if match:
                _, line_num, col, level, message = match.groups()
                formatted = f"Line {line_num}:{col}: {message}"
                if level == "error":
                    errors.append(formatted)
                else:
                    warnings.append(formatted)

        # Also catch general error messages
        if "error:" in output.lower() and not errors:
            for line in output.split("\n"):
                if "error:" in line.lower():
                    errors.append(line.strip())

        return errors, warnings
