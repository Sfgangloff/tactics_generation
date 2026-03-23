"""Main orchestrator: generates a structured specification and milestone plan."""

import re
import json
from pathlib import Path
from dataclasses import dataclass, field
from typing import Optional

from .config import Config, DEFAULT_CONFIG
from .models.base import LLMModel


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
    """Result of spec + plan generation for one tactic."""
    tactic_name: str
    spec_path: Path
    plan_path: Path
    spec_name: str = ""  # Original specification name (from JSON)


@dataclass
class BatchResult:
    """Result of batch generation from specifications.json."""
    spec_name: str
    split_result: SplitResult
    generation_results: list[GenerationResult] = field(default_factory=list)


class TacticGenerator:
    """Generates a structured specification and milestone plan from an informal request."""

    def __init__(self, config: Optional[Config] = None):
        self.config = config or DEFAULT_CONFIG
        self.model: LLMModel = self.config.get_model()
        self._load_prompts()

    def _load_prompts(self):
        prompts_dir = Path(__file__).parent / "prompts"
        self.analyze_prompt = (prompts_dir / "analyze_request.txt").read_text()
        self.plan_prompt = (prompts_dir / "generate_plan.txt").read_text()
        self.split_prompt = (prompts_dir / "split_specifications.txt").read_text()

    def generate(self, informal_request: str) -> GenerationResult:
        """Generate a spec and milestone plan from an informal request.

        Args:
            informal_request: Natural language description of the desired tactic.

        Returns:
            GenerationResult with paths to the saved spec and plan files.
        """
        print(f"Using model: {self.model.name}")
        print()

        # Step 1: Analyze the informal request → structured spec
        print("Step 1: Generating specification...")
        analysis = self._analyze_request(informal_request)
        tactic_name = self._extract_tactic_name(analysis)
        print(f"Tactic name: {tactic_name}")
        print()

        # Determine output paths
        output_dir = self._get_output_dir()
        spec_path = output_dir / f"{tactic_name}.spec.md"
        plan_path = output_dir / f"{tactic_name}.plan.md"

        # Save specification
        self._save_specification(spec_path, tactic_name, informal_request, analysis)
        print(f"Specification saved to: {spec_path}")
        print()

        # Step 2: Generate milestone plan
        print("Step 2: Generating milestone plan...")
        plan = self._generate_plan(analysis, tactic_name)
        self._save_plan(plan_path, plan)
        print(f"Plan saved to: {plan_path}")
        print()

        return GenerationResult(
            tactic_name=tactic_name,
            spec_path=spec_path,
            plan_path=plan_path,
        )

    def _analyze_request(self, request: str) -> str:
        prompt = self.analyze_prompt.replace("{request}", request)
        return self.model.generate(prompt)

    def _generate_plan(self, analysis: str, tactic_name: str) -> str:
        prompt = self.plan_prompt.replace("{specification}", analysis)
        prompt = prompt.replace("{tactic_name}", tactic_name)
        return self.model.generate(prompt)

    def _extract_tactic_name(self, analysis: str) -> str:
        match = re.search(r"Tactic Name[:\s]+`?(\w+)`?", analysis, re.IGNORECASE)
        if match:
            return match.group(1)
        return "generated_tactic"

    def _get_output_dir(self) -> Path:
        output_dir = Path(self.config.project_root) / self.config.output_dir
        output_dir.mkdir(parents=True, exist_ok=True)
        return output_dir

    def _save_specification(
        self,
        spec_path: Path,
        tactic_name: str,
        informal_request: str,
        analysis: str,
    ) -> None:
        content = f"""> **User Request:** {informal_request}

---

# Tactic Specification: {tactic_name}

## Analysis

{analysis}
"""
        spec_path.write_text(content)

    def _save_plan(self, plan_path: Path, plan: str) -> None:
        plan_path.write_text(plan)

    def split_specification(self, spec_name: str, description: str) -> SplitResult:
        """Split a specification into individual tactic specs if it describes multiple tactics."""
        prompt = self.split_prompt.replace("{spec_name}", spec_name)
        prompt = prompt.replace("{description}", description)
        response = self.model.generate(prompt)

        try:
            json_match = re.search(r'```json\s*(.*?)\s*```', response, re.DOTALL)
            json_str = json_match.group(1) if json_match else response.strip()
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
            print(f"Warning: Failed to parse split response: {e}")
            return SplitResult(
                is_multi_tactic=False,
                tactics=[TacticSpec(name=spec_name, description=description)],
                reasoning="Fallback: could not parse LLM response",
                original_name=spec_name,
                original_description=description,
            )

    def generate_from_spec(self, tactic_spec: TacticSpec, parent_spec_name: str = "") -> GenerationResult:
        result = self.generate(tactic_spec.description)
        result.spec_name = parent_spec_name or tactic_spec.name
        return result

    def generate_batch(self, specifications: dict[str, dict]) -> list[BatchResult]:
        """Generate spec + plan for each entry in a specifications dictionary."""
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

            print("\nAnalyzing specification for multiple tactics...")
            split_result = self.split_specification(spec_name, description)

            if split_result.is_multi_tactic:
                print(f"  Found {len(split_result.tactics)} distinct tactics:")
                for t in split_result.tactics:
                    print(f"    - {t.name}")
            else:
                print(f"  Single tactic: {split_result.tactics[0].name}")

            batch_result = BatchResult(spec_name=spec_name, split_result=split_result)

            for i, tactic_spec in enumerate(split_result.tactics, 1):
                print()
                print("-" * 50)
                print(f"Generating {i}/{len(split_result.tactics)}: {tactic_spec.name}")
                print("-" * 50)
                gen_result = self.generate_from_spec(tactic_spec, parent_spec_name=spec_name)
                batch_result.generation_results.append(gen_result)

            results.append(batch_result)

            print()
            print(f"Done: {spec_name} — {len(batch_result.generation_results)} tactic(s) processed")

        return results

    @staticmethod
    def load_specifications(path: Path) -> dict[str, dict]:
        with open(path) as f:
            return json.load(f)
