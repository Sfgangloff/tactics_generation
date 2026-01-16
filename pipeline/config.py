"""Configuration for the tactic generation pipeline."""

from dataclasses import dataclass
from typing import Optional
from pathlib import Path


@dataclass
class Config:
    """Pipeline configuration."""

    # Model settings
    model_provider: str = "anthropic"  # "anthropic" or "openai"
    model_name: Optional[str] = None  # If None, uses provider default

    # Mathlib configuration
    use_mathlib: bool = False  # Whether generated tactics can use Mathlib

    # Repair settings
    max_repair_rounds: int = 4  # Maximum attempts to fix compilation errors
    treat_warnings_as_errors: bool = False  # Whether to fix warnings too

    # Test generation settings
    num_tests: int = 10  # Number of test theorems to generate

    # Output settings
    output_dir: str = "output"  # Directory for generated tactics

    # Project root (auto-detected if not set)
    project_root: Optional[Path] = None

    def __post_init__(self):
        # Set default model names per provider
        if self.model_name is None:
            if self.model_provider == "anthropic":
                self.model_name = "claude-sonnet-4-20250514"
            elif self.model_provider == "openai":
                self.model_name = "gpt-4o"
            else:
                raise ValueError(f"Unknown model provider: {self.model_provider}")

    def get_model(self):
        """Create and return the configured LLM model."""
        if self.model_provider == "anthropic":
            from .models import AnthropicModel
            return AnthropicModel(model_name=self.model_name)
        elif self.model_provider == "openai":
            from .models import OpenAIModel
            return OpenAIModel(model_name=self.model_name)
        else:
            raise ValueError(f"Unknown model provider: {self.model_provider}")


# Default configuration
DEFAULT_CONFIG = Config()
