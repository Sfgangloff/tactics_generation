"""Configuration for the tactic generation pipeline."""

from dataclasses import dataclass
from typing import Optional
from pathlib import Path


@dataclass
class Config:
    """Pipeline configuration."""

    # Model settings
    model_provider: str = "anthropic"  # "anthropic", "openai", or "openrouter"
    model_name: Optional[str] = None  # If None, uses provider default

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
            elif self.model_provider == "openrouter":
                self.model_name = "anthropic/claude-3.5-sonnet"
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
        elif self.model_provider == "openrouter":
            from .models import OpenRouterModel
            return OpenRouterModel(model_name=self.model_name)
        else:
            raise ValueError(f"Unknown model provider: {self.model_provider}")


# Default configuration
DEFAULT_CONFIG = Config()
