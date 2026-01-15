"""Anthropic model implementation."""

import os
from pathlib import Path
from typing import Optional

import anthropic

from .base import LLMModel


def _find_project_root() -> Path:
    """Find project root by searching for lakefile.toml."""
    current = Path(__file__).resolve().parent
    while current != current.parent:
        if (current / "lakefile.toml").exists():
            return current
        current = current.parent
    return Path.cwd()


class AnthropicModel(LLMModel):
    """Anthropic API implementation."""

    def __init__(
        self,
        model_name: str = "claude-sonnet-4-20250514",
        api_key: Optional[str] = None,
        max_tokens: int = 8192,
    ):
        self._model_name = model_name
        self._max_tokens = max_tokens
        self._api_key = api_key or self._load_api_key()
        if not self._api_key:
            raise ValueError(
                "Anthropic API key not found. Either:\n"
                "  - Set ANTHROPIC_API_KEY environment variable, or\n"
                "  - Put your key in anthropic_key.txt"
            )
        self._client = anthropic.Anthropic(api_key=self._api_key)

    def _load_api_key(self) -> Optional[str]:
        """Load API key from environment or file."""
        # Try environment variable first
        key = os.environ.get("ANTHROPIC_API_KEY")
        if key:
            return key

        # Try key file
        key_file = _find_project_root() / "anthropic_key.txt"
        if key_file.exists():
            return key_file.read_text().strip()

        return None

    def generate(self, prompt: str, system: Optional[str] = None) -> str:
        kwargs = {
            "model": self._model_name,
            "max_tokens": self._max_tokens,
            "messages": [{"role": "user", "content": prompt}],
        }
        if system:
            kwargs["system"] = system

        response = self._client.messages.create(**kwargs)
        return response.content[0].text

    @property
    def name(self) -> str:
        return self._model_name
