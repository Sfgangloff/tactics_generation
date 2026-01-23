"""OpenRouter model implementation."""

import os
from pathlib import Path
from typing import Optional

from openai import OpenAI

from .base import LLMModel


def _find_project_root() -> Path:
    """Find project root by searching for lakefile.toml."""
    current = Path(__file__).resolve().parent
    while current != current.parent:
        if (current / "lakefile.toml").exists():
            return current
        current = current.parent
    return Path.cwd()


class OpenRouterModel(LLMModel):
    """OpenRouter API implementation.

    OpenRouter provides access to many models through a unified API.
    Uses the OpenAI SDK with a custom base URL.
    """

    BASE_URL = "https://openrouter.ai/api/v1"

    def __init__(
        self,
        model_name: str = "anthropic/claude-3.5-sonnet",
        api_key: Optional[str] = None,
    ):
        self._model_name = model_name
        self._api_key = api_key or self._load_api_key()
        if not self._api_key:
            raise ValueError(
                "OpenRouter API key not found. Either:\n"
                "  - Set OPENROUTER_API_KEY environment variable, or\n"
                "  - Put your key in openrouter_key.txt"
            )
        self._client = OpenAI(
            api_key=self._api_key,
            base_url=self.BASE_URL,
        )

    def _load_api_key(self) -> Optional[str]:
        """Load API key from environment or file."""
        # Try environment variable first
        key = os.environ.get("OPENROUTER_API_KEY")
        if key:
            return key

        # Try key file
        key_file = _find_project_root() / "openrouter_key.txt"
        if key_file.exists():
            return key_file.read_text().strip()

        return None

    def generate(self, prompt: str, system: Optional[str] = None) -> str:
        messages = []
        if system:
            messages.append({"role": "system", "content": system})
        messages.append({"role": "user", "content": prompt})

        response = self._client.chat.completions.create(
            model=self._model_name,
            messages=messages,
        )
        return response.choices[0].message.content

    @property
    def name(self) -> str:
        return self._model_name
