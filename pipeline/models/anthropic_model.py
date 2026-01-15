"""Anthropic model implementation."""

import os
from typing import Optional

import anthropic

from .base import LLMModel


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
        self._api_key = api_key or os.environ.get("ANTHROPIC_API_KEY")
        if not self._api_key:
            raise ValueError("Anthropic API key not found. Set ANTHROPIC_API_KEY environment variable.")
        self._client = anthropic.Anthropic(api_key=self._api_key)

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
