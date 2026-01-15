"""OpenAI model implementation."""

import os
from typing import Optional

from openai import OpenAI

from .base import LLMModel


class OpenAIModel(LLMModel):
    """OpenAI API implementation."""

    def __init__(
        self,
        model_name: str = "gpt-4o",
        api_key: Optional[str] = None,
    ):
        self._model_name = model_name
        self._api_key = api_key or os.environ.get("OPENAI_API_KEY")
        if not self._api_key:
            raise ValueError("OpenAI API key not found. Set OPENAI_API_KEY environment variable.")
        self._client = OpenAI(api_key=self._api_key)

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
