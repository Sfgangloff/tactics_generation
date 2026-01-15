"""Abstract base class for LLM models."""

from abc import ABC, abstractmethod
from typing import Optional


class LLMModel(ABC):
    """Abstract interface for LLM providers."""

    @abstractmethod
    def generate(self, prompt: str, system: Optional[str] = None) -> str:
        """Generate a response from the model.

        Args:
            prompt: The user prompt/message.
            system: Optional system prompt.

        Returns:
            The model's response text.
        """
        pass

    @property
    @abstractmethod
    def name(self) -> str:
        """Return the model name."""
        pass
