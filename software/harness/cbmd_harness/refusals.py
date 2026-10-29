from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class Refusal(Exception):
    code: str
    detail: str
    authority_effect: str = "NONE"

    def as_dict(self) -> dict[str, str]:
        return {
            "status": "REFUSED",
            "refusal_code": self.code,
            "detail": self.detail,
            "authority_effect": self.authority_effect,
        }
