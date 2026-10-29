from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any


class CanonicalError(ValueError):
    pass


def _check(value: Any, path: str = "$") -> None:
    if value is None or isinstance(value, (str, bool, int)):
        return
    if isinstance(value, float):
        raise CanonicalError(f"NON_CANONICAL_NUMBER:{path}")
    if isinstance(value, list):
        for index, item in enumerate(value):
            _check(item, f"{path}[{index}]")
        return
    if isinstance(value, dict):
        for key, item in value.items():
            if not isinstance(key, str):
                raise CanonicalError(f"NON_STRING_KEY:{path}")
            _check(item, f"{path}.{key}")
        return
    raise CanonicalError(f"UNSUPPORTED_CANONICAL_TYPE:{path}:{type(value).__name__}")


def canonical_bytes(value: Any) -> bytes:
    _check(value)
    return json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    ).encode("utf-8")


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def root(value: Any) -> str:
    return sha256_bytes(canonical_bytes(value))


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load_json(path: Path) -> Any:
    def reject_constant(value: str) -> None:
        raise CanonicalError(f"NON_FINITE_JSON:{value}")

    def reject_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in pairs:
            if key in result:
                raise CanonicalError(f"DUPLICATE_JSON_KEY:{key}")
            result[key] = value
        return result

    with path.open("r", encoding="utf-8-sig") as handle:
        value = json.load(handle, parse_constant=reject_constant, object_pairs_hook=reject_pairs)
    _check(value)
    return value


def write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    data = canonical_bytes(value) + b"\n"
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_bytes(data)
    temporary.replace(path)
