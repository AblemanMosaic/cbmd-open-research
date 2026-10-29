"""Verify the declared Lean source envelope; this command does not compile Lean."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import sys


ROOT = Path(__file__).resolve().parent.parent
MANIFEST = "proofs/native/SOURCE_MANIFEST.json"
TOOLCHAIN = "leanprover/lean4:v4.34.1"
MATHLIB_REVISION = "d13f23b723b8a846827a245b89c10fc7d3f11612"
HEX64 = re.compile(r"[0-9a-f]{64}\Z")
HEX40 = re.compile(r"[0-9a-f]{40}\Z")
MODULE = re.compile(r"[A-Z][A-Za-z0-9_']*(?:\.[A-Za-z0-9_']+)*\Z")
BASE_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
ESCAPES = {"sorry", "admit", "axiom", "sorryAx", "unsafe", "native_decide"}
TOKENS = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z0-9_']+)*|[^\s]")


def require(condition: bool, diagnostic: str) -> None:
    if not condition:
        raise ValueError(diagnostic)


def relative_path(value: object) -> str:
    require(isinstance(value, str) and bool(value), "unsafe repository path")
    require(not any(char in value for char in "\\:*?\x00"), "unsafe repository path")
    pure = PurePosixPath(value)
    require(bool(pure.parts) and not pure.is_absolute() and str(pure) == value
            and ".." not in pure.parts and "." not in pure.parts,
            "unsafe repository path")
    return value


def repository_file(relative: str) -> Path:
    relative_path(relative)
    root = ROOT.resolve()
    result = root.joinpath(*PurePosixPath(relative).parts).resolve()
    require(root in result.parents, "path escapes repository: " + relative)
    require(result.is_file(), "required proof input absent: " + relative)
    return result


def lean_code(text: str) -> str:
    """Erase nested comments and strings, preserving positions and line numbers."""
    output = list(text)
    position = 0
    depth = 0
    in_string = False
    while position < len(text):
        pair = text[position:position + 2]
        character = text[position]
        if depth:
            if pair == "/-":
                depth += 1
            elif pair == "-/":
                depth -= 1
            else:
                output[position] = "\n" if character == "\n" else " "
                position += 1
                continue
            output[position:position + 2] = [" ", " "]
            position += 2
        elif in_string:
            output[position] = "\n" if character == "\n" else " "
            if character == "\\" and position + 1 < len(text):
                output[position + 1] = "\n" if text[position + 1] == "\n" else " "
                position += 2
                continue
            if character == '"':
                in_string = False
            position += 1
        elif pair == "/-":
            depth = 1
            output[position:position + 2] = [" ", " "]
            position += 2
        elif pair == "--":
            ending = text.find("\n", position)
            if ending == -1:
                ending = len(text)
            output[position:ending] = [" "] * (ending - position)
            position = ending
        elif character == '"':
            in_string = True
            output[position] = " "
            position += 1
        else:
            position += 1
    require(depth == 0 and not in_string, "unterminated Lean comment or string")
    return "".join(output)


def lean_imports(code: str) -> list[str]:
    """Read the module header, including multiline and multiple-module imports."""
    tokens = TOKENS.findall(code)
    index = int(bool(tokens) and tokens[0] == "prelude")
    imports: list[str] = []
    while index < len(tokens) and tokens[index] == "import":
        index += 1
        beginning = index
        while index < len(tokens) and MODULE.fullmatch(tokens[index]):
            imports.append(tokens[index])
            index += 1
        require(index != beginning, "unrecognized or empty Lean import")
    require("import" not in tokens[index:], "Lean import outside module header")
    return imports


def verify(manifest_path: Path | None = None) -> dict[str, object]:
    root = ROOT.resolve()
    manifest_file = Path(manifest_path) if manifest_path is not None else root / MANIFEST
    if not manifest_file.is_absolute():
        manifest_file = root / manifest_file
    manifest_file = manifest_file.resolve()
    require(root in manifest_file.parents, "manifest escapes repository")
    manifest = json.loads(manifest_file.read_text(encoding="utf-8-sig"))
    require(manifest["schema"] == "cbmd.proof-source-manifest.v1", "proof manifest schema mismatch")
    require(manifest["toolchain"] == TOOLCHAIN, "unexpected proof toolchain")
    require(manifest["mathlib_revision"] == MATHLIB_REVISION, "unexpected mathlib revision")
    project = relative_path(manifest["project_path"])
    library = relative_path(manifest["source_library_root"])
    require(library == project + "/lean", "unexpected Lean source library layout")
    allowed_axioms = manifest["allowed_axioms"]
    require(isinstance(allowed_axioms, list) and len(allowed_axioms) == len(set(allowed_axioms))
            and set(allowed_axioms) <= BASE_AXIOMS, "unapproved axiom allowlist")

    files = manifest["files"]
    require(isinstance(files, list) and bool(files), "empty proof source envelope")
    declared: dict[str, dict[str, object]] = {}
    modules: dict[str, list[str]] = {}
    for row in files:
        relative = relative_path(row["path"])
        require(relative not in declared, "duplicate proof input: " + relative)
        require(isinstance(row["origin"], str) and bool(row["origin"]), "missing input origin")
        require(isinstance(row["sha256"], str) and bool(HEX64.fullmatch(row["sha256"])),
                "invalid proof input digest")
        require(type(row["bytes"]) is int and row["bytes"] >= 0, "invalid proof input size")
        source = repository_file(relative)
        content = source.read_bytes()
        require(len(content) == row["bytes"], "proof input size mismatch: " + relative)
        require(hashlib.sha256(content).hexdigest() == row["sha256"],
                "proof input digest mismatch: " + relative)
        declared[relative] = row
        if relative.startswith(library + "/") and relative.endswith(".lean"):
            module = relative[len(library) + 1:-5].replace("/", ".")
            require(bool(MODULE.fullmatch(module)), "invalid local Lean module: " + relative)
            code = lean_code(content.decode("utf-8-sig"))
            tokens = set(TOKENS.findall(code))
            require(not any(part in ESCAPES for token in tokens for part in token.split(".")),
                    "Lean proof escape in " + relative)
            require(not re.search(r"\bset_option\s+debug\.skipKernelTC\s+true\b", code),
                    "Lean kernel check disabled in " + relative)
            modules[module] = lean_imports(code)

    required = {
        project + "/lean-toolchain", project + "/lakefile.lean", project + "/lake-manifest.json",
        "tools/replay_lean.py", "tools/verify_proof_sources.py",
    }
    require(required <= declared.keys(), "runner or pinned project input absent from manifest")
    require(any(any(part.upper().startswith("LICENSE") for part in PurePosixPath(path).parts)
                for path in declared),
            "retained license absent from manifest")
    observed = {
        source.relative_to(root).as_posix()
        for source in (root / library).rglob("*.lean") if source.is_file()
    }
    require(observed <= declared.keys(), "unbound Lean source in proof library")

    toolchain = repository_file(project + "/lean-toolchain").read_text(encoding="utf-8-sig").strip()
    require(toolchain == TOOLCHAIN, "toolchain file differs from manifest")
    lakefile = repository_file(project + "/lakefile.lean").read_text(encoding="utf-8-sig")
    require(MATHLIB_REVISION in lakefile and "fixedToolchain := true" in lakefile,
            "Lake configuration does not retain pinned dependency and toolchain")
    dependencies = json.loads(repository_file(project + "/lake-manifest.json")
                              .read_text(encoding="utf-8-sig"))
    require(dependencies.get("fixedToolchain") is True, "Lake manifest toolchain is not fixed")
    packages = dependencies["packages"]
    require(isinstance(packages, list) and bool(packages), "empty pinned dependency set")
    package_names: set[str] = set()
    mathlib = None
    for package in packages:
        require(package["name"] not in package_names, "duplicate Lake dependency")
        package_names.add(package["name"])
        require(package["type"] == "git" and bool(HEX40.fullmatch(package["rev"])),
                "unpinned Lake dependency")
        if package["name"] == "mathlib":
            mathlib = package
    require(mathlib is not None and mathlib["rev"] == MATHLIB_REVISION
            and mathlib["url"] == "https://github.com/leanprover-community/mathlib4.git",
            "Lake mathlib binding mismatch")

    targets = manifest["targets"]
    require(isinstance(targets, list) and bool(targets) and len(targets) == len(set(targets)),
            "invalid proof target set")
    closure: set[str] = set()
    visiting: set[str] = set()

    def visit(module: str) -> None:
        require(isinstance(module, str) and bool(MODULE.fullmatch(module)), "invalid module name")
        require(module in modules, "missing local import: " + module)
        require(module not in visiting, "cyclic local imports: " + module)
        if module in closure:
            return
        visiting.add(module)
        for dependency in modules[module]:
            if dependency == "OAI" or dependency.startswith("OAI."):
                visit(dependency)
        visiting.remove(module)
        closure.add(module)

    for target in targets:
        visit(target)
    if "source_imports" in manifest:
        require(manifest["source_imports"] == modules, "declared source imports differ from sources")

    return {
        "schema": "cbmd.proof-source-custody-check.v1", "status": "PASS",
        "scope": "SOURCE_CUSTODY_AND_NO_ESCAPE_ONLY", "files_checked": len(declared),
        "lean_modules_checked": len(modules), "target_modules_checked": len(targets),
        "target_import_closure_modules": len(closure), "toolchain": TOOLCHAIN,
        "mathlib_revision": MATHLIB_REVISION,
        "manifest_sha256": hashlib.sha256(manifest_file.read_bytes()).hexdigest(),
        "lean_recompiled": False, "actual_axiom_dependencies_checked": False,
        "allowed_axioms": allowed_axioms, "independent_verification": False,
        "authority_effect": "NONE",
    }


if __name__ == "__main__":
    try:
        requested = Path(sys.argv[1]) if len(sys.argv) == 2 else None
        require(len(sys.argv) <= 2, "usage: verify_proof_sources.py [manifest_path]")
        print(json.dumps(verify(requested), sort_keys=True))
    except (KeyError, OSError, TypeError, UnicodeError, ValueError) as exc:
        print(json.dumps({"status": "FAIL", "error": str(exc), "authority_effect": "NONE"},
                         sort_keys=True), file=sys.stderr)
        sys.exit(1)
