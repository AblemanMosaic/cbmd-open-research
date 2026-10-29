"""Build a deterministic ZIP and detached receipt from the clean Git index."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import subprocess
import sys
import zipfile


ROOT = Path(__file__).resolve().parent.parent


def git(*arguments: str) -> bytes:
    completed = subprocess.run(
        ["git", "-C", str(ROOT), *arguments],
        capture_output=True,
        check=False,
        shell=False,
    )
    if completed.returncode:
        raise ValueError(completed.stderr.decode("utf-8", errors="replace").strip())
    return completed.stdout


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def tracked_files() -> list[tuple[str, str]]:
    rows: list[tuple[str, str]] = []
    for record in git("ls-files", "--stage", "-z").split(b"\0"):
        if not record:
            continue
        metadata, encoded_path = record.split(b"\t", 1)
        mode, _object_id, stage = metadata.decode("ascii").split()
        if stage != "0":
            raise ValueError("unmerged Git index entry")
        path = encoded_path.decode("utf-8")
        pure = PurePosixPath(path)
        if pure.is_absolute() or ".." in pure.parts:
            raise ValueError("unsafe tracked path: " + path)
        rows.append((mode, path))
    return sorted(rows, key=lambda row: row[1])


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", default="dist")
    args = parser.parse_args()
    try:
        if git("status", "--porcelain"):
            raise ValueError("release packaging requires a clean checkout")
        version = (ROOT / "VERSION").read_text(encoding="utf-8").strip()
        if version != "0.1.0":
            raise ValueError("unexpected release version")
        commit = git("rev-parse", "HEAD").decode("ascii").strip()
        entries = tracked_files()
        file_rows: list[dict[str, object]] = []
        payloads: list[tuple[str, str, bytes]] = []
        for mode, path in entries:
            content = (ROOT / Path(*PurePosixPath(path).parts)).read_bytes()
            file_rows.append({"path": path, "bytes": len(content), "sha256": sha256(content), "mode": mode})
            payloads.append((mode, path, content))

        prefix = f"cbmd-open-research-{version}"
        manifest = {
            "schema": "cbmd.release-content-manifest.v1",
            "version": version,
            "git_commit": commit,
            "files": file_rows,
        }
        manifest_bytes = (json.dumps(manifest, indent=2, sort_keys=True) + "\n").encode("utf-8")
        output_dir = (ROOT / args.output_dir).resolve()
        output_dir.mkdir(parents=True, exist_ok=True)
        archive = output_dir / f"CBMD-Research-Toolkit-v{version}.zip"
        with zipfile.ZipFile(archive, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as bundle:
            for mode, path, content in payloads:
                info = zipfile.ZipInfo(f"{prefix}/{path}", date_time=(1980, 1, 1, 0, 0, 0))
                info.create_system = 3
                permissions = 0o755 if mode == "100755" else 0o644
                info.external_attr = (0o100000 | permissions) << 16
                info.compress_type = zipfile.ZIP_DEFLATED
                bundle.writestr(info, content, compress_type=zipfile.ZIP_DEFLATED, compresslevel=9)
            info = zipfile.ZipInfo(f"{prefix}/RELEASE_MANIFEST.json", date_time=(1980, 1, 1, 0, 0, 0))
            info.create_system = 3
            info.external_attr = (0o100000 | 0o644) << 16
            info.compress_type = zipfile.ZIP_DEFLATED
            bundle.writestr(info, manifest_bytes, compress_type=zipfile.ZIP_DEFLATED, compresslevel=9)

        archive_bytes = archive.read_bytes()
        receipt = {
            "schema": "cbmd.release-receipt.v1",
            "version": version,
            "git_commit": commit,
            "archive": archive.name,
            "archive_bytes": len(archive_bytes),
            "archive_sha256": sha256(archive_bytes),
            "tracked_files": len(file_rows),
            "embedded_manifest_sha256": sha256(manifest_bytes),
            "authority_effect": "NONE",
            "claim_boundary": "Exact release custody; not mathematical review or novelty.",
        }
        receipt_path = output_dir / f"CBMD-Research-Toolkit-v{version}.receipt.json"
        receipt_path.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8", newline="\n")
        print(json.dumps(receipt, indent=2, sort_keys=True))
        return 0
    except (OSError, TypeError, UnicodeError, ValueError, zipfile.BadZipFile) as exc:
        print(json.dumps({"status": "FAIL", "error": str(exc)}), file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
