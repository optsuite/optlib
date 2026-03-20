#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path

__all__ = ["load_dependency_graph"]


def _parse_imports(file_path: Path) -> list[str]:
    imports: list[str] = []
    for line in file_path.read_text(encoding="utf-8").splitlines():
        stripped = line.lstrip()
        if not stripped.startswith("import "):
            continue
        parts = stripped.split()
        if len(parts) >= 2:
            imports.extend(parts[1:])
    return imports


def _module_name_from_path(path: str) -> str:
    return Path(path).with_suffix("").as_posix().replace("/", ".")


def _discover_lean_paths(root: Path) -> list[str]:
    optlib_dir = root / "Optlib"
    if not optlib_dir.exists():
        raise FileNotFoundError(f"Optlib directory not found: {optlib_dir}")
    return [file_path.relative_to(root).as_posix() for file_path in sorted(optlib_dir.rglob("*.lean"))]


def load_dependency_graph(root: Path | None = None) -> tuple[list[str], dict[str, set[str]]]:
    if root is None:
        root = Path.cwd()
    root = root.resolve()
    paths = _discover_lean_paths(root)
    module_to_path = {_module_name_from_path(path): path for path in paths}

    deps_by_path: dict[str, set[str]] = {}
    for path in paths:
        file_path = root / path
        deps = set()
        for dep_module in _parse_imports(file_path):
            dep_path = module_to_path.get(dep_module)
            if dep_path and dep_path != path:
                deps.add(dep_path)
        deps_by_path[path] = deps

    return paths, deps_by_path
