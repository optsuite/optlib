import subprocess
import sys
import threading
from collections import deque
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from pathlib import Path

DEPENDCY_FILE = "Dependcy.md"
PROMPT_FILE = "PROMPT.md"
PLACEHOLDER = "__________________"
MAX_RETRIES = 3
WORKERS = 8

TAG = "\033[32m[pipeline]\033[0m"
git_lock = threading.Lock()


def read_paths(dependcy_file):
    paths = []
    seen = set()
    with open(dependcy_file, "r") as f:
        for line in f:
            line = line.strip()
            if not line or line == "---":
                continue
            if line in seen:
                continue
            paths.append(line)
            seen.add(line)
    return paths


def read_prompt(prompt_file):
    with open(prompt_file, "r") as f:
        return f.read()


def make_prompt(prompt_template, path):
    return prompt_template.replace(PLACEHOLDER, path)


def module_name_from_path(path):
    return Path(path).with_suffix("").as_posix().replace("/", ".")


def parse_imports(file_path):
    imports = []
    with open(file_path, "r", encoding="utf-8") as f:
        for line in f:
            stripped = line.lstrip()
            if not stripped.startswith("import "):
                continue
            parts = stripped.split()
            if len(parts) >= 2:
                imports.extend(parts[1:])
    return imports


def build_dependencies(paths):
    module_to_path = {module_name_from_path(path): path for path in paths}
    deps_by_path = {}
    for path in paths:
        file_path = Path(path)
        if not file_path.exists():
            raise FileNotFoundError(f"missing path from dependency list: {path}")
        deps = set()
        for dep_module in parse_imports(path):
            dep_path = module_to_path.get(dep_module)
            if dep_path and dep_path != path:
                deps.add(dep_path)
        deps_by_path[path] = deps
    return deps_by_path


def enqueue_ready_paths(remaining, deps_by_path, resolved, queued, ready_queue):
    newly_added = []
    for path in sorted(remaining):
        if path in queued:
            continue
        if deps_by_path[path].issubset(resolved):
            ready_queue.append(path)
            queued.add(path)
            newly_added.append(path)
    return newly_added


def run_codex(prompt):
    result = subprocess.run(
        ["codex", "--search", "exec", "-", "--color", "never"],
        input=prompt,
        text=True,
        stdout=sys.stdout,
        stderr=sys.stderr,
    )
    if result.returncode != 0:
        print(f"{TAG} codex failed with code {result.returncode}", file=sys.stderr)
    return result.returncode == 0


def run_lean(path):
    result = subprocess.run(
        ["lake", "env", "lean", path],
        capture_output=True,
        text=True,
    )
    print(result.stdout)
    if result.stderr:
        print(result.stderr, file=sys.stderr)
    return result.returncode == 0


def git_commit(path):
    with git_lock:
        result = subprocess.run(
            ["git", "add", path],
            capture_output=True,
            text=True,
        )
        if result.returncode != 0:
            print(result.stderr, file=sys.stderr)
            return False
        staged_check = subprocess.run(
            ["git", "diff", "--cached", "--quiet", "--", path],
            capture_output=True,
            text=True,
        )
        if staged_check.returncode == 0:
            print(f"{TAG} {path} has no staged changes, skipping commit.")
            return True
        if staged_check.returncode != 1:
            if staged_check.stderr:
                print(staged_check.stderr, file=sys.stderr)
            return False
        result = subprocess.run(
            ["git", "commit", "-m", f"fix: {path}"],
            capture_output=True,
            text=True,
        )
        print(result.stdout)
        if result.stderr:
            print(result.stderr, file=sys.stderr)
        return result.returncode == 0


def git_push():
    with git_lock:
        result = subprocess.run(
            ["git", "push"],
            capture_output=True,
            text=True,
        )
        print(result.stdout)
        if result.stderr:
            print(result.stderr, file=sys.stderr)
        if result.returncode != 0:
            print(f"{TAG} git push failed with code {result.returncode}", file=sys.stderr)
        return result.returncode == 0


def commit_and_push(path):
    if not git_commit(path):
        print(f"{TAG} {path} git commit step failed.", file=sys.stderr)
        return False
    if not git_push():
        print(f"{TAG} {path} git push step failed.", file=sys.stderr)
        return False
    return True


def process_path(path, prompt_template):
    print(f"\n{TAG} {path} — pre-check compilation")
    if run_lean(path):
        print(f"{TAG} {path} already compiles, committing and pushing...")
        return commit_and_push(path)

    for attempt in range(1, MAX_RETRIES + 1):
        print(f"\n{TAG} {path} — attempt {attempt}/{MAX_RETRIES}")

        prompt = make_prompt(prompt_template, path)
        if not run_codex(prompt):
            print(f"{TAG} {path} codex step failed.")
            continue

        if run_lean(path):
            print(f"{TAG} {path} compiled successfully, committing and pushing...")
            return commit_and_push(path)
        else:
            print(f"{TAG} {path} failed to compile.")

    print(f"{TAG} {path} exceeded {MAX_RETRIES} retries — aborting.", file=sys.stderr)
    return False


def main():
    paths = read_paths(DEPENDCY_FILE)
    prompt_template = read_prompt(PROMPT_FILE)

    deps_by_path = build_dependencies(paths)
    remaining = set(paths)
    resolved = set()
    queued = set()
    ready_queue = deque()
    total = len(paths)

    enqueue_ready_paths(remaining, deps_by_path, resolved, queued, ready_queue)
    print(f"\n{TAG} initial ready queue ({len(ready_queue)}): {list(ready_queue)}")

    failed = []
    with ThreadPoolExecutor(max_workers=WORKERS) as executor:
        running = {}
        while remaining or running:
            while ready_queue and len(running) < WORKERS:
                path = ready_queue.popleft()
                future = executor.submit(process_path, path, prompt_template)
                running[future] = path
                print(
                    f"{TAG} scheduled {path}; running={len(running)}/{WORKERS}, "
                    f"queued={len(ready_queue)}"
                )

            if not running:
                unresolved = sorted(remaining)
                print(
                    f"\n{TAG} dependency deadlock, unresolved paths: {unresolved}",
                    file=sys.stderr,
                )
                sys.exit(1)

            completed_futures, _ = wait(running, return_when=FIRST_COMPLETED)
            for future in completed_futures:
                path = running.pop(future)
                queued.discard(path)

                try:
                    ok = future.result()
                except Exception as exc:
                    print(f"{TAG} {path} raised exception: {exc}", file=sys.stderr)
                    ok = False

                if not ok:
                    failed.append(path)
                    continue

                resolved.add(path)
                remaining.remove(path)
                print(f"{TAG} resolved {path} ({len(resolved)}/{total})")
                unlocked = enqueue_ready_paths(
                    remaining, deps_by_path, resolved, queued, ready_queue
                )
                if unlocked:
                    print(
                        f"{TAG} unlocked {len(unlocked)} path(s), "
                        f"ready queue now {len(ready_queue)}"
                    )

            if failed:
                for pending in running:
                    pending.cancel()
                break

    if failed:
        print(f"\n{TAG} Failed paths: {failed}", file=sys.stderr)
        sys.exit(1)

    print(f"\n{TAG} All paths processed successfully.")


if __name__ == "__main__":
    main()
