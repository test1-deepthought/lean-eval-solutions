#!/usr/bin/env python3
"""Print a compact Lean-Eval preflight summary for GitHub Actions logs."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


def classify_failure(problem: dict) -> str:
    text = json.dumps(problem, sort_keys=True).lower()
    if "landrun" in text or "sandbox" in text:
        return "environment/sandbox"
    if "lean4export" in text or "comparator" in text:
        return "comparator"
    if "lake update" in text or "cache get" in text or "toolchain" in text:
        return "environment/dependency"
    if "timeout" in text:
        return "environment/timeout"
    if "unsolved goals" in text or "proof contains" in text or "submission" in text:
        return "proof"
    return "proof-or-comparator"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args()

    summary_path = args.output_dir / "summary.json"
    results_path = args.output_dir / "results.json"

    if not summary_path.exists():
        print("Lean-Eval preflight summary")
        print("=" * 60)
        print(f"summary.json not found at {summary_path}")
        return 1

    summary = json.loads(summary_path.read_text(encoding="utf-8"))
    results = {}
    if results_path.exists():
        results = json.loads(results_path.read_text(encoding="utf-8"))

    passed = set(results.get("passed") or [])
    overlay_records = summary.get("overlay_records") or []
    run_eval = summary.get("run_eval") or {}
    problems = run_eval.get("problems") or []
    by_id = {
        item.get("id"): item
        for item in problems
        if isinstance(item, dict) and isinstance(item.get("id"), str)
    }

    print("Lean-Eval preflight summary")
    print("=" * 60)
    print(f"Passed problems: {len(passed)}")
    print(f"Candidate records: {len(overlay_records)}")
    print("Command: lake exe lean-eval run-eval --json --workspaces-root <clean-workspaces>")
    print("")

    failed = 0
    skipped = 0
    for record in overlay_records:
        problem_id = record.get("problem_id", "(unknown)")
        if record.get("skip_reason"):
            skipped += 1
            print(f"- {problem_id}: SKIP")
            print(f"  reason: {record.get('skip_reason')}")
            continue
        problem_result = by_id.get(problem_id, {})
        status = "PASS" if problem_id in passed else "FAIL"
        if status == "FAIL":
            failed += 1
        print(f"- {problem_id}: {status}")
        print(f"  copied: {', '.join(record.get('overlaid_files') or [])}")
        print(f"  shared_packages: {record.get('shared_packages')}")
        if status == "FAIL":
            print(f"  category: {classify_failure(problem_result)}")
            rendered = json.dumps(problem_result, indent=2, sort_keys=True)
            lines = rendered.splitlines()
            print("  relevant log:")
            for line in lines[:80]:
                print(f"    {line}")
            if len(lines) > 80:
                print(f"    ... {len(lines) - 80} more lines omitted")
        print("")

    print(f"Overall: {'FAIL' if failed else 'PASS'}")
    print(f"Failed: {failed}")
    print(f"Skipped: {skipped}")
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
