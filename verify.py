#!/usr/bin/env python3
"""Standalone verification script for Putnam 2025 problems.

Calls rocq_verify with a pet context so Phase 2 (shared-defs) works
for problems with Inductive/Record/Definition types.
"""

import argparse
import asyncio
import sys
from pathlib import Path

from tqdm import tqdm

from rocq_mcp.server import rocq_verify, _invalidate_pet


class _Ctx:
    """Minimal stand-in for FastMCP Context to inject pet lifespan state."""

    def __init__(self, state):
        self.lifespan_context = state


async def verify(problem, workspace, ctx):
    problem_file = workspace / f"problems/putnam_2025_{problem}.v"
    solution_file = workspace / f"solutions/proof_{problem}.v"
    theorem_name = f"putnam_2025_{problem}"

    problem_text = problem_file.read_text()
    solution_text = solution_file.read_text()

    return await rocq_verify(
        proof=solution_text,
        problem_name=theorem_name,
        problem_statement=problem_text,
        workspace=str(workspace),
        ctx=ctx,
    )


def print_summary(results):
    """Print a markdown summary table with checkboxes."""
    verified = sum(1 for r in results if r["verified"])
    total = len(results)

    print("\n| Problem | Status | Axioms      |")
    print("|---------|--------|-------------|")

    for r in results:
        icon = "\u2705" if r["verified"] else "\u274c"
        assumptions = r.get("assumptions", "")
        print(f"| {r['problem']} | {icon} | {assumptions} |")

    print(f"\n**{verified}/{total} verified**")

    # Show errors for failed problems
    failed = [r for r in results if not r["verified"]]
    if failed:
        print("\n<details><summary>Errors</summary>\n")
        for r in failed:
            print(f"**{r['problem']}**\n")
            error = r.get("error", "")
            if error:
                print("```")
                for line in error.splitlines()[:5]:
                    print(line)
                print("```")
            hint = r.get("hint", "")
            if hint:
                print(f"> Hint: {hint}\n")
        print("</details>")


async def main():
    parser = argparse.ArgumentParser(description="Verify Putnam 2025 Rocq proofs")
    parser.add_argument(
        "problems",
        nargs="*",
        help="Problem IDs to verify (e.g. a1 b3). Default: all 12 problems.",
    )
    args = parser.parse_args()

    workspace = Path(__file__).parent

    if args.problems:
        problems = args.problems
    else:
        problems = [f"a{i}" for i in range(1, 7)] + [f"b{i}" for i in range(1, 7)]

    # Set up pet context (lazy init — pet spawned only if Phase 2 needed)
    state = {"pet_client": None, "pet_timeout": 30.0}
    ctx = _Ctx(state)

    results = []
    try:
        for problem in tqdm(problems, desc="Verifying", unit="problem"):
            result = await verify(problem, workspace, ctx)

            verified = result.get("verified", False)
            assumptions = result.get("assumptions", "")

            # Extract axiom names only (drop ": type" suffix)
            if isinstance(assumptions, list):
                axiom_names = [a.split(" :")[0] for a in assumptions]
                assumptions_str = ", ".join(axiom_names)
            elif assumptions == "Closed under the global context":
                assumptions_str = ""
            else:
                assumptions_str = str(assumptions)

            entry = {
                "problem": f"putnam_2025_{problem}",
                "verified": verified,
                "assumptions": assumptions_str,
            }
            if not verified:
                entry["error"] = result.get("error", "")
                entry["hint"] = result.get("hint", "")

            results.append(entry)
    finally:
        _invalidate_pet(state)

    print_summary(results)
    if any(not r["verified"] for r in results):
        sys.exit(1)


if __name__ == "__main__":
    asyncio.run(main())
