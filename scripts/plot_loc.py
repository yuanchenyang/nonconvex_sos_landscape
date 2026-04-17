#!/usr/bin/env python3
"""Plot lines of code over time, colored by dominant file type per commit.

Usage:
    python scripts/plot_loc.py <branch> <start_commit> <end_commit> [-o OUTPUT]

Counts lines in .lean, .jl, and .tex files. The baseline is measured at
<start_commit>, then each commit in (start_commit, end_commit] on <branch>
is applied incrementally. The filled area under the curve is colored by the
dominant file type changed in each commit.

Example:
    python scripts/plot_loc.py main 2c3fa6a HEAD -o /tmp/commits_loc.png
"""

import argparse
import subprocess
import sys
from datetime import datetime, timezone

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Patch

TRACKED_EXTS = {"lean", "jl", "tex"}
EXT_COLOR = {"lean": "steelblue", "jl": "crimson", "tex": "#FFD700", "mixed": "#888"}


def get_numstat(branch, start, end):
    """Return list of (datetime_utc, {ext: net_delta}) in chronological order."""
    result = subprocess.run(
        ["git", "log", "--reverse", "--format=COMMIT %H %aI", "--numstat",
         f"{start}..{end}"],
        capture_output=True, text=True, check=True,
    )
    commits = []
    pending = {}
    current_ts = None
    for line in result.stdout.splitlines():
        line = line.rstrip()
        if line.startswith("COMMIT "):
            # Flush previous commit
            if current_ts is not None:
                commits.append((current_ts, pending))
                pending = {}
            parts = line.split(" ", 2)
            current_ts = datetime.fromisoformat(parts[2].strip()).astimezone(timezone.utc)
        elif line.strip() == "":
            continue
        else:
            cols = line.split("\t")
            if len(cols) < 3:
                continue
            added_s, deleted_s, fname = cols[0], cols[1], cols[2]
            if added_s == "-" or deleted_s == "-":
                continue  # binary
            added, deleted = int(added_s), int(deleted_s)
            ext = fname.rsplit(".", 1)[-1] if "." in fname else ""
            if ext in TRACKED_EXTS:
                pending[ext] = pending.get(ext, 0) + added - deleted
    # Flush last commit
    if current_ts is not None:
        commits.append((current_ts, pending))
    return commits


def main():
    parser = argparse.ArgumentParser(description="Plot lines of code over time, colored by dominant file type.")
    parser.add_argument("branch", help="Git branch name")
    parser.add_argument("start_commit", help="Start commit (baseline)")
    parser.add_argument("end_commit", help="End commit (inclusive)")
    parser.add_argument("-o", "--output", default="commits_loc.png",
                        help="Output image path (default: commits_loc.png)")
    args = parser.parse_args()

    print("Collecting numstat...", file=sys.stderr)
    commits = get_numstat(args.branch, args.start_commit, args.end_commit)
    if not commits:
        print("No commits found in range.", file=sys.stderr)
        sys.exit(1)
    print(f"  {len(commits)} commits", file=sys.stderr)

    # Build per-commit added lines by extension (only positive net additions)
    commit_adds = []  # list of {ext: added_lines} per commit
    for ts, delta in commits:
        adds = {}
        for ext in TRACKED_EXTS:
            net = delta.get(ext, 0)
            if net > 0:
                adds[ext] = net
        commit_adds.append(adds)

    n = len(commits)
    xs = list(range(1, n + 1))

    # Stacked vertical bars: jl at bottom, then lean, then tex
    ext_order = ["jl", "lean", "tex"]
    fig, ax = plt.subplots(figsize=(max(8, n * 0.06), 6))

    bottoms = [0] * n
    for ext in ext_order:
        heights = [commit_adds[i].get(ext, 0) for i in range(n)]
        ax.bar(xs, heights, bottom=bottoms, width=0.8,
               color=EXT_COLOR[ext], edgecolor="none", label=ext)
        bottoms = [b + h for b, h in zip(bottoms, heights)]

    ax.set_xlabel("Commit number")
    ax.set_ylabel("Lines added")
    short_start = args.start_commit[:7] if len(args.start_commit) > 7 else args.start_commit
    short_end = args.end_commit[:7] if len(args.end_commit) > 7 else args.end_commit
    ax.set_title(f"LOC added per commit ({short_start} → {short_end})")

    legend_handles = [
        Patch(color="crimson", label="Julia (.jl)"),
        Patch(color="steelblue", label="Lean (.lean)"),
        Patch(color="#FFD700", label="LaTeX (.tex)"),
    ]
    ax.legend(handles=legend_handles, loc="upper right")
    ax.grid(axis="y", linestyle="--", alpha=0.4)

    plt.tight_layout()
    plt.savefig(args.output, dpi=150)
    total_added = {ext: sum(commit_adds[i].get(ext, 0) for i in range(n)) for ext in ext_order}
    print(f"Saved to {args.output}  (total added: {total_added})")


if __name__ == "__main__":
    main()
