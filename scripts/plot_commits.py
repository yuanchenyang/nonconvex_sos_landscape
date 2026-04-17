#!/usr/bin/env python3
"""Plot cumulative commits over time, colored by file-type category.

Usage:
    python scripts/plot_commits.py <branch> <start_commit> <end_commit> [-o OUTPUT]

Commits in the range (start_commit, end_commit] on <branch> are plotted.
Each commit is classified as lean_only, julia_only, both, or neither based
on the file extensions it touches.

Example:
    python scripts/plot_commits.py main 2c3fa6a HEAD -o /tmp/commits_line.png
"""

import argparse
import subprocess
import sys
from datetime import datetime, timezone, timedelta, date

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import matplotlib.dates as mdates
from matplotlib.lines import Line2D


COLORS = {
    "lean_only": "steelblue",
    "julia_only": "crimson",
    "both": "purple",
    "neither": "gray",
}
ALPHA_FILL = 0.18


def classify_commit(sha):
    """Return 'lean_only', 'julia_only', 'both', or 'neither'."""
    result = subprocess.run(
        ["git", "diff-tree", "--no-commit-id", "--numstat", "-r", sha],
        capture_output=True, text=True, check=True,
    )
    has_lean = False
    has_julia = False
    for line in result.stdout.strip().splitlines():
        cols = line.split("\t")
        if len(cols) < 3:
            continue
        fname = cols[2]
        if fname.endswith(".lean"):
            has_lean = True
        elif fname.endswith(".jl"):
            has_julia = True
    if has_lean and has_julia:
        return "both"
    if has_lean:
        return "lean_only"
    if has_julia:
        return "julia_only"
    return "neither"


def get_commits(branch, start, end):
    """Return list of (datetime_utc, sha) in chronological order."""
    result = subprocess.run(
        ["git", "log", "--reverse", "--format=%H %aI", f"{start}..{end}"],
        capture_output=True, text=True, check=True,
    )
    commits = []
    for line in result.stdout.strip().splitlines():
        if not line.strip():
            continue
        sha, ts_str = line.split(" ", 1)
        ts = datetime.fromisoformat(ts_str.strip()).astimezone(timezone.utc)
        commits.append((ts, sha))
    return commits


def main():
    parser = argparse.ArgumentParser(description="Plot cumulative commits over time, colored by file type.")
    parser.add_argument("branch", help="Git branch name")
    parser.add_argument("start_commit", help="Start commit (exclusive)")
    parser.add_argument("end_commit", help="End commit (inclusive)")
    parser.add_argument("-o", "--output", default="commits_line.png",
                        help="Output image path (default: commits_line.png)")
    args = parser.parse_args()

    raw_commits = get_commits(args.branch, args.start_commit, args.end_commit)
    if not raw_commits:
        print("No commits found in range.", file=sys.stderr)
        sys.exit(1)

    print(f"Found {len(raw_commits)} commits, classifying...", file=sys.stderr)
    commits = []
    for i, (ts, sha) in enumerate(raw_commits):
        cat = classify_commit(sha)
        commits.append((ts, cat))
        if (i + 1) % 50 == 0:
            print(f"  classified {i + 1}/{len(raw_commits)}", file=sys.stderr)

    timestamps = [ts for ts, _ in commits]
    categories = [cat for _, cat in commits]
    ys = list(range(1, len(commits) + 1))

    fig, ax = plt.subplots(figsize=(15, 5))

    # First commit: draw a single marker
    ax.plot([timestamps[0]], [ys[0]], "o", color=COLORS[categories[0]], markersize=4, zorder=3)

    for i in range(1, len(commits)):
        t0, t1 = timestamps[i - 1], timestamps[i]
        y0, y1 = ys[i - 1], ys[i]
        color = COLORS[categories[i]]
        ax.plot([t0, t1], [y0, y1], color=color, linewidth=1.8, solid_capstyle="round")
        ax.fill_between([t0, t1], [y0, y1], alpha=ALPHA_FILL, color=color)

    # Day boundary lines
    first_day = timestamps[0].date()
    last_day = timestamps[-1].date() + timedelta(days=1)
    d = first_day
    while d <= last_day:
        ax.axvline(datetime(d.year, d.month, d.day, tzinfo=timezone.utc),
                   color="gray", linewidth=0.5, linestyle="--", alpha=0.4)
        d += timedelta(days=1)

    ax.set_xlim(timestamps[0], timestamps[-1])
    ax.xaxis.set_major_locator(mdates.HourLocator(byhour=range(0, 24, 4)))
    ax.xaxis.set_major_formatter(mdates.DateFormatter("%b %d\n%H:%M"))
    ax.xaxis.set_minor_locator(mdates.HourLocator(interval=1))
    fig.autofmt_xdate(rotation=45, ha="right")
    ax.grid(axis="y", linestyle="--", alpha=0.4)
    ax.set_ylim(0, len(commits) + 5)
    ax.set_xlabel("Time (UTC)")
    ax.set_ylabel("Cumulative commits")
    short_start = args.start_commit[:7] if len(args.start_commit) > 7 else args.start_commit
    short_end = args.end_commit[:7] if len(args.end_commit) > 7 else args.end_commit
    ax.set_title(f"Commits over time — {args.branch} ({short_start} → {short_end})")

    legend_handles = [
        Line2D([0], [0], color=COLORS["lean_only"], linewidth=2, label="Lean only"),
        Line2D([0], [0], color=COLORS["julia_only"], linewidth=2, label="Julia only"),
        Line2D([0], [0], color=COLORS["both"], linewidth=2, label="Julia + Lean"),
        Line2D([0], [0], color=COLORS["neither"], linewidth=2, label="Neither"),
    ]
    ax.legend(handles=legend_handles, loc="upper left")

    plt.tight_layout()
    plt.savefig(args.output, dpi=150)
    print(f"Saved to {args.output}")


if __name__ == "__main__":
    main()
