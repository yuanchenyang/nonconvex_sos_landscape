#!/usr/bin/env bash
set -euo pipefail

workspace="${1:-/agent-workspace}"
local_lake_dir="${2:-/var/local/agent-workspace-lake}"
target="${workspace}/.lake"

if [[ "${EUID}" -ne 0 ]]; then
  echo "Run as root, for example: sudo $0 ${workspace} ${local_lake_dir}" >&2
  exit 1
fi

if [[ ! -d "${workspace}" ]]; then
  echo "Workspace does not exist: ${workspace}" >&2
  exit 1
fi

if [[ -L "${target}" ]]; then
  echo "Refusing to mount over symlink: ${target}" >&2
  exit 1
fi

if id -u vagrant >/dev/null 2>&1; then
  owner_uid="$(id -u vagrant)"
  owner_gid="$(id -g vagrant)"
else
  owner_uid="$(stat -c '%u' "${workspace}")"
  owner_gid="$(stat -c '%g' "${workspace}")"
fi

mkdir -p "${local_lake_dir}"
chown -R "${owner_uid}:${owner_gid}" "${local_lake_dir}"

if mountpoint -q "${target}"; then
  current_source="$(findmnt -n -o SOURCE --target "${target}" || true)"
  if [[ "${current_source}" == "${local_lake_dir}" ]]; then
    exit 0
  fi
  echo "${target} is already mounted from ${current_source}" >&2
  exit 1
fi

mkdir -p "${target}"

if ! find "${local_lake_dir}" -mindepth 1 -maxdepth 1 -print -quit | grep -q .; then
  if find "${target}" -mindepth 1 -maxdepth 1 -print -quit | grep -q .; then
    rsync -a "${target}/" "${local_lake_dir}/"
    chown -R "${owner_uid}:${owner_gid}" "${local_lake_dir}"
  fi
fi

mount --bind "${local_lake_dir}" "${target}"
