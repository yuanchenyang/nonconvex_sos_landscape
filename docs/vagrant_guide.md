# Vagrant Development VM

This repository includes a [Vagrant](https://www.vagrantup.com/) configuration
(`Vagrantfile`) for a reproducible Ubuntu 24.04 guest with the same
Julia/Lean/TeX tooling the project expects. Use it when you prefer an isolated
VM instead of installing tools on the host.

## Prerequisites (host machine)

1. **Vagrant** — Install from your OS package manager or
   [vagrantup.com](https://www.vagrantup.com/downloads).
2. **VirtualBox** — The `Vagrantfile` is configured for the
   `virtualbox` provider (see `config.vm.provider "virtualbox"`). Install
   [VirtualBox](https://www.virtualbox.org/) and ensure `VBoxManage` is on your
   `PATH`.
3. **Resources** — The VM is set to **16 GB RAM** and **4 CPUs**. Ensure the
   host can spare that; edit `vb.memory` and `vb.cpus` in `Vagrantfile` if
   needed.
4. **Disk** — First boot downloads the base box and provisioning packages;
   allow several gigabytes free.

Other providers (VMware, libvirt, etc.) are not configured in this repo; you
would need to add a matching `config.vm.provider` block yourself.

## Quick start

From the repository root (where `Vagrantfile` lives):

```bash
vagrant up
vagrant ssh
```

Inside the guest, the project is mounted at **`/agent-workspace`** (not the
default `/vagrant`, which is disabled). Work there as you would on the host:

```bash
cd /agent-workspace
```

## What provisioning does

On first boot, `scripts/vagrant-provision.sh` runs (once per new machine). It
roughly:

- Installs system packages (build tools, Git, TeX/Rubber, CMake, Python, Node,
  etc.), including `bubblewrap`.
- Installs **Julia** using the version in `julia/Manifest.toml` (the
  `Vagrantfile` passes this as `JULIA_VERSION`).
- Installs **elan** and the **Lean** toolchain pinned in `lean-toolchain`.
- Enables unprivileged user namespaces in the guest so sandboxed tools that
  rely on `bubblewrap` can start normally.
- Configures login `PATH` for elan via `/etc/profile.d/agent-workspace-env.sh`.

The initial provision script is **not idempotent** (it is meant for a fresh
VM). For a clean toolchain install, prefer `vagrant destroy` then
`vagrant up` instead of re-running provisioning on a dirty machine.

## Synced folder and Lake

- The repo is synced to **`/agent-workspace`**.
- On every `vagrant up`, a **bind mount** is applied so **`/agent-workspace/.lake`**
  lives on the guest’s local disk (`scripts/mount-local-lake.sh`). This avoids
  sync-related issues when Lake builds Lean/mathlib artifacts.

After `vagrant ssh`, run Lake from `/agent-workspace` as usual; see
[lean_guide.md](lean_guide.md) for build and verification commands.

## Everyday commands (host)

| Command | Purpose |
|--------|---------|
| `vagrant up` | Start the VM (provision on first run). |
| `vagrant halt` | Stop the VM. |
| `vagrant ssh` | Open a shell in the guest. |
| `vagrant destroy` | Delete the VM disk (clean slate next `up`). |
| `vagrant reload --provision` | Restart and re-run provisioners (use sparingly). |

## Julia inside the VM

Julia project setup matches the host workflow; see
[julia_guide.md](julia_guide.md). Use `julia` in `/agent-workspace/julia` or
open a REPL and `]` to activate the project as documented there.

## Troubleshooting

- **VirtualBox errors** — Confirm VirtualBox kernel modules are loaded and no
  other hypervisor locks VT-x/AMD-V.
- **Out of memory** — Lower `vb.memory` in `Vagrantfile` or close host
  applications.
- **Stale or broken VM** — `vagrant destroy -f` then `vagrant up` for a fresh
  guest.
