# -*- mode: ruby -*-
# vi: set ft=ruby :

def julia_version_from_manifest(manifest_path)
  return nil unless File.file?(manifest_path)

  File.foreach(manifest_path) do |line|
    m = line.match(/^julia_version\s*=\s*"([^"]+)"/)
    return m[1] if m
  end
  nil
end

vm_name = File.basename(Dir.getwd)
manifest_path = File.expand_path("julia/Manifest.toml", __dir__)
julia_version = julia_version_from_manifest(manifest_path)
unless julia_version
  raise "Could not read julia_version from #{manifest_path}"
end
Vagrant.configure("2") do |config|
  # The most common configuration options are documented and commented below.
  # For a complete reference, please see the online documentation at
  # https://docs.vagrantup.com.

  # Every Vagrant development environment requires a box. You can search for
  # boxes at https://vagrantcloud.com/search.
  config.vm.box = "bento/ubuntu-24.04"

  # Disable automatic box update checking. If you disable this, then
  # boxes will only be checked for updates when the user runs
  # `vagrant box outdated`. This is not recommended.
  # config.vm.box_check_update = false

  # Create a forwarded port mapping which allows access to a specific port
  # within the machine from a port on the host machine. In the example below,
  # accessing "localhost:8080" will access port 80 on the guest machine.
  # NOTE: This will enable public access to the opened port
  # config.vm.network "forwarded_port", guest: 80, host: 8080

  # Create a forwarded port mapping which allows access to a specific port
  # within the machine from a port on the host machine and only allow access
  # via 127.0.0.1 to disable public access
  # config.vm.network "forwarded_port", guest: 80, host: 8080, host_ip: "127.0.0.1"

  # Create a public network, which generally matched to bridged network.
  # Bridged networks make the machine appear as another physical device on
  # your network.
  # config.vm.network "public_network"

  config.vm.synced_folder ".", "/vagrant", disabled: true
  config.vm.synced_folder ".", "/agent-workspace"

  # Provider-specific configuration so you can fine-tune various
  # backing providers for Vagrant. These expose provider-specific options.
  # Example for VirtualBox:
  #
   config.vm.provider "virtualbox" do |vb|
     # Display the VirtualBox GUI when booting the machine
     # vb.gui = true

     # Customize the amount of memory on the VM:
     vb.memory = "16000"
     vb.cpus = "4"
     vb.name = vm_name
     vb.customize ["modifyvm", :id, "--audio", "none"]
     vb.customize ["modifyvm", :id, "--usb", "off"]
   end
  #
  # View the documentation for the provider you are using for more
  # information on available options.

  # Initial VM setup (runs once on `vagrant up` / first provision; script is not idempotent).
  config.vm.provision "shell",
    env: { "JULIA_VERSION" => julia_version },
    path: "scripts/vagrant-provision.sh"

  # Keep Lake artifacts on the VM's local filesystem instead of the shared folder.
  # This is necessary to prevent VM file-syncing errors when building lean
  config.vm.provision "shell", run: "always", inline: <<-'SHELL'
    set -euo pipefail
    bash /agent-workspace/scripts/mount-local-lake.sh /agent-workspace /var/local/agent-workspace-lake/root
  SHELL
end
