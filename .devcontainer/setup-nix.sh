#!/bin/sh
set -eux

# Install Nix
curl -L https://nixos.org/nix/install | sh

# Source Nix
. /home/codespace/.nix-profile/etc/profile.d/nix.sh

# Enable flakes and nix-command
mkdir -p /home/codespace/.config/nix
echo "experimental-features = nix-command flakes" > /home/codespace/.config/nix/nix.conf

# Ensure Nix is available in the shell
echo ". /home/codespace/.nix-profile/etc/profile.d/nix.sh" >> /home/codespace/.bashrc
echo ". /home/codespace/.nix-profile/etc/profile.d/nix.sh" >> /home/codespace/.zshrc

# Enter the development shell
exec nix develop
