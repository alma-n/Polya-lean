{
  description = "Polya-lean";

  inputs = {
    flake-parts.url = "github:hercules-ci/flake-parts";
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    # nixpkgs_xhalo32.url = "github:xhalo32/nixpkgs";
    devenv.url = "github:cachix/devenv";
  };

  outputs =
    inputs@{ flake-parts, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      imports = [ inputs.devenv.flakeModule ];
      systems = [
        "x86_64-linux"
        "aarch64-linux"
        "aarch64-darwin"
        "x86_64-darwin"
      ];
      perSystem =
        {
          config,
          self',
          inputs',
          pkgs,
          system,
          ...
        }:
        let
          # pkgs_xhalo32 = inputs.nixpkgs_xhalo32.legacyPackages.${system};
          # inherit (pkgs_xhalo32.python312Packages) leanblueprint;

          watch-blueprint = pkgs.writeShellScriptBin "watch-blueprint" ''
            rm -rf blueprint/web
            leanblueprint web
            echo "Watching for changes in blueprint/src/..."
            ${pkgs.inotify-tools}/bin/inotifywait -q -e close_write,moved_to,create -r -m ./blueprint/src/*.tex |
              while read -r directory events filename; do
                rm -rf blueprint/web
                leanblueprint web
              done
          '';
        in
        {
          # Per-system attributes can be defined here. The self' and inputs'
          # module parameters provide easy access to attributes of the same
          # system.

          devenv.shells.default = {
            packages = [
              # leanblueprint
              watch-blueprint
              pkgs.python3Packages.pygraphviz
              pkgs.elan
            ];
            languages.python = {
              enable = true;
              # package = python;
              venv.enable = true;
            };
          };
        };
      flake = {
        # The usual flake attributes can be defined here, including system-
        # agnostic ones like nixosModule and system-enumerating ones, although
        # those are more easily expressed in perSystem.
      };
    };
}
