{
  description = "Constructive Logic and Formal Proof High-school Course";

  inputs = {
    flake-parts.url = "github:hercules-ci/flake-parts";
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    devenv.url = "github:cachix/devenv";
    lean4 = {
      url = "github:leanprover/lean4";
      inputs.nixpkgs.follows = "nixpkgs";
    };
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
          lib = pkgs.lib;
          pythonOverrides = [
            (final: prev: {
              plasTeX = pkgs.python3Packages.buildPythonPackage rec {
                pname = "plasTeX";
                version = "3.1";
                src = pkgs.fetchPypi {
                  inherit pname version;
                  hash = "sha256-ai7n+8plYdP0y9ef4/SRi5BUdXOCxUIrn9oyTWRqt30=";
                };

                propagatedBuildInputs = with final; [
                  typing-extensions
                  pillow
                  jinja2
                  unidecode
                ];

                doCheck = false; # TODO
              };

              plastexdepgraph = pkgs.python3Packages.buildPythonPackage rec {
                pname = "plastexdepgraph";
                version = "0.0.4";
                src = pkgs.fetchPypi {
                  inherit pname version;
                  hash = "sha256-LUw76Kn80lbGG67uTBWaQQfpjnSkUfCoD2wvcFv41L0=";
                };

                propagatedBuildInputs = with final; [
                  pygraphviz
                  plasTeX
                ];
              };

              plastexshowmore = pkgs.python3Packages.buildPythonPackage rec {
                pname = "plastexshowmore";
                version = "0.0.2";
                src = pkgs.fetchPypi {
                  inherit pname version;
                  hash = "sha256-8f6nIl6ufivT+RI1w2ySMQh+N5NZPIwTnDlVzQCPC1E=";
                };

                propagatedBuildInputs = with final; [ plasTeX ];
              };

              leanblueprint = pkgs.python3Packages.buildPythonPackage rec {
                pname = "leanblueprint";
                version = "0.0.10";
                src = pkgs.fetchPypi {
                  inherit pname version;
                  hash = "sha256-z514yxhEcJwVIKae38cEkEZgyC4NoxCbokhGgBPQZvc=";
                };
                propagatedBuildInputs = with final; [
                  plasTeX
                  plastexshowmore
                  plastexdepgraph
                  click
                  rich
                  rich-click
                  tomlkit
                  jinja2
                  GitPython
                ];

                doCheck = false;
              };
            })
          ];
          python = pkgs.python3.override { packageOverrides = lib.composeManyExtensions pythonOverrides; };
        in
        {
          # Per-system attributes can be defined here. The self' and inputs'
          # module parameters provide easy access to attributes of the same
          # system.

          devenv.shells.default = {
            packages =
              [
                (python.withPackages (p: [ p.leanblueprint ]))
                # inputs.lean4.packages.${system}.lake
                pkgs.elan
              ]
              ++ (with inputs.lean4.packages.${system}; [
                lean
                leanc
              ]);
            languages.python = {
              enable = true;
              package = python;
              # venv.enable = true;
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
