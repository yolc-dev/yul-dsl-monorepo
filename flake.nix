{
  description = "Nix flake for the YulDSL monorepo";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    solc = {
      url = "github:hellwolf/solc.nix";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = { nixpkgs, flake-utils, solc, ... }: (flake-utils.lib.eachDefaultSystem (system:
    let
      pkgs = import nixpkgs {
        inherit system;
        overlays = [
          solc.overlay
        ];
      };
      commonDevInputs = with pkgs; [
        jq
        shellcheck
      ];
      shellHook = ''
        # This makes binaries of this project available for testing, e.g. `yolc`
        export PATH=$PWD/hs-pkgs/yol-suite/bin/:$PATH
      '';
    in {
      devShells.default = pkgs.mkShell {
        buildInputs = with pkgs; commonDevInputs ++ [
          # local dev tooling
          nodePackages.nodemon
          # solc
          solc_0_8_28
          # haskell tooling
          cabal-install
          haskell.compiler.ghc910
          haskell.packages.ghc98.hlint_3_8
          haskell.packages.ghc98.stylish-haskell # it doesn't work with 9.10
          haskell.packages.ghc910.haskell-language-server
        ];
        inherit shellHook;
      };
    }));
  }
