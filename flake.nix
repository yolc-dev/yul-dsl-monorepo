{
  description = "Nix flake for the YulDSL monorepo";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    foundry = {
      url = "github:shazow/foundry.nix/stable";
      inputs.flake-utils.follows = "flake-utils";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    solc = {
      url = "github:hellwolf/solc.nix";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs =
    {
      nixpkgs,
      flake-utils,
      foundry,
      solc,
      ...
    }:
    (flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [
            foundry.overlay
            solc.overlay
          ];
        };
        yolc_path = ./hs-pkgs/yol-suite;
        # default configurations
        haskellLib = pkgs.haskell.lib.compose;
        ghcId = "ghc912";
        ghcVer = pkgs.haskell.compiler.${ghcId}.version;
        solcId = "solc_0_8_28";
        commonDevInputs = with pkgs; [
          jq
          yq
          gnumake
        ];
        yolcBuildInputs = with pkgs; [
          # foundry and solc
          pkgs.${solcId}
          (solc.mkDefault pkgs pkgs.${solcId})
          foundry-bin
          # haskell tooling
          cabal-install
          haskell.compiler.${ghcId}
        ];
        localDevEnvInputs = with pkgs; [
          # haskell dev tooling
          cabal2nix
          haskell.packages.${ghcId}.haskell-language-server
          haskell.packages.ghc98.hlint
          haskell.packages.ghc98.stylish-haskell # it doesn't work with 9.10
          # other dev tooling
          nodePackages.nodemon
          shellcheck
        ];
        localShellHook = ''
          # This makes binaries of this project available for testing, e.g. `yolc`
          export PATH=$PWD/hs-pkgs/yol-suite/bin:$PATH
          # Localy testing yolc requires package db to be provided
          GHC_ID=$(ghc --info | ghci -e 'readFile "/dev/stdin" >>= putStrLn . snd . last . filter ((== "Project Unit Id"). fst) . (read :: String -> [(String, String)])')
          export YOLC_PACKAGE_DB=$PWD/build/yolc/''${GHC_ID}-dist/packagedb/ghc-${ghcVer}

          # foundry to use solc.nix provided solc
          export FOUNDRY_OFFLINE=true
          export FOUNDRY_SOLC_VERSION=${pkgs.lib.getExe pkgs.${solcId}}
        '';

        # TODO: package for nixpkgs-based build environment
        #
        # yolcPackages = pkgs.haskell.packages.${ghcId}.override {
        #   overrides = self: super: {
        #     # yolc
        #     simple-sop = self.callPackage ./hs-pkgs/simple-sop { };
        #     eth-abi = self.callPackage ./hs-pkgs/eth-abi { };
        #     yul-dsl = self.callPackage ./hs-pkgs/yul-dsl { };
        #     yul-dsl-pure = self.callPackage ./hs-pkgs/yul-dsl-pure { };
        #     yul-dsl-linear-smc = self.callPackage ./hs-pkgs/yul-dsl-linear-smc { };
        #     yol-suite = self.callPackage ./hs-pkgs/yol-suite { };
        #     # dependency fixes:
        #     crypton = haskellLib.dontCheck super.crypton;
        #   };
        # };
      in
      {
        # local development shells

        devShells.local = pkgs.mkShell {
          buildInputs = commonDevInputs ++ yolcBuildInputs ++ localDevEnvInputs;
          shellHook = localShellHook;
        };
        devShells.minimal = pkgs.mkShell {
          buildInputs = commonDevInputs ++ yolcBuildInputs;
          shellHook = localShellHook;
        };
      }
    ));
}
