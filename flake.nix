{
  description = "secp256k1 scalar formal verification - Rocq + VST";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    flake-compat = {
      url = "github:NixOS/flake-compat";
      flake = false;
    };

    # NOTE: pinned to the `feat/nix-flake` branch on the remix7531 fork while
    # the Nix flake is in review upstream. Swap to
    # `github:LLM4Rocq/rocq-mcp/<tag>` once the flake lands there.
    rocq-mcp.url = "github:remix7531/rocq-mcp/feat/nix-flake";
    rocq-mcp.inputs.flake-utils.follows = "flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils, flake-compat, rocq-mcp, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          config.allowUnfreePredicate = pkg:
            builtins.elem (pkgs.lib.getName pkg) [ "compcert" ];
        };

        coqPkgs = pkgs.coqPackages_9_0;
      in {
        devShells.default = pkgs.mkShell {
          shellHook = ''
            unset COQPATH
          '';
          packages = (with coqPkgs; [
            VST
            compcert
            coq
            coq-hammer
            coq-lsp
            flocq
            vsrocq-language-server
          ]) ++ (with pkgs; [
            clang
            cvc4
            eprover
            gcc
            gmp
            gmp.dev
            gnumake
            m4
            pkg-config
            vampire
            which
          ]) ++ [
            rocq-mcp.packages.${system}.rocq-mcp
          ];
        };
      });
}
