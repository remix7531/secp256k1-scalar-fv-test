{
  description = "secp256k1 scalar formal verification - Rocq + VST dev environment";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-25.11";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        # CompCert has an unfree (INRIA) license.
        pkgs = import nixpkgs {
          inherit system;
          config.allowUnfreePredicate = pkg:
            builtins.elem (pkgs.lib.getName pkg) [ "compcert" ];
        };

        coqPkgs = pkgs.coqPackages_9_0;

        # VST 2.16 — extends nixpkgs VST/default.nix with Rocq 9.0 support.
        # Once merged upstream, replace with coqPkgs.VST.
        vst = coqPkgs.callPackage ./.nix/vst.nix {};

        rocq-mcp = pkgs.callPackage ./.nix/rocq-mcp.nix {};

      in {
        devShells.default = pkgs.mkShell {
          shellHook = ''
            unset COQPATH
          '';
          packages = [
            # Build tools & system libraries
            pkgs.clang
            pkgs.gcc
            pkgs.which
            pkgs.gmp
            pkgs.gmp.dev
            pkgs.gnumake
            pkgs.m4
            pkgs.pkg-config

            # ATP/SMT solvers
            pkgs.eprover
            pkgs.vampire
            pkgs.cvc4

            # Rocq ecosystem (nixpkgs coqPackages_9_0)
            coqPkgs.coq
            coqPkgs.compcert
            coqPkgs.flocq
            coqPkgs.coq-hammer
            coqPkgs.coq-lsp
            vst

            # Language server
            pkgs.rocqPackages_9_0.vsrocq-language-server

            # MCP server
            rocq-mcp
          ];
        };

        packages = {
          inherit vst rocq-mcp;
        };
      });
}
