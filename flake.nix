{
  description = "A devShell example";

  inputs = {
    nixpkgs.url      = "github:nixos/nixpkgs/nixos-unstable";
    flake-utils.url  = "github:numtide/flake-utils";
    # coq-lsp = { type = "git"; url = "https://github.com/ejgallego/coq-lsp.git"; submodules = true; };
  };

  outputs = { self, nixpkgs, flake-utils, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          config.allowUnfree = true;
        };
      in
      with pkgs;
      {
        devShell = mkShell rec {
          buildInputs = with coqPackages_8_15; [
            coq
          ];
        };
      }
      );
  }
