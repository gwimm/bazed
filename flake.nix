{
  description = "The baz editor";

  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";

    advisory-db = {
      url = "github:rustsec/advisory-db";
      flake = false;
    };

    crane = {
      url = "github:ipetkov/crane";
      inputs.nixpkgs.follows = "nixpkgs";
    };

    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = {
    self,
    advisory-db,
    crane,
    flake-utils,
    nixpkgs,
    rust-overlay,
  }:
    flake-utils.lib.eachDefaultSystem (system: let
      pkgs = import nixpkgs {
        inherit system;
        overlays = [
          (import rust-overlay)
        ];
      };

      inherit (pkgs) lib;

      rustToolchain = pkgs.rust-bin.fromRustupToolchainFile ./rust-toolchain.toml;
      craneLib = (crane.mkLib pkgs).overrideToolchain rustToolchain;
      src = lib.cleanSourceWith {
        src = ./.;
        filter = let
          node = path: _: builtins.match "node_packages" path != null || builtins.match ".*\.json$" path != null;
          rustOrNode = path: type: craneLib.filterCargoSources path type || node path type;
        in
          rustOrNode;
      };

      buildInputs = with pkgs; [
        cargo-deny
        glib
        gtk3
        libsoup
        nodejs
        pkg-config
        webkitgtk
      ];

      # TODO: cachix
      cargoArtifacts = craneLib.buildDepsOnly {
        inherit src buildInputs;
      };

      bazed = craneLib.buildPackage {
        inherit cargoArtifacts src buildInputs;
        doCheck = false; # already done with nextest
      };
    in {
      checks =
        {
          inherit bazed;

          bazed-clippy = craneLib.cargoClippy {
            inherit cargoArtifacts src buildInputs;
            cargoClippyExtraArgs = "--all-targets -- --deny warnings";
          };

          bazed-doc = craneLib.cargoDoc {
            inherit cargoArtifacts src buildInputs;
          };

          bazed-fmt = craneLib.cargoFmt {
            inherit src;
          };

          bazed-audit = craneLib.cargoAudit {
            inherit src advisory-db;
          };

          bazed-nextest = craneLib.cargoNextest {
            inherit cargoArtifacts src buildInputs;
            partitions = 1;
            partitionType = "count";
          };
        }
        // lib.optionalAttrs (system == "x86_64-linux") {
          # NB: cargo-tarpaulin only supports x86_64 systems
          # Check code coverage (note: this will not upload coverage anywhere)
          bazed-coverage = craneLib.cargoTarpaulin {
            inherit cargoArtifacts src;
          };
        };

      packages.default = bazed;

      apps.default = flake-utils.lib.mkApp {
        drv = bazed;
      };

      devShells.default = pkgs.mkShell {
        inputsFrom = builtins.attrValues self.checks;

        nativeBuildInputs = with pkgs; [
          rustToolchain
        ];
      };
    });
}
