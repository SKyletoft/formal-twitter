{
	inputs = {
		nixpkgs.url     = "github:nixos/nixpkgs/nixpkgs-unstable";
		flake-utils.url = "github:numtide/flake-utils";
		rust-overlay = {
			url = "github:oxalica/rust-overlay";
			inputs.nixpkgs.follows = "nixpkgs";
		};
	};

	outputs = { self, nixpkgs, rust-overlay, flake-utils }:
		flake-utils.lib.eachDefaultSystem(system:
			let
				pkgs = import nixpkgs {
					inherit system;
					overlays = [ rust-overlay.overlays.default ];
				};

				rustToolchain = pkgs.rust-bin.selectLatestNightlyWith (toolchain: toolchain.default.override {
					extensions = [ "rust-src" "rust-analyzer" "miri" ];
					targets = [ "x86_64-unknown-linux-gnu" ];
				});
				rustPlatform = pkgs.makeRustPlatform {
					cargo = rustToolchain;
					rustc = rustToolchain;
				};

				devBuildInputs = with pkgs; [
					rustToolchain
					cargo-fuzz

					custom-agda
					(ghc.withPackages(p: with p; [
						QuickCheck
						haskell-language-server
						fourmolu
						BNFC
						alex
						happy
					]))
				];
				custom-agda = pkgs.agda.withPackages (p: with p; [
					standard-library
				]);
			in {
				devShells.default = pkgs.mkShell {
					packages = devBuildInputs;
				};
				packages.default = rustPlatform.buildRustPackage rec {
					pname = "formal-twitter";
					version = "0.0.1";
					src = ./backend;
					prePatch = ''
						cp -r ${./frontend} ../frontend
					'';
					cargoLock.lockFile = "${src}/Cargo.lock";
					postInstall = ''
						cp -r ${./frontend} $out/frontend
					'';
				};
			}
		);
}
