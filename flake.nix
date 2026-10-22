{
	inputs = {
		nixpkgs.url     = "github:nixos/nixpkgs/nixpkgs-unstable";
		flake-utils.url = "github:numtide/flake-utils";
	};

	outputs = { self, nixpkgs, flake-utils }:
		flake-utils.lib.eachDefaultSystem(system:
			let
				pkgs = import nixpkgs { inherit system; };

				devBuildInputs = with pkgs; [
					cargo
					rustc
					rustfmt
					clippy
					rust-analyzer
					custom-agda
				];
				custom-agda = pkgs.agda.withPackages (p: with p; [
					standard-library
				]);
			in {
				devShells.default = pkgs.mkShell {
					packages = devBuildInputs;
				};
				packages.default = pkgs.rustPlatform.buildRustPackage rec {
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
