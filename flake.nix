{
	inputs = {
		nixpkgs.url     = "github:nixos/nixpkgs/nixpkgs-unstable";
		flake-utils.url = "github:numtide/flake-utils";
	};

	outputs = { self, nixpkgs, flake-utils }:
		flake-utils.lib.eachDefaultSystem(system:
			let
				pkgs = import nixpkgs { inherit system; };

				# store path of the frontend sources (already a drv input via prePatch)
				frontendSrc = ./frontend;

				devBuildInputs = with pkgs; [
					cargo
					rustc
					rustfmt
					clippy
					rust-analyzer
					sqlite
					custom-agda
				];
				custom-agda = pkgs.agda.withPackages (p: with p; [
					standard-library
				]);
				package = pkgs.rustPlatform.buildRustPackage rec {
					pname       = "formal-twitter";
					version     = "0.0.1";
					buildInputs = with pkgs; [ sqlite ];
					src         = ./backend;
					prePatch  = ''
						cp -r ${frontendSrc} ../frontend
					'';
					# pin frontend/app.js JS syntax at build time (nodejs stays OUT of buildInputs so the
					# rust hook cannot turn it into linker flags; we call the store binary by absolute path)
					preBuild = ''
						${pkgs.nodejs_24.out}/bin/node --check ${frontendSrc}/app.js
					'';
					cargoLock.lockFile = "${src}/Cargo.lock";
					# smoke.rs spawns live servers + raw TCP; impossible in the no-network sandbox
					# (rust hook gates the cargo-test check phase on dontCargoCheck, not skipTests)
					dontCargoCheck = true;
					meta.mainProgram = "formal-twitter";
					postInstall = ''
						cp -r ${frontendSrc} $out/frontend
					'';
				};
			in {
				devShells.default = pkgs.mkShell {
					packages = devBuildInputs;
				};
				packages.default = package;
				apps.default = {
					type    = "app";          # nix requires "app" (flake-utils mkApp uses the same)
					program = pkgs.lib.getExe package;
				};
			}
		);
}
