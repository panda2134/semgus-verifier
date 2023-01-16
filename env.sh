#!/usr/bin/env bash

target_dir="$HOME/Documents/Semgus-Parser/SemgusParser"
alias run-parser='nix shell nixpkgs#dotnet-sdk_6 -c bash -c "cd $target_dir; dotnet run -- --no-function-events --mode batch --format json; cd ~-"'
