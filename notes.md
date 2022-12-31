## Parser related

```shell
target_dir="~/Documents/Semgus-Parser/SemgusParser"
nix shell nixpkgs#dotnet-sdk_6 -c bash -c "cd $target_dir; dotnet run -- --no-function-events --mode batch --format json; cd ~-" < input > output
```

or as an alias:

```shell
target_dir="~/Documents/Semgus-Parser/SemgusParser"
alias run-parser='nix shell nixpkgs#dotnet-sdk_6 -c bash -c "cd $target_dir; dotnet run -- --no-function-events --mode batch --format json; cd ~-"'
```

## mul-by-while

for the correct case: `(error "query failed: Stuck on a lemma")`
