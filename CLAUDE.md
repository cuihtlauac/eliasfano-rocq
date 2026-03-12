# Elias-Fano Verified Implementation

## Build

Use `./build.sh` (wrapper around `opam exec -- dune build`).

```
./build.sh
```

## Permissions

- Writing files in `/tmp/` is always allowed — do not prompt for confirmation.
- Using shell redirection (`<<`, `>`, `|`) in Bash commands is always allowed.
