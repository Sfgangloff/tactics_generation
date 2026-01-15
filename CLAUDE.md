# CLAUDE.md

Minimal Lean 4 project using Lake with Batteries dependency.

## Commands

```bash
lake update   # Fetch dependencies
lake build    # Build the project
lake exe tactics_generation  # Run executable
```

## Structure

```
lakefile.toml      # Project config
lean-toolchain     # Lean version
lake-manifest.json # Dependency lock
Main.lean          # Entry point
```
