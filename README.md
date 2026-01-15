# Tactics Generation

A minimal Lean 4 project.

## Prerequisites

- Lean 4 with Lake ([installation guide](https://leanprover.github.io/lean4/doc/setup.html))

## Setup

```bash
lake update
lake build
lake exe tactics_generation
```

## Project Structure

```
tactics_generation/
├── lakefile.toml      # Project configuration
├── lean-toolchain     # Lean version
├── lake-manifest.json # Dependency lock
└── Main.lean          # Entry point
```
