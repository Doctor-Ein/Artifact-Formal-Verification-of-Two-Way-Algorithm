# Artifact for Anonymous Submission

This repository contains the artifact accompanying an anonymous submission
under double-blind review. It includes mechanized Coq developments for
specifying and verifying the two-way string matching algorithm.


All key proofs have been completed, and we will finalize the remaining refinements, including comments and naming, by February 11.

## Code Structure

Directories/files denoted with `*` are dependencies or auxiliary libraries
that are not the main focus of the paper.

```text
.
├── sets*          # Dependency: Library for set theory
├── fixedpoints*   # Dependency: Library for order theory and fixed points
├── ListLibDev*    # Dependency: List-related auxiliary library
├── monadlib       # Core monad library
│   ├── set_monad
│   │   ├── Monad.v       # Monad definitions and notations
│   │   ├── SetBasic.v    # Constructors and properties
│   │   └── SetHoare.v    # Hoare logic and tactics
│   ├── state_rel_monad
│   │   ├── StateRelBasic.v    # Constructors and properties
│   │   ├── StateRelHoare.v    # Hoare logic and tactics
│   │   └── safeexec_lib.v*    # Auxiliary library for relational Hoare logic
│   └── monad_err
│       ├── MonadErrBasic.v    # Basic constructors and properties
│       ├── MonadErrLoop.v     # Loop constructors and properties
│       ├── MonadErrHoare.v    # Hoare logic and tactics
│       └── monadsafe_lib.v*   # Auxiliary library for relational Hoare logic
└── examples
    ├── MaximalSuffix.v   # Preprocess phase proof
    ├── TwoWayMatch.v     # Match phase proof
    └── TwoWayComplete.v  # Main proof: complete verification of two-way algorithm
````

**Note.**
The main technical developments corresponding to the paper are located in
the `examples/` directory.

## Build Instructions

* Coq version: **8.20.1**

### Linux / macOS

Ensure that `coqc` is in your `PATH`. Then run:

```bash
make
```

### Windows

On Windows, a configuration file is required to specify the Coq installation
path.

Create a file named `CONFIGURE` (without extension) in the root directory.

**Example (Cygwin):**

```text
COQBIN=/cygdrive/d/Coq-8.20.1/bin/
SUF=
```

**Example (PowerShell):**

```text
COQBIN=D:\Coq-8.20.1\bin\\
SUF=.exe
```

Make sure `make` is available:

```bash
make --version
```

If not, `mingw32-make` or `mingw64-make` can be used as alternatives:

```bash
mingw32-make --version
# or
mingw64-make --version
```

Then compile the project by running:

```bash
make
```

---

All identifying information has been removed for double-blind review.