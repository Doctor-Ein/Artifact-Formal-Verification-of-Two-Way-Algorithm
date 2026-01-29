# Artifact for Anonymous Submission

This repository contains the artifact accompanying an anonymous submission
under double-blind review. It includes mechanized Coq developments for
specifying and verifying sequential algorithms.

## Code Structure

Directories/files denoted with `*` are dependencies or auxiliary libraries
that are not the main focus of the paper.

```text
.
├── sets*          # Dependency: Library for set theory
├── fixedpoints*   # Dependency: Library for order theory and fixed points
├── ZListLib*      # Dependency: List-related auxiliary library
├── monadlib       # Core monad library
│   ├── set_monad
│   │   ├── Monad.v        # Monad definitions and notations
│   │   ├── SetBasic.v     # Constructors and properties
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
    ├── DFS.v        # Example: DFS in the state relation monad
    ├── KMP.v        # Main proof: two-stage verification of KMP in the set monad
    ├── KMPErr.v     # KMP in the monad with error
    └── Listlib.v*   # Auxiliary list lemmas used in the KMP proof
````

**Note.**
The main technical developments corresponding to the paper are located in
the `examples/` directory.

## Build Instructions

* Coq version: **8.20.1**

Before compilation, please initialize and update git submodules:

```bash
git submodule init
git submodule update
```

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
COQBIN=/cygdrive/d/Coq-8.15/bin/
SUF=
```

**Example (PowerShell):**

```text
COQBIN=D:\Coq-8.15\bin\\
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

