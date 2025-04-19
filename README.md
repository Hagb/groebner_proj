# groebner

This project presents a formalization of Gröbner basis theory in the Lean 4 theorem prover, establishing the mathematical infrastructure required for automated algebraic reasoning. By constructing certified implementations of fundamental algorithms and theorems, we aim to bridge the gap between computational algebra and interactive theorem proving.

## Introduction

Gröbner bases are a central tool in computational algebra, with wide applications in solving systems of polynomial equations, ideal membership problems, and more. Despite their ubiquity in computer algebra systems, rigorous formal verification of Gröbner basis theory remains a challenge.

This project tackles that challenge by developing a fully verified formalization of Gröbner basis theory using [Lean 4](https://leanprover.github.io/), a functional programming language and proof assistant.

## Project Resources

We maintain a set of web-based resources to track and explore the formalization effort:

- 📘 **[Project Homepage](https://wuprover.github.io/groebner_proj/)**
  An overview of the project’s goals, scope, and current progress.

- 📐 **[Formalization Blueprint](https://wuprover.github.io/groebner_proj/blueprint/)**
  A detailed list of definitions, lemmas, and theorems, including their proof status and logical dependencies.

- 🔗 **[Dependency Graph](https://wuprover.github.io/groebner_proj/blueprint/dep_graph_document.html)**
  A visual representation of the dependency structure of the formalized components.

These tools help us manage development, track formalization progress, and guide future contributors.

## Installation

To use this project, you’ll need to have Lean 4 and its package manager `lake` installed. If you don’t already have Lean 4 set up, follow the [Lean 4 installation instructions](https://leanprover-community.github.io/get_started.html).

Once Lean is installed, you can clone this repository and build the project:

```bash
git https://github.com/WuProver/groebner_proj.git
cd groebner_proj
lake exe cache get
lake build
```

## Reference
This project draws heavily from the following reference:
[Ideals, Varieties, and Algorithms](https://link.springer.com/book/10.1007/978-3-319-16721-3)