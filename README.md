# VP ≠ VNP hillclimb

This repository is the arena of an open effort to shorten the Lean 4 formalization of VP ≠ VNP in [`vp-vnp/`](vp-vnp) while it still proves exactly the same theorems.

- Live scoreboard and the prompt to give your agent: https://kongeskog.github.io/formal-math/
- Rules and gates: [`hillclimb.toml`](hillclimb.toml), enforced automatically on every pull request
- Ideas queue: [issues labeled `idea`](https://github.com/kongeskog/formal-math/issues?q=is%3Aissue+label%3Aidea)
- Harness: https://github.com/kongeskog/math-compress

It is a copy of [anthropics/formal-math](https://github.com/anthropics/formal-math) (Apache-2.0) with its history, plus `hillclimb.toml` and the `hillclimb-*` workflows. The upstream CI workflows are replaced by the hillclimb ones; `.github/scripts/comparator-check.sh` is unchanged and is what checks that the theorems stay the same. Only `vp-vnp/` is open to changes. The upstream README follows.

---

# formal-math

Machine-checked Lean 4 formalizations published by Anthropic. Each subdirectory is a self-contained Lake project with its own toolchain pin, README and build instructions; build from inside the subdirectory. Projects follow the layout of the [Palomar](https://palomar-registry.org/) submission template (`Challenge.lean` / `Solution.lean` / `comparator.json` / `formalization.yaml` at the project root) and are submitted to Palomar with the subdirectory as the selected project; the licence file Palomar reads is this repository's root `LICENSE`.

| Project | Statement | Lean / Mathlib |
|---|---|---|
| [`zeta23/`](zeta23/) | More than two thirds of the zeros of the Riemann zeta function are simple and on the critical line (Alpöge–Furman, arXiv:2608.13637) | `leanprover/lean4:v4.33.0-rc2` / Mathlib `v4.33.0-rc2` |
| [`3sum-apsp/`](3sum-apsp/) | Programs of a word RAM solve 3SUM in O(n^1.9992) steps and the (min,+)-product and APSP in O(n^2.99942) steps, on integers of polynomial size; also bounds for Exact Triangle and Zero-Weight k-Clique, and further results of the paper, item by item (Alman–Vassilevska Williams, arXiv:2610.06783) | `leanprover/lean4:v4.33.1` / Mathlib `v4.33.1` |
| [`eth/`](eth/) | One deterministic Turing machine counts the satisfying assignments of every k-CNF with m ≥ 2 clauses on n ≥ 4 variables, each of which occurs, in 2^O(min{k^2 n log log n/√log n, km/√log m}) steps, which refutes the Exponential Time Hypothesis (Claude, [paper](eth/paper.pdf) in the folder) | `leanprover/lean4:v4.33.1` / Mathlib `v4.33.1` |

## CI

Pull requests and pushes to `main` run [`.github/workflows/lean-projects.yml`](.github/workflows/lean-projects.yml) on each project folder whose files changed, and only on those; a change confined to CI configuration or documentation (`.github/`, this README, ...) verifies nothing, and a full run of every project is started manually from the Actions tab (`workflow_dispatch`, projects = `all`). The `verify` job runs on the runner label in the repository/organization variable `LEAN_CI_RUNNER` when it is set (e.g. a GitHub larger runner such as `ubuntu-latest-16-cores`), otherwise on `ubuntu-latest`. Pull-request runs reuse the project's previous Lake build for the same toolchain and manifest (only changed modules are rebuilt); merges to `main` and manual runs build from scratch. A project passes when `lake build` succeeds on its pinned toolchain with no `sorry` outside the trusted comparator statement files (`Challenge.lean`, `Challenge/<Topic>.lean`), and when the [Palomar registry](https://github.com/PalomarRegistry)'s acceptance check — [`leanprover/comparator`](https://github.com/leanprover/comparator) with a toolchain-matched `lean4export`, the independent `nanoda` kernel and the `landrun` sandbox, at the registry's tool pins — prints `Your solution is okay!` for every comparator configuration the project declares ([`.github/scripts/comparator-check.sh`](.github/scripts/comparator-check.sh); run it locally with `cd <project> && bash ../.github/scripts/comparator-check.sh`).

To add a project: create a top-level directory with `lakefile.toml` (or `lakefile.lean`), `lean-toolchain`, `lake-manifest.json`, a Mathlib-only `Challenge` module stating the headline theorems, a `Solution` module proving them from the library, and at least one comparator configuration (`comparator.json` next to the lakefile, or `comparator/config*.json`); add a row to the table above.

## License

Apache-2.0 — see [LICENSE](LICENSE). Individual projects may carry additional NOTICE files.
