# ConjointSD

## GitHub configuration

To set up your new GitHub repository, follow these steps:

* Under your repository name, click **Settings**.
* In the **Actions** section of the sidebar, click "General".
* Check the box **Allow GitHub Actions to create and approve pull requests**.
* Click the **Pages** section of the settings sidebar.
* In the **Source** dropdown menu, select "GitHub Actions".

After following the steps above, you can remove this section from the README file.

## Building with Lake

1. Install Lean toolchain via `apt-get install elan` (the `elan` package bundles the Lean and Lake installer).
2. Ensure the toolchain from `lean-toolchain` is available: `elan toolchain install $(cat lean-toolchain)`.
3. Run `lake build` from the repo root. The first invocation downloads mathlib and can take a while, but subsequent runs reuse the cached build in `.lake/`.

A successful build was started in this environment after installing `elan`, though compiling mathlib takes significant time on a fresh cache.
