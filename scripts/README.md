# scripts/

Copied unchanged from the conductor template (`template/scripts/`), which copied them unchanged from the
Palomar-registered repositories the template was distilled from. Their docstrings and the CI header name the
origin as the PalomarRegistry/PalomarTemplate checker of the same name.

- `check-lean-sources.py` — module-system header, no `.lean` symlinks, file-size limits.
- `validate-formalization.rb` — `formalization.yaml` v0.4 shape, Apache-2.0, no remaining `TEMPLATE:` values.
- `verify-comparator.sh` — `lake comparator` with the toolchain's bundled nanoda and con-ron kernels.
  It runs `lake exe cache get` (downloads Mathlib's prebuilt oleans) and then `lake comparator`, which builds
  and exports Challenge and Solution inside a `bwrap` sandbox. It is meant for the CI runner (job "Check
  statement against solution"). It is kept byte-identical to the Palomar copy, so do not edit it. On a conductor
  host, `.lake` comes from `conductor lean lake-clone`, and the local statement check is
  `conductor lean probe fidelity --tree .`, which builds and fetches nothing.

License: distributed under this repository's `LICENSE` (Apache-2.0), as in the repositories they were copied
from.
