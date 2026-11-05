# Contributing

Use the Lean and dependency versions committed to this repository. Build changes with:

```sh
lake exe cache get
lake build MainTheorems
```

Follow the mathlib [style](https://leanprover-community.github.io/contribute/style.html)
and [documentation](https://leanprover-community.github.io/contribute/doc.html)
guidelines, using syntax supported by Lean 4.19.0.

- Write comments and documentation in English.
- Start Lean files with a copyright and license header, imports, and a titled
  `/-! ... -/` module docstring describing the mathematics.
- Use `/-- ... -/` for declaration documentation and `/- ... -/` or `--` for
  implementation comments. State required hypotheses clearly.
- Keep the distinction between cited reference inputs and proved conclusions explicit.
- Add bibliographic references to `docs/references.bib`.
- Prefer lines of at most 100 characters in new code and prose.
- Keep caches, logs, credentials, and personal contact details out of commits.
