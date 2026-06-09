import Lake
open Lake DSL

package "QIQTH" where
  version := v!"0.1.0"
  keywords := #["math"]
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]

require "leanprover-community" / "mathlib" @ git "v4.30.0"

@[default_target]
lean_lib «QIQTH» where
  -- add any library configuration options here

-- Blueprint tooling: verify every `\lean{...}` reference denotes a real declaration.
require checkdecls from git "https://github.com/PatrickMassot/checkdecls.git"

-- API documentation generator (doc-gen4). Only pulled in dev builds so ordinary
-- `lake build` stays lightweight: enable with `lake -R -Kenv=dev build QIQTH:docs`.
meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"
