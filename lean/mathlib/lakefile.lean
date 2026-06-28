import Lake
open Lake DSL

package "QIQTH" where
  version := v!"0.1.0"
  keywords := #["math"]
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]

require "leanprover-community" / "mathlib" @ git "v4.30.0"

-- PhysLean (HEPLean): pinned to the last v4.30.0 commit (d0ee4af), whose Mathlib pin
-- (c5ea00351c28 @ v4.30.0) EXACTLY matches QIQT-H's — so no Mathlib bump / rebuild is needed.
-- Provides the fermionic CAR creation/annihilation + Wick-algebra operator layer (FieldStatistic,
-- CreateAnnihilate, CrAnFieldOp, WickAlgebra) for the ELECTRON_FIELD E2-full / E5 operator tier.
require PhysLean from git
  "https://github.com/HEPLean/PhysLean.git" @ "d0ee4af6f490ce3811842fe874463bea8a33f4be"

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
