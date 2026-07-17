import Lake
open Lake DSL

package «Polya» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require VersoBlueprint from git "https://github.com/leanprover/verso-blueprint"@"v4.30.0"

-- require Verso from git "https://github.com/leanprover/verso"@"v4.30.0"

-- must be last, otherwise mathlib post-update hooks break :o
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.30.0"

@[default_target]
lean_lib Blueprint where
  globs := Glob.submodules `Blueprint

lean_exe «blueprint-gen» where
  root := `BlueprintMain

@[default_target]
lean_lib «Polya» where
  -- add any library configuration options here

require checkdecls from git "https://github.com/PatrickMassot/checkdecls.git"

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"
