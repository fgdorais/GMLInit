import Lake
open Lake DSL

package GMLInit {
  moreLeanArgs := #["-Dlinter.unusedVariables=false"]
}

@[default_target]
lean_lib GMLInit {}

require std from git "https://github.com/leanprover/std4" @ "main"

require extra from git "https://github.com/fgdorais/extra4" @ "main"

require logic from git "https://github.com/fgdorais/logic4" @ "main"
