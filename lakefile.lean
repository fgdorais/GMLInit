import Lake
open Lake DSL

package GMLInit {
  moreLeanArgs := #["-Dlinter.unusedVariables=false"]
}

@[default_target]
lean_lib GMLInit {}

require std from git "https://github.com/fgdorais/std4" @ "nat-all"

require Logic from git "https://github.com/fgdorais/logic4" @ "main"
