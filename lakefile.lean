import Lake
open Lake DSL

package GMLInit {
  moreLeanArgs := #["-Dlinter.unusedVariables=false"]
}

@[default_target]
lean_lib GMLInit {}

require Std from git "https://github.com/fgdorais/std4" @ "reustep"
