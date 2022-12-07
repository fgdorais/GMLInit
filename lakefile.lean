import Lake
open Lake DSL

package GMLInit {
  moreLeanArgs := #["-Dlinter.unusedVariables=false"]
}

@[default_target]
lean_lib GMLInit {}

require std from git "https://github.com/leanprover/std4.git"@"main"
