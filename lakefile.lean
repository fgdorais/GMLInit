import Lake
open Lake DSL

package GMLInit {
  moreLeanArgs := #["-Dlinter.unusedVariables=false"]
}

@[default_target]
lean_lib GMLInit {}

require std from git "https://github.com/leanprover/std4.git"@"5aa4ab4f0c096e8d0600e3ae41b8577dcf6edb13"
