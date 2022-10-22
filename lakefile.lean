import Lake
open Lake DSL

package GMLInit {
  moreLeanArgs := #["-Dlinter.unusedVariables=false"]
}

@[default_target]
lean_lib GMLInit {}

require std from git "https://github.com/leanprover/std4.git"@"68c404a3bc72a44559fb58ae9ab74196abf9853d"
