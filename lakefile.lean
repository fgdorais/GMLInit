import Lake
open Lake DSL

package GMLInit {
  moreLeanArgs := #["-Dlinter.unusedVariables=false"]
}

@[defaultTarget]
lean_lib GMLInit {}

require std from git "https://github.com/leanprover/std4.git"@"4ae14128fd57e260c13524b9743c36b124a3a2d9"
