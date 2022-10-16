import Lake
open Lake DSL

package GMLInit {
  moreLeanArgs := #["-Dlinter.unusedVariables=false"]
}

@[defaultTarget]
lean_lib GMLInit {}

require std from git "https://github.com/leanprover/std4.git"@"e564a554a3aa40ca8542928494ef161a1f79f2df"
