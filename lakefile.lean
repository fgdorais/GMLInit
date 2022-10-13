import Lake
open Lake DSL

package GMLInit {
  moreLeanArgs := #["-Dlinter.unusedVariables=false"]
}

@[defaultTarget]
lean_lib GMLInit {}

require std from git "https://github.com/leanprover/std4.git"@"66b5f95c7f8632823a2d8fd57c54e3c02dead2df"
