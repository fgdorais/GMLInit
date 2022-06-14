import Lake
open Lake DSL

package GMLInit {
  moreLeanArgs := #["-Dlinter.unusedVariables=false"]
}

@[defaultTarget]
lean_lib GMLInit {}
