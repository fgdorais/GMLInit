import GMLInit.Meta.Basic
import GMLInit.Logic.Function

namespace Meta
open Lean.Parser.Tactic

syntax "injectivity" (term)? (location)? : tactic

macro_rules
| `(tactic|injectivity $f) => `(tactic|apply Function.injection $f)
| `(tactic|injectivity at $hs:ident*) => `(tactic|rw [Function.injectionEq] at $hs:ident*)
| `(tactic|injectivity $f at $hs:ident*) => `(tactic|rw [Function.injectionEq $f] at $hs:ident*)
| `(tactic|injectivity $f at $hs:ident* ⊢) => `(tactic|injectivity $f at $hs:ident*; injectivity $f)

end Meta
