import GMLInit.Meta.Basic
import GMLInit.Logic.Function

namespace Meta
open Lean.Parser.Tactic (location)

syntax "injectivity " (term:max)? (location)? : tactic

macro_rules
| `(tactic| injectivity $f) => `(tactic| apply Function.inj $f)
| `(tactic| injectivity at $hs:ident*) => `(tactic| rw [Function.inj_eq] at $hs:ident*)
| `(tactic| injectivity $f at $hs:ident*) => `(tactic| rw [Function.inj_eq $f] at $hs:ident*)
| `(tactic| injectivity $f at $hs:ident* ⊢) => `(tactic| injectivity $f at $hs:ident*; injectivity $f)

end Meta
