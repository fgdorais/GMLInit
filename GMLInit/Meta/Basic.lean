import GMLInit.Prelude
import GMLInit.Logic.Cast
import GMLInit.Logic.Congr
import GMLInit.Logic.HEq
import Lean

open Lean
open Lean.Meta
open Lean.Elab
open Lean.Parser.Tactic (location)

namespace Meta

syntax termOrHole := term <|> hole <|> syntheticHole

syntax termList := "[" termOrHole,* ("|" termOrHole)? "]"

macro mods:declModifiers "lemma" n:declId sig:declSig val:declVal : command =>
  `($mods:declModifiers theorem $n $sig $val)

syntax "clean " (location)? : tactic
set_option hygiene false in macro_rules
| `(tactic| clean $[$loc]?) =>
  `(tactic| simp only [clean] $[$loc]?)

syntax "unfold " withPosition((colGe ident)+) (location)? : tactic
macro_rules
| `(tactic| unfold $ids* $[$loc]?) =>
  `(tactic| simp only [$[$ids:ident],*] $[$loc]?)

syntax "elim_casts" (location)? : tactic
set_option hygiene false in macro_rules
| `(tactic| elim_casts $[$loc]?) =>
  `(tactic| first | rw [←heq_iff_eq] $[$loc]?; simp only [elim_casts] $[$loc]?; rw [heq_iff_eq] $[$loc]? | simp only [elim_casts] $[$loc]?)

macro "exfalso" : tactic => `(tactic| apply False.elim)

macro "absurd " h:term : tactic => `(tactic| first | apply absurd _ $h | apply absurd $h)

syntax "whnf" (&"lhs" <|> &"rhs")? (location)? : tactic
macro_rules
| `(tactic| whnf $[at $h:ident]?) =>
  `(tactic| conv $[at $h]? => whnf)
| `(tactic| whnf lhs $[at $h:ident]?) =>
  `(tactic| conv $[at $h]? => {lhs; whnf})
| `(tactic| whnf rhs $[at $h:ident]?) =>
  `(tactic| conv $[at $h]? => {rhs; whnf})

def Tactic.constr (mvarId : MVarId) : MetaM (List MVarId) := do
  withMVarContext mvarId do
    checkNotAssigned mvarId `constr
    let target ← getMVarType' mvarId
    matchConstStruct target.getAppFn
      (fun _ => throwTacticEx `constr mvarId "target is not an inductive datatype with one constructor")
      fun ival us cval => do
        let ctor := mkAppN (Lean.mkConst cval.name us) target.getAppArgs[:cval.numParams]
        let ctorType ← inferType ctor
        let (mvars, _, _) ← forallMetaTelescopeReducing ctorType (some cval.numFields)
        apply mvarId <| mkAppN ctor mvars

elab "constr" : tactic => Tactic.withMainContext do
  let gs ← Tactic.constr (← Tactic.getMainGoal)
  Term.synthesizeSyntheticMVarsNoPostponing
  Tactic.replaceMainGoal gs

def Tactic.left (mvarId : MVarId) : MetaM (List MVarId) := do
  withMVarContext mvarId do
    checkNotAssigned mvarId `left
    let target ← getMVarType' mvarId
    matchConstInduct target.getAppFn
      (fun _ => throwTacticEx `left mvarId "target is not an inductive datatype")
      fun ival us => do
        match ival.ctors with
        | [ctor,_] => apply mvarId (mkConst ctor us)
        | _ => throwTacticEx `left mvarId "target is not an inductive datatype with two constructors"

elab "left" : tactic => Tactic.withMainContext do
  let gs ← Tactic.left (← Tactic.getMainGoal)
  Term.synthesizeSyntheticMVarsNoPostponing
  Tactic.replaceMainGoal gs

def Tactic.right (mvarId : MVarId) : MetaM (List MVarId) := do
  withMVarContext mvarId do
    checkNotAssigned mvarId `right
    let target ← getMVarType' mvarId
    matchConstInduct target.getAppFn
      (fun _ => throwTacticEx `right mvarId "target is not an inductive datatype")
      fun ival us => do
        match ival.ctors with
        | [_,ctor] => apply mvarId (mkConst ctor us)
        | _ => throwTacticEx `right mvarId "target is not an inductive datatype with two constructors"

elab "right" : tactic => Tactic.withMainContext do
  let gs ← Tactic.right (← Tactic.getMainGoal)
  Term.synthesizeSyntheticMVarsNoPostponing
  Tactic.replaceMainGoal gs

end Meta
