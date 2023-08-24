import GMLInit.Meta.Prelude
import GMLInit.Logic.Cast
import GMLInit.Logic.HEq
import Lean

open Lean
open Lean.Meta
open Lean.Parser.Tactic (location)
open Lean.Elab
open Lean.Elab.Tactic (Location expandLocation joinLocation)

namespace Meta

syntax termOrHole := term <|> hole <|> syntheticHole

syntax termList := "[" (term <|> hole <|> syntheticHole),* ("|" (term <|> hole <|> syntheticHole))? "]"

macro mods:declModifiers "lemma" n:declId sig:declSig val:declVal : command =>
  `($mods:declModifiers theorem $n $sig $val)

syntax (name := clean) "clean " (colGt tactic)? (colGe location)? : tactic
macro_rules
| `(tactic| clean $[$loc:location]?) =>
  `(tactic| simp only [clean] $[$loc]?)
| `(tactic| clean $tac $[$loc:location]?) => do
  let mut loc : Location := match loc with
  | some loc => expandLocation loc
  | none => .targets #[] false
  for stx in Lean.Syntax.filter tac fun stx => stx.getKind == ``location do
    loc := joinLocation loc (expandLocation stx)
  match loc with
  | .wildcard =>
    `(tactic| $tac; simp only [clean] at *)
  | .targets hs true =>
    let locs := hs.map Lean.TSyntax.mk
    `(tactic| $tac; simp only [clean] at $[$locs]* ⊢)
  | .targets hs false =>
    let locs := hs.map Lean.TSyntax.mk
    `(tactic| $tac; simp only [clean] at $[$locs]*)

syntax "elim_casts" (location)? : tactic
set_option hygiene false in macro_rules
| `(tactic| elim_casts $[$loc]?) =>
  `(tactic| first | rw [←heq_iff_eq] $[$loc]?; simp only [elim_casts] $[$loc]?; rw [heq_iff_eq] $[$loc]? | simp only [elim_casts] $[$loc]?)

-- macro "exfalso" : tactic => `(tactic| apply False.elim)

-- macro "absurd " h:term : tactic => `(tactic| first | apply absurd _ $h | apply absurd $h)

-- def Tactic.constructor (mvarId : MVarId) : MetaM (List MVarId) := do
--   mvarId.withContext do
--     mvarId.checkNotAssigned `constructor
--     let target ← mvarId.getType'
--     matchConstStruct target.getAppFn
--       (fun _ => throwTacticEx `constructor mvarId "target is not an inductive datatype with one constructor")
--       fun _ us cval => do
--         let ctor := mkAppN (Lean.mkConst cval.name us) target.getAppArgs[:cval.numParams]
--         let ctorType ← inferType ctor
--         let (mvars, _, _) ← forallMetaTelescopeReducing ctorType (some cval.numFields)
--         mvarId.apply <| mkAppN ctor mvars

-- elab "constructor" : tactic => Tactic.withMainContext do
--   let gs ← Tactic.constructor (← Tactic.getMainGoal)
--   Term.synthesizeSyntheticMVarsNoPostponing
--   Tactic.replaceMainGoal gs

def Tactic.left (mvarId : MVarId) : MetaM (List MVarId) := do
  mvarId.withContext do
    mvarId.checkNotAssigned `left
    let target ← mvarId.getType'
    matchConstInduct target.getAppFn
      (fun _ => throwTacticEx `left mvarId "target is not an inductive datatype")
      fun ival us => do
        match ival.ctors with
        | [ctor,_] => mvarId.apply (mkConst ctor us)
        | _ => throwTacticEx `left mvarId "target is not an inductive datatype with two constructors"

elab "left" : tactic => Tactic.withMainContext do
  let gs ← Tactic.left (← Tactic.getMainGoal)
  Term.synthesizeSyntheticMVarsNoPostponing
  Tactic.replaceMainGoal gs

def Tactic.right (mvarId : MVarId) : MetaM (List MVarId) := do
  mvarId.withContext do
    mvarId.checkNotAssigned `right
    let target ← mvarId.getType'
    matchConstInduct target.getAppFn
      (fun _ => throwTacticEx `right mvarId "target is not an inductive datatype")
      fun ival us => do
        match ival.ctors with
        | [_,ctor] => mvarId.apply (mkConst ctor us)
        | _ => throwTacticEx `right mvarId "target is not an inductive datatype with two constructors"

elab "right" : tactic => Tactic.withMainContext do
  let gs ← Tactic.right (← Tactic.getMainGoal)
  Term.synthesizeSyntheticMVarsNoPostponing
  Tactic.replaceMainGoal gs

end Meta
