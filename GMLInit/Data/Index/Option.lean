import GMLInit.Data.Index.Basic
import GMLInit.Data.Index.Map

protected abbrev List.option {α} (xs : List α) : List (Option α) := none :: xs.map some

namespace Index
variable {α} {xs : List α}

def option : Option (Index xs) → Index xs.option
| none => head
| some i => tail (i.map some)

def unoption (k : Index xs.option) : Option (Index xs) :=
  match k with
  | head => none
  | tail i => i.unmap some

theorem unoption_option : (i : Option (Index xs)) → unoption (option i) = i
| none => rfl
| some i => congrArg some (unmap_map some i)

theorem option_unoption : (k : Index (List.option xs)) → option (unoption k) = k
| head => rfl
| tail k => congrArg tail (map_unmap some k)

theorem option_eq_iff_eq_unoption (i : Option (Index xs)) (k : Index (List.option xs)) : option i = k ↔ i = unoption k := by
  constr
  · intro h; cases h; rw [unoption_option]
  · intro h; cases h; rw [option_unoption]

theorem unoption_eq_iff_eq_option (k : Index (List.option xs)) (i : Option (Index xs)) : unoption k = i ↔ k = option i := by
  constr
  · intro h; cases h; rw [option_unoption]
  · intro h; cases h; rw [unoption_option]

def optionEquiv (xs : List α) : Equiv (Option (Index xs)) (Index (List.option xs)) where
  fwd := option
  rev := unoption
  spec := by
    intros
    constr
    · intro | rfl => exact unoption_option ..
    · intro | rfl => exact option_unoption ..

theorem val_option (i : Option (Index xs)) : (match i with | none => none | some i => some i.val) = (option i).val := by
  match i with
  | none => rfl
  | some i => unfold option; rw [val_map]

theorem val_unoption (k : Index (List.option xs)) : k.val = (match k.unoption with | none => none | some k => some k.val) := by
  rw [←option_unoption k, val_option, unoption_option]

end Index
