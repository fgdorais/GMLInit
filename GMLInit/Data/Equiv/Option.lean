import GMLInit.Data.Equiv.Basic

namespace Option

def equiv {α β} (e : Equiv α β) : Equiv (Option α) (Option β) where
  fwd
  | some x => some (e.fwd x)
  | none => none
  rev
  | some x => some (e.rev x)
  | none => none
  fwd_eq_iff_rev_eq := by
    intro
    | some _, some _ =>
      constr
      · intro | rfl => clean; rw [e.rev_fwd]
      · intro | rfl => clean; rw [e.fwd_rev]
    | some _, none => constr <;> (intro h; cases h)
    | none, some _ => constr <;> (intro h; cases h)
    | none, none => constr <;> intro | rfl => rfl

end Option
