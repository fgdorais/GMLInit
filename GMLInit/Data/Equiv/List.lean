import GMLInit.Data.Equiv.Basic

namespace List
variable {α β : Type _}

def equiv (e : Equiv α β) : Equiv (List α) (List β) where
  fwd := List.map e.fwd
  rev := List.map e.rev
  spec := by
    intros
    constr
    · intro h; rw [←h, map_map, e.comp_rev_fwd, map_id]
    · intro h; rw [←h, map_map, e.comp_fwd_rev, map_id]

end List