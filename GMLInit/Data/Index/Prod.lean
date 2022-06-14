import GMLInit.Data.Index.Basic
import GMLInit.Data.Index.Bind
import GMLInit.Data.Index.Map

protected abbrev List.prod {α β} (xs : List α) (ys : List β) : List (α × β) := xs.bind fun x => ys.map (Prod.mk x)

namespace Index
variable {α β} {xs : List α} {ys : List β}

def prod : Index xs × Index ys → Index (List.prod xs ys)
| (i,j) => Index.bind (λ x => ys.map (Prod.mk x)) ⟨i, j.map (Prod.mk i.val)⟩

def unprod (k : Index (List.prod xs ys)) : Index xs × Index ys :=
  match unbind (λ x => ys.map (Prod.mk x)) k with
  | ⟨i,j⟩ => (i, j.unmap (Prod.mk i.val))

theorem unprod_prod (i : Index xs × Index ys) : unprod (prod i) = i := by
  rw [prod, unprod]
  clean
  rw [unbind_bind, unmap_map]

theorem prod_unprod (k : Index (List.prod xs ys)) : prod (unprod k) = k := by
  rw [prod, unprod]
  clean
  rw [map_unmap, bind_unbind]

theorem prod_eq_iff_eq_unprod (i : Index xs × Index ys) (k : Index (List.prod xs ys)) : prod i = k ↔ i = unprod k := by
  constr
  · intro h; rw [←h, unprod_prod]
  · intro h; rw [h, prod_unprod]

theorem unprod_eq_iff_eq_prod (i : Index (List.prod xs ys)) (j : Index xs × Index ys) : unprod i = j ↔ i = prod j := by
  constr
  · intro h; rw [←h, prod_unprod]
  · intro h; rw [h, unprod_prod]

def prodEquiv (xs ys : List α) : Equiv (Index xs × Index ys) (Index (List.prod xs ys)) where
  fwd := prod
  rev := unprod
  spec := by
    intros
    constr
    · intro | rfl => exact unprod_prod ..
    · intro | rfl => exact prod_unprod ..

theorem val_prod (i : Index xs × Index ys) : (prod i).val = (i.fst.val, i.snd.val) := by
  rw [prod, val_bind, val_map]

theorem val_unprod (i : Index (List.prod xs ys)) : ((unprod i).fst.val, (unprod i).snd.val) = i.val := by
  rw [←prod_unprod i, val_prod, unprod_prod]

end Index
