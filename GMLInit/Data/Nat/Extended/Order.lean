import GMLInit.Data.Nat.Extended.Basic

namespace ENat

protected def le (x y : ENat) : Prop := ∀ n, x.isLE n || !y.isLE n
instance : LE ENat := ⟨ENat.le⟩

protected def lt (x y : ENat) : Prop := ∃ n, x.isLE n && !y.isLE n
instance : LT ENat := ⟨ENat.lt⟩

theorem zero_le (x : ENat) : 0 ≤ x := by
  intro n
  rw [isLE_zero, Bool.true_or]

theorem le_infinity (x : ENat) : x ≤ ∞ := by
  intro n
  rw [isLE_infinity, Bool.not_false, Bool.or_true]

theorem le_refl (x : ENat) : x ≤ x := by
  intro n
  cases x.isLE n <;> rfl

theorem le_trans {x y z : ENat} : x ≤ y → y ≤ z → x ≤ z := by
  intro hxy hyz n
  match hx : x.isLE n, hy : y.isLE n, hz : z.isLE n with
  | true, true, true => rfl
  | true, true, false => rfl
  | true, false, true => rfl
  | true, false, false => rfl
  | false, true, true =>
    have : false = true := by rw [←hxy n, hx, hy]; rfl
    contradiction
  | false, true, false => rfl
  | false, false, true =>
    have : false = true := by rw [←hyz n, hy, hz]; rfl
    contradiction
  | false, false, false => rfl

theorem le_antisymm {x y : ENat} : x ≤ y → y ≤ x → x = y := by
  intro hxy hyx
  apply ENat.ext
  intro n
  match hx : x.isLE n, hy : y.isLE n with
  | true, true => rfl
  | true, false =>
    have : false = true := by rw [←hyx n, hx, hy]; rfl
    contradiction
  | false, true =>
    have : false = true := by rw [←hxy n, hx, hy]; rfl
    contradiction
  | false, false => rfl

theorem le_of_eq {x y : ENat} : x = y → x ≤ y | rfl => le_refl _

theorem le_of_lt {x y : ENat} : x < y → x ≤ y
| ⟨n₀,h₀⟩ => by
  rw [Bool.and_eq_true] at h₀
  intro n
  cases Nat.le_total n n₀ with
  | inl hle =>
    have : y.isLE n = false := by
      rw [←Bool.not_eq_true]
      intro hy
      have : y.isLE n₀ = true := by
        apply y.mono hle
        exact hy
      simp [this] at h₀
    rw [this, Bool.not_false, Bool.or_true]
  | inr hge =>
    have : x.isLE n = true := by
      apply x.mono hge
      exact h₀.1
    rw [this, Bool.true_or]

theorem lt_irrefl (x : ENat) : ¬ x < x := by
  intro ⟨n, hn⟩
  have : false = true := by rw [←hn]; cases x.isLE n <;> rfl
  contradiction

theorem lt_of_le_of_lt {x y z : ENat} : x ≤ y → y < z → x < z := by
  intro hxy ⟨n,h⟩
  rw [Bool.and_eq_true] at h
  have h' := hxy n
  rw [Bool.or_eq_true] at h'
  match h, h' with
  | ⟨_,hz⟩, Or.inl hx =>
    exists n
    rw [hx, hz]
    rfl
  | ⟨hy,_⟩, Or.inr hy' =>
    rw [hy] at hy'
    contradiction

theorem lt_of_lt_of_le {x y z : ENat} : x < y → y ≤ z → x < z := by
  intro ⟨n,h⟩ hyz
  rw [Bool.and_eq_true] at h
  have h' := hyz n
  rw [Bool.or_eq_true] at h'
  match h, h' with
  | ⟨_,hy⟩, Or.inl hy' =>
    rw [hy'] at hy
    contradiction
  | ⟨hx,_⟩, Or.inr hz =>
    exists n
    rw [hx, hz]
    rfl

theorem lt_trans {x y z : ENat} : x < y → y < z → x < z := by
  intro hxy hyz
  apply lt_of_lt_of_le
  · exact hxy
  · apply le_of_lt
    exact hyz

instance : Relation.Reflexive (α:=ENat) (.≤.) := ⟨ENat.le_refl⟩

instance : Relation.Irreflexive (α:=ENat) (.<.) := ⟨ENat.lt_irrefl⟩

instance : Relation.Transitive (α:=ENat) (.≤.) := ⟨ENat.le_trans⟩

instance : Relation.Transitive (α:=ENat) (.<.) := ⟨ENat.lt_trans⟩

instance : Relation.HTransitive (α:=ENat) (β:=ENat) (γ:=ENat) (.≤.) (.<.) (.<.) := ⟨ENat.lt_of_le_of_lt⟩

instance : Relation.HTransitive (α:=ENat) (β:=ENat) (γ:=ENat) (.<.) (.≤.) (.<.) := ⟨ENat.lt_of_lt_of_le⟩

instance : Relation.Antisymmetric (α:=ENat) (.≤.) := ⟨ENat.le_antisymm⟩

end ENat
