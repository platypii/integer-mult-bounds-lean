module

public import IntegerMultBounds.MathlibTM2.Cover.LabelView
public import IntegerMultBounds.MathlibTM2.Cover.LabelAddress
public import IntegerMultBounds.Machine.ArbitraryWidthSliceTranspose

/-! The flat matrix address in radix `Q^m`, with one digit per column. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Cover.LabelColumns
noncomputable section

open IntegerMultBounds.Machine.FlatCoordinateLayout
open IntegerMultBounds.Machine.ArbitraryWidthSliceTranspose (rank_sum)
open IntegerMultBounds.MathlibTM2.M8.AtomOps (refine refine_at)
open LabelAddress (address)
open Route (cols)
variable {m Q : ℕ} [NeZero Q]

/-- The radix-`Q^m` digit at column `j` packs its rows most significant first. -/
def column (g : Matrix (Fin m) (Fin m) (ZMod Q)) (j : Fin m) : ZMod (Q^m) :=
  ZMod.finEquiv _ (rank (cols g j))

theorem column_val (g : Matrix (Fin m) (Fin m) (ZMod Q)) (j : Fin m) :
    (column g j).val = (rank (cols g j)).val := by
  rw [← finEquiv_symm_val, column, RingEquiv.symm_apply_apply]

theorem address_columns (g : Matrix (Fin m) (Fin m) (ZMod Q)) :
    (address g).val = (rank (column g)).val := by
  unfold address
  rw [rank_sum, rank_sum, ← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  rw [column_val, rank_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  change (refine (cols g) (IntegerMultBounds.MathlibTM2.M8.AtomOps.«at» j i)).val * _ = _
  rw [refine_at, mul_assoc, ← pow_mul, ← pow_add]
  congr 2
  simp only [finProdFinEquiv_apply_val]
  have hj : (j : ℕ) + 1 + (m-1-j.val) = m := by have := j.isLt; omega
  have hi : (i : ℕ) + 1 + (m-1-i.val) = m := by have := i.isLt; omega
  have h := congrArg (m * ·) hj
  simp only [Nat.mul_add, Nat.mul_one] at h
  omega

theorem read_column (g : Matrix (Fin m) (Fin m) (ZMod Q)) (j : Fin m) :
    (address g).val / (Q^m)^suffixFields j % (Q^m) = (rank (cols g j)).val := by
  rw [address_columns, coordinate_value, column_val]

/-- Splitting at two column boundaries yields the same five fields used by the supplier. -/
theorem rank_pair {D : ℕ} [NeZero D] (x : Fin m → ZMod D) (s t : Fin m) (hst : s < t) :
    let lp := rank (fun i : Fin s.val => x ⟨i.val, lt_trans i.isLt s.isLt⟩)
    let mid := rank (fun i : Fin (t.val-s.val-1) => x ⟨s.val+1+i.val, by
      have := i.isLt; have := t.isLt; omega⟩)
    let ls := rank (fun i : Fin (m-1-t.val) => x ⟨t.val+1+i.val, by have := i.isLt; omega⟩)
    (rank x).val = (((lp.val*D + (x s).val)*D^(t.val-s.val-1) + mid.val)*D +
      (x t).val)*D^(m-1-t.val) + ls.val := by
  let a := s.val
  let b := t.val-s.val-1
  let c := m-1-t.val
  have hs := s.isLt
  have ht := t.isLt
  have hst' : s.val < t.val := hst
  have hn : a+(1+(b+(1+c))) = m := by dsimp [a,b,c]; omega
  let pre := fun i : Fin a => x ⟨i.val, lt_trans i.isLt hs⟩
  let mid := fun i : Fin b => x ⟨a+1+i.val, by have := i.isLt; dsimp [a,b] at *; omega⟩
  let suf := fun i : Fin c => x ⟨t.val+1+i.val, by have := i.isLt; dsimp [c] at *; omega⟩
  let y : Fin (a+(1+(b+(1+c)))) → ZMod D := Fin.addCases pre (Fin.addCases (fun _ : Fin 1 => x s)
    (Fin.addCases mid (Fin.addCases (fun _ : Fin 1 => x t) suf)))
  have he : y = fun i => x (Fin.cast hn i) := by
    funext i
    unfold y
    repeat' first | induction i using Fin.addCases with | left i => _ | right i => _
    all_goals simp only [Fin.addCases_left, Fin.addCases_right, pre, mid, suf]
    all_goals apply congrArg x; apply Fin.ext
    all_goals simp only [Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd]
    all_goals have hi := i.isLt; dsimp [a,b,c] at *; omega
  have hcast {n : ℕ} (h : n = m) : (rank (fun i => x (Fin.cast h i))).val = (rank x).val := by
    subst n; rfl
  rw [← hcast hn, ← he]
  have hone (z : ZMod D) : (rank (fun _ : Fin 1 => z)).val = z.val := by simp [rank_sum]
  simp only [y, IntegerMultBounds.Machine.ArbitraryWidthSliceTranspose.rank_append, hone, pow_add, pow_one]
  dsimp only [a,b,c,pre,mid,suf]
  ring

/-- Updating two selected digits keeps the three spectator blocks of the rank. -/
theorem rank_pair_update {D : ℕ} [NeZero D] (x : Fin m → ZMod D) (s t : Fin m) (hst : s < t)
    (a b : ZMod D) :
    ∃ (lp : Fin (D^s.val)) (gap : Fin (D^(t.val-s.val-1))) (ls : Fin (D^(m-1-t.val))),
      (rank x).val = LabelView.label D 1 m s t lp (x s).val gap (x t).val ls ∧
      (rank (Function.update (Function.update x s a) t b)).val =
        LabelView.label D 1 m s t lp a.val gap b.val ls := by
  have h₁ := rank_pair x s t hst
  let y := Function.update (Function.update x s a) t b
  have h₂ := rank_pair y s t hst
  have hst' : s.val < t.val := hst
  have hfix (i : Fin m) (hi : i.val ≠ s.val) (hj : i.val ≠ t.val) : y i = x i := by
    simp [y, Function.update_of_ne (fun h => hi (congrArg Fin.val h)),
      Function.update_of_ne (fun h => hj (congrArg Fin.val h))]
  have pre (i : Fin s.val) := hfix ⟨i.val, lt_trans i.isLt s.isLt⟩
    (by exact i.isLt.ne) (by change i.val ≠ t.val; have := i.isLt; omega)
  have middle (i : Fin (t.val-s.val-1)) := hfix ⟨s.val+1+i.val, by have := i.isLt; have := t.isLt; omega⟩
    (by change s.val+1+i.val ≠ s.val; omega) (by change s.val+1+i.val ≠ t.val; have := i.isLt; omega)
  have suf (i : Fin (m-1-t.val)) := hfix ⟨t.val+1+i.val, by have := i.isLt; omega⟩
    (by change t.val+1+i.val ≠ s.val; omega) (by change t.val+1+i.val ≠ t.val; omega)
  dsimp only at h₁ h₂
  have hs : y s = a := by simp [y, Function.update_of_ne hst.ne]
  have ht : y t = b := by simp [y]
  simp only [pre, middle, suf, hs, ht] at h₂
  unfold LabelView.label
  simp only [Nat.mul_one, pow_one]
  exact ⟨_, _, _, h₁, h₂⟩

/-- A matrix and its column transposition have identical spectator fields in the label view. -/
theorem address_swap (g : Matrix (Fin m) (Fin m) (ZMod Q)) (s t : Fin m) (hst : s < t) :
    ∃ (lp : Fin ((Q^m)^s.val)) (mid : Fin ((Q^m)^(t.val-s.val-1)))
      (ls : Fin ((Q^m)^(m-1-t.val))),
      (address g).val = LabelView.label (Q^m) 1 m s t lp (column g s).val mid (column g t).val ls ∧
      (address (fun i j => g i (Equiv.swap s t j))).val =
        LabelView.label (Q^m) 1 m s t lp (column g t).val mid (column g s).val ls := by
  obtain ⟨lp, gap, ls, h₁, h₂⟩ := rank_pair_update (column g) s t hst (column g t) (column g s)
  have he : column (fun i j => g i (Equiv.swap s t j)) =
      Function.update (Function.update (column g) s (column g t)) t (column g s) := by
    funext j
    change column g (Equiv.swap s t j) = _
    by_cases hs : j = s
    · subst j; simp [Function.update_of_ne hst.ne]
    by_cases ht : j = t
    · subst j; simp
    simp [Equiv.swap_apply_of_ne_of_ne hs ht, Function.update_of_ne hs, Function.update_of_ne ht]
  refine ⟨lp, gap, ls, (address_columns g).trans h₁, ?_⟩
  rw [address_columns (fun i j => g i (Equiv.swap s t j)), he]
  exact h₂

end
end IntegerMultBounds.MathlibTM2.Cover.LabelColumns
