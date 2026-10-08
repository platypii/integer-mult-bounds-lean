import IntegerMultBounds.Machine.FlatCoordinateLayout

/-! One- and two-digit decompositions of the actual most-significant-first
coordinate encoding. These are arithmetic identities for the existing word;
they do not postulate a rearrangement or perform an uncharged tape operation. -/
namespace IntegerMultBounds.Machine.RecursiveCoordinateDigits
noncomputable section
open FlatCoordinateLayout
variable {m Q : ℕ} [NeZero Q]

def preDigits (x : Fin m → ZMod Q) (i : Fin m) : Fin (Q^i.val) :=
  ⟨prefixIndex x i,prefix_lt x i⟩

def suffix (x : Fin m → ZMod Q) (i : Fin m) : Fin (Q^(m-1-i.val)) :=
  ⟨(rank x).val%Q^(m-1-i.val),Nat.mod_lt _ (pow_pos (NeZero.pos Q) _)⟩

theorem one (x : Fin m → ZMod Q) (i : Fin m) :
    (rank x).val = (preDigits x i).val*Q*Q^(m-1-i.val)+(x i).val*Q^(m-1-i.val)+(suffix x i).val := by
  have hh := index_split x i (0 : Fin 1)
  simpa only [index_val,Fin.val_zero,Nat.mul_one,Nat.add_zero,preDigits,suffix,
    suffixSize,FlatCoordinateLayout.suffix,suffixFields,Nat.mul_assoc] using hh

/-- The portion strictly between an earlier control and the target. -/
def middle (x : Fin m → ZMod Q) (j i : Fin m) : Fin (Q^(i.val-j.val-1)) :=
  ⟨(preDigits x i).val%Q^(i.val-j.val-1),Nat.mod_lt _ (pow_pos (NeZero.pos Q) _)⟩

omit [NeZero Q] in
private theorem split_power (j i : Fin m) (hj : j < i) :
    Q^i.val = Q^j.val*(Q*Q^(i.val-j.val-1)) := by
  rw [← pow_succ',← pow_add]
  congr 1
  change j.val < i.val at hj
  omega

def pairPrefix (x : Fin m → ZMod Q) (j i : Fin m) (hj : j < i) : Fin (Q^j.val) :=
  ⟨(preDigits x i).val/(Q*Q^(i.val-j.val-1)),by
    apply (Nat.div_lt_iff_lt_mul (Nat.mul_pos (NeZero.pos Q) (pow_pos (NeZero.pos Q) _))).2
    rw [← split_power j i hj]
    exact (preDigits x i).isLt⟩

/-- The prefix of the target consists of the prefix of the control, the
control itself, and the intervening digit block. -/
theorem pair_prefix (x : Fin m → ZMod Q) (j i : Fin m) (hj : j < i) :
    (preDigits x i).val = ((pairPrefix x j i hj).val*Q+(x j).val)*Q^(i.val-j.val-1)+(middle x j i).val := by
  have h₁ := Nat.mod_add_div (preDigits x i).val (Q^(i.val-j.val-1))
  have h₂ := Nat.mod_add_div ((preDigits x i).val/Q^(i.val-j.val-1)) Q
  have hc : ((preDigits x i).val/Q^(i.val-j.val-1))%Q = (x j).val := by
    have he : i.val-j.val-1 = i.val-1-j.val := by omega
    simpa only [preDigits,he] using earlier_control x i j hj
  rw [hc] at h₂
  have hd : ((preDigits x i).val/Q^(i.val-j.val-1))/Q = (pairPrefix x j i hj).val := by
    rw [Nat.div_div_eq_div_mul]
    simp only [pairPrefix,Nat.mul_comm]
  rw [hd] at h₂
  dsimp only [middle]
  rw [← h₂] at h₁
  nlinarith only [h₁]

/-- Exact five-block decomposition exposing the earlier control and target. -/
theorem pair (x : Fin m → ZMod Q) (j i : Fin m) (hj : j < i) :
    (rank x).val = ((((pairPrefix x j i hj).val*Q+(x j).val)*Q^(i.val-j.val-1)+
      (middle x j i).val)*Q+(x i).val)*Q^(m-1-i.val)+(suffix x i).val := by
  rw [one x i,pair_prefix x j i hj]
  ring

/-- Updating a selected digit leaves both surrounding blocks literal. -/
theorem one_update (x : Fin m → ZMod Q) (i : Fin m) (z : ZMod Q) :
    (rank (Function.update x i z)).val = ((preDigits x i).val*Q+z.val)*Q^(m-1-i.val)+(suffix x i).val := by
  have hu := rank_update_balance x i z
  have hd := one x i
  simp only [suffixFields] at hu
  nlinarith

/-- Updating the target preserves the original earlier control and middle. -/
theorem pair_update (x : Fin m → ZMod Q) (j i : Fin m) (hj : j < i) (z : ZMod Q) :
    (rank (Function.update x i z)).val = ((((pairPrefix x j i hj).val*Q+(x j).val)*Q^(i.val-j.val-1)+
      (middle x j i).val)*Q+z.val)*Q^(m-1-i.val)+(suffix x i).val := by
  rw [one_update x i z,pair_prefix x j i hj]

end
end IntegerMultBounds.Machine.RecursiveCoordinateDigits
