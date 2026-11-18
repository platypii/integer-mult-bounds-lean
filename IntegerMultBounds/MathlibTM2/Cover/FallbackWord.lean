module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackResidual

/-! Undo fallback elimination using only forward shears and exchanges of two fields. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback

open Matrix GoodForm
variable {n : ℕ} {R : Type*} [CommRing R]

inductive RowOp (n : ℕ) (R : Type*)
  | shear (i j : Fin n) (h : i < j) (c : R)
  | swap (i j : Fin n)

def RowOp.apply : RowOp n R → (Fin n → R) → (Fin n → R)
  | .shear i j _ c, x => Function.update x j (x j + c * x i)
  | .swap i j, x => x ∘ Equiv.swap i j

def RowOp.children : RowOp n R → ℕ
  | .shear .. => 0
  | .swap .. => 3

private theorem add_apply (i k : Fin n) (c : R) (x : Fin n → R) :
    (1 + colMat k (Pi.single i c)) *ᵥ x = Function.update x i (x i + c * x k) := by
  ext j
  rw [add_mulVec,one_mulVec]
  by_cases h : j = i <;> simp [h,colMat,mulVec,dotProduct,ite_mul,Pi.single_apply]

private theorem swap_apply (i j : Fin n) (x : Fin n → R) :
    swapMat i j *ᵥ x = x ∘ Equiv.swap i j := by
  ext k
  simp [mulVec,dotProduct,swapMat,ite_mul]

private theorem undo_add (i k : Fin n) (hik : i ≠ k) (c : R) :
    ∃ w : List (RowOp n R), (w.map RowOp.children).sum ≤ 6 ∧
      ∀ x, w.foldl (fun y op => op.apply y) ((1 + colMat k (Pi.single i c)) *ᵥ x) = x := by
  have hki := hik.symm
  rcases lt_or_gt_of_ne hik with h | h
  · refine ⟨[.swap i k,.shear i k h (-c),.swap i k],by simp [RowOp.children],?_⟩
    intro x
    rw [add_apply]
    ext j
    by_cases hi : j = i <;> by_cases hk : j = k <;>
      simp_all [RowOp.apply,Function.comp_def,Equiv.swap_apply_of_ne_of_ne,add_assoc]
  · refine ⟨[.shear k i h (-c)],by simp [RowOp.children],?_⟩
    intro x
    rw [add_apply]
    ext j
    by_cases hi : j = i <;> simp_all [RowOp.apply,add_assoc]

/-- Starting from the diagonalized output, undo the most recent row operation first. -/
theorem Elim.undo_word {a s : ℕ} {E : Matrix (Fin n) (Fin n) R} (h : Elim a s E) :
    ∃ w : List (RowOp n R), (w.map RowOp.children).sum ≤ 6*a + 3*s ∧
      ∀ x, w.foldl (fun y op => op.apply y) (E *ᵥ x) = x := by
  induction h with
  | one => exact ⟨[],by simp,by simp⟩
  | add i k c hik _ ih =>
    obtain ⟨v,hv,undo⟩ := ih
    obtain ⟨u,hu,step⟩ := undo_add i k hik c
    exact ⟨u ++ v,by simp; omega,by simp [List.foldl_append,← mulVec_mulVec,step,undo]⟩
  | swap i j _ ih =>
    obtain ⟨v,hv,undo⟩ := ih
    refine ⟨.swap i j :: v,by simp [RowOp.children]; omega,?_⟩
    intro x
    rw [← mulVec_mulVec,swap_apply,List.foldl_cons]
    convert undo x using 2
    funext j'
    simp [RowOp.apply,Function.comp_def]

/-- Apply the diagonal first, then undo elimination. The bound includes the
six children for each of the non-anchor diagonal pairs. -/
theorem fallback_word {m : ℕ} (hm : 1 ≤ m) {E G D : Matrix (Fin (2*m)) (Fin (2*m)) R}
    (hE : Elim ((2*m)*(2*m-1)) (2*m) E) (hD : E * G = D) :
    ∃ w : List (RowOp (2*m) R), (w.map RowOp.children).sum + 6*(2*m-1) < 32*m^2 ∧
      ∀ x, w.foldl (fun y op => op.apply y) (D *ᵥ x) = G *ᵥ x := by
  obtain ⟨w,h,undo⟩ := hE.undo_word
  refine ⟨w,lt_of_le_of_lt (Nat.add_le_add_right h _) (Weighted.fallback_children m hm),?_⟩
  intro x
  rw [← hD,← mulVec_mulVec,undo]

/-- For each listed coordinate, scale it and the anchor by reciprocal units.
The empty product leaves every coordinate alone. -/
def applyPairs (d : Fin n → Rˣ) (l : List (Fin n)) (x : Fin (n+1) → R) :=
  l.foldl (fun y i j => (pair i (d i) j : R) * y j) x

theorem applyPairs_eq (d : Fin n → Rˣ) (l : List (Fin n)) (x : Fin (n+1) → R)
    (j : Fin (n+1)) : applyPairs d l x j = ((l.map (fun i => (pair i (d i) j : R))).prod) * x j := by
  induction l generalizing x with
  | nil => simp [applyPairs]
  | cons i l ih =>
    simp only [applyPairs,List.foldl_cons,List.map_cons,List.prod_cons]
    rw [← applyPairs,ih]
    ring

/-- The whole fallback on a nonempty pair of fields: apply the anchor sign, run
the reciprocal pairs, then undo elimination. The same word works for every input. -/
theorem residual_word {ι : Type*} [Fintype ι] [DecidableEq ι] {q w m : ℕ} [Fact q.Prime]
    (hodd : 2 < q) (hw : 0 < w) (dim : n+1 = 2*m) (e : (ι ⊕ ι) ≃ Fin (n+1))
    (A A' C P : Matrix ι ι (ZMod (q ^ w))) (hA : A * A' = 1) (hA' : A' * A = 1)
    (hC : C * C = 1) (hP : P * P = P) :
    ∃ (s : (ZMod (q^w))ˣ) (d : Fin n → (ZMod (q^w))ˣ) (ops : List (RowOp (n+1) (ZMod (q^w)))),
      (s = 1 ∨ s = -1) ∧ (ops.map RowOp.children).sum + 2*n < 24*m^2 ∧
      ∀ x, ops.foldl (fun y op => op.apply y)
        (applyPairs d (List.finRange n) (fun j => ↑((Fin.cons s (fun _ => 1) : Fin (n+1) → (ZMod (q^w))ˣ) j) * x j)) =
          reindex e e (residual A A' C P) *ᵥ x := by
  obtain ⟨E,d,s,hE,hs,hD⟩ := residual_pairs hodd hw e A A' C P hA hA' hC hP
  obtain ⟨ops,hops,undo⟩ := hE.undo_word
  refine ⟨s,d,ops,hs,?_,?_⟩
  · have : 6*((n+1)*n) + 3*(n+1) + 2*n < 24*m^2 := by nlinarith [congrArg (fun t : ℕ => t*t) dim]
    omega
  · intro x
    rw [← undo (reindex e e (residual A A' C P) *ᵥ x),mulVec_mulVec,hD]
    congr 1
    ext j
    simp [applyPairs_eq,mulVec_diagonal,Finset.prod_apply,Units.coe_prod,
      List.prod_ofFn,← List.ofFn_eq_map, mul_left_comm,mul_assoc]

end IntegerMultBounds.MathlibTM2.Cover.Fallback
