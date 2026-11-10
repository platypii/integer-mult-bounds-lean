module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTargetCorePacked
public import IntegerMultBounds.NLogN.PhaseCellHaloBoundary

/-! Assemble different computed fields on the manuscript's disjoint source
cores. Their actual packed crops concatenate without sorting or padding. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.TargetCoreAssembly
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.PhaseCellTargetCoreOwnership
noncomputable section
variable {s t L Q : ℕ} [NeZero s]

noncomputable def owner (ht : 0 < t) (hQ : Q*L = t) (i : ZMod s) : Fin Q :=
  let h := partition s t L Q ht hQ i.val i.val_lt
  ⟨h.choose,h.choose_spec.1.1⟩

theorem owner_spec (ht : 0 < t) (hQ : Q*L = t) (i : ZMod s) :
    cut s t L (owner ht hQ i).val ≤ i.val ∧ i.val < cut s t L ((owner ht hQ i).val+1) :=
  (partition s t L Q ht hQ i.val i.val_lt).choose_spec.1.2

theorem owner_eq (ht : 0 < t) (hQ : Q*L = t) (i : ZMod s) {k : ℕ}
    (hi : cut s t L k ≤ i.val ∧ i.val < cut s t L (k+1)) :
    (owner ht hQ i).val = k := owns_unique s t L i.val _ k (owner_spec ht hQ i) hi

def assemble {E : Type} (ht : 0 < t) (hQ : Q*L = t) (D : ℕ → ZMod s → E) (i : ZMod s) : E :=
  D (owner ht hQ i).val i

theorem assemble_on {E : Type} (ht : 0 < t) (hQ : Q*L = t) (D : ℕ → ZMod s → E)
    (i : ZMod s) {k : ℕ} (hi : cut s t L k ≤ i.val ∧ i.val < cut s t L (k+1)) :
    assemble ht hQ D i = D k i := by rw [assemble,owner_eq ht hQ i hi]

/-- A pointwise invariant on each core holds everywhere on the assembled field.
Use this once for accuracy and for the unit bound, independently of core count. -/
theorem assemble_property {E : Type} (ht : 0 < t) (hQ : Q*L = t) (D : ℕ → ZMod s → E)
    (P : E → ZMod s → Prop)
    (hD : ∀ k < Q, ∀ i ∈ haloVertices s (cut s t L k) (cut s t L (k+1)), P (D k i) i) :
    ∀ i, P (assemble ht hQ D i) i := by
  intro i
  exact hD _ (owner ht hQ i).isLt i ((mem_haloVertices _ _ i).mpr (owner_spec ht hQ i))

theorem packedInterval_assemble (ht : 0 < t) (hQ : Q*L = t) (D : ℕ → ZMod s → GaussianInt)
    {k : ℕ} (hk : k < Q) :
    packedInterval (cut s t L k) (rows s t L k) (assemble ht hQ D) =
      packedInterval (cut s t L k) (rows s t L k) (D k) := by
  have hrows : cut s t L k+rows s t L k = cut s t L (k+1) := by
    have hm := cut_mono s t L (show k ≤ k+1 by omega)
    unfold rows
    omega
  have hend : cut s t L (k+1) ≤ s := by
    have hm := cut_mono s t L (show k+1 ≤ Q by omega)
    rw [cut_last s t L Q ht hQ] at hm
    exact hm
  apply packedInterval_congr _ _ (by omega)
  intro j hj
  apply assemble_on
  have hv : (((cut s t L k+j : ℕ) : ZMod s)).val = cut s t L k+j := by
    rw [ZMod.val_natCast,Nat.mod_eq_of_lt (by omega : cut s t L k+j < s)]
  rw [hv]
  constructor <;> omega

theorem packed_concat (ht : 0 < t) (hQ : Q*L = t) (D : ℕ → ZMod s → GaussianInt) :
    (List.range Q).flatMap (fun k => packedInterval (cut s t L k) (rows s t L k) (D k)) =
      chirpLine s (assemble ht hQ D) := by
  rw [←targetCorePacked_concat (assemble ht hQ D) ht hQ]
  apply List.flatMap_congr
  intro k hk
  exact (packedInterval_assemble ht hQ D (List.mem_range.mp hk)).symm

theorem cstream_concat (A w : ℕ) (ht : 0 < t) (hQ : Q*L = t) (D : ℕ → ZMod s → GaussianInt) :
    (List.range Q).flatMap (fun k => cstream A w (packedInterval (cut s t L k) (rows s t L k) (D k))) =
      cstream A w (chirpLine s (assemble ht hQ D)) := by
  rw [←packed_concat ht hQ D]
  simp only [cstream,List.flatMap_assoc]

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.TargetCoreAssembly
