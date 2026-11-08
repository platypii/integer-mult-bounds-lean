module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicReplicaBoundaryRows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaResidualSharpBound
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicReplicaProblems
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRealCouplingField

/-! Actual cached residual certificates imply the shared solver's row bounds.
No additional residual-row magnitude or realness supplier is required. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

theorem cyclicReplicaBoundaryRow_bound {s : ℕ} [NeZero s] (t band a n q e : ℕ)
    (C D : ZMod s → GaussianInt)
    (hC : ∀ i, ‖value q (C i)‖ ≤ (2 : ℝ)^e)
    (hD : ∀ i, ‖value q (D i)‖ ≤ (2 : ℝ)^e) :
    ∀ z ∈ cyclicReplicaBoundaryRow t band a n C D,
      |gv q z.re| ≤ (2 : ℝ)^e ∧ |gv q z.im| ≤ (2 : ℝ)^e := by
  intro z hz
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hz
  have hnorm : ‖value q (realPartWord
      (if i ∈ haloVertices s a (a+min n (s-a)) then C i else D i))‖ ≤ (2 : ℝ)^e := by
    rw [value_realPartWord_norm]
    apply (Complex.abs_re_le_norm _).trans
    split <;> first | exact hC i | exact hD i
  exact ⟨by simpa only [value,gv] using (Complex.abs_re_le_norm _).trans hnorm,
    by simpa only [value,gv] using (Complex.abs_im_le_norm _).trans hnorm⟩

theorem cyclicReplicaBoundaryRows_format {s t p u l : ℕ} [NeZero s] {α d : ℝ}
    (axis : RecoveryAxisBounds s t p u l α d)
    (target rhsExp a n : ℕ) (ha : a < s) (hn : n ≤ s)
    (Fs : List (ZMod s → GaussianInt))
    (hF : ∀ F ∈ Fs, ∀ k,
      ‖value (executionPrecision p l target rhsExp) (F k)‖ ≤ (2 : ℝ)^rhsExp)
    (Cs Ds : List (ZMod s → GaussianInt))
    (hCs : Cs.length = Fs.length) (hDs : Ds.length = Fs.length)
    (hC : ∀ j : Fin Cs.length, ReplicaCouplingResidualSpec
      (axis.cyclicLeftReplicaProblem target rhsExp a n ha Fs hF)
      (Fs.length-1-j.val) (Cs[j.val]'j.isLt))
    (hD : ∀ j : Fin Ds.length, ReplicaCouplingResidualSpec
      (axis.cyclicRightReplicaProblem target rhsExp a n hn Fs hF)
      (Fs.length-1-j.val) (Ds[j.val]'j.isLt)) :
    let rows := (Cs.zip Ds).map (fun z => cyclicReplicaBoundaryRow t (PhaseCellBand.width p u) a n z.1 z.2)
    rows.length = Fs.length ∧
    (∀ b ∈ rows, b.length = (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card) ∧
    (∀ b ∈ rows, ∀ z ∈ b, z.im = 0) ∧
    (∀ b ∈ rows, ∀ z ∈ b,
      |gv (executionPrecision p l target rhsExp) z.re| ≤
        (2 : ℝ)^couplingRowExponent rhsExp (stableInteriorExponent p rhsExp) (8*p+1) (couplingCountExponent p u) ∧
      |gv (executionPrecision p l target rhsExp) z.im| ≤
        (2 : ℝ)^couplingRowExponent rhsExp (stableInteriorExponent p rhsExp) (8*p+1) (couplingCountExponent p u)) := by
  dsimp only
  refine ⟨by simp [hCs,hDs],?_,?_,?_⟩
  · intro b hb
    obtain ⟨z,_,rfl⟩ := List.mem_map.mp hb
    exact cyclicReplicaBoundaryRow_length _ _ _ _ _ _
  · intro b hb
    obtain ⟨z,_,rfl⟩ := List.mem_map.mp hb
    exact cyclicReplicaBoundaryRow_real _ _ _ _ _ _
  · intro b hb
    obtain ⟨⟨C,D⟩,hpair,rfl⟩ := List.mem_map.mp hb
    obtain ⟨hCmem,hDmem⟩ := List.of_mem_zip hpair
    have hCnorm := replicaCouplingResiduals_sharp_norm
      (axis.cyclicLeftReplicaProblem target rhsExp a n ha Fs hF) Cs hCs hC C hCmem
    have hDnorm := replicaCouplingResiduals_sharp_norm
      (axis.cyclicRightReplicaProblem target rhsExp a n hn Fs hF) Ds hDs hD D hDmem
    exact cyclicReplicaBoundaryRow_bound t (PhaseCellBand.width p u) a n
      (executionPrecision p l target rhsExp) _ C D hCnorm hDnorm

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
