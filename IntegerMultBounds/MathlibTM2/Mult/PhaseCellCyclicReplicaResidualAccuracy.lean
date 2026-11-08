module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicReplicaProblems
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaCouplingResidualAccuracy
public import IntegerMultBounds.NLogN.PhaseCellCyclicResidualPieces
public import IntegerMultBounds.NLogN.PhaseCellCyclicBoundaryOrder

/-! Join the two cached replica accuracy contracts without another interior
solve or another error allowance. Archive indices retain their source order. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s t p u l : ℕ} [NeZero s] {α d : ℝ}

/-- A row selector, rather than a sum, assembles the joint cyclic residual. -/
def cyclicReplicaResidualField (a n : ℕ) (C D : ZMod s → GaussianInt) : ZMod s → GaussianInt :=
  fun i => realPartWord (if i ∈ haloVertices s a (a+min n (s-a)) then C i else D i)

/-- Stage the left row, then prepend the right row, and use the existing linear
boundary fold once. No random access to ambient-sized residuals is needed. -/
theorem cyclicReplicaResidualField_order (a n : ℕ) (ha : a < s) (hn : n ≤ s)
    (C D : ZMod s → GaussianInt) :
    (bOrder s (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n)).map
      (cyclicReplicaResidualField a n C D) =
    ((bOrder s (haloBoundary s t (PhaseCellBand.width p u) 0 (n-min n (s-a)))).map
      (fun i => realPartWord (D i))) ++
    ((bOrder s (haloBoundary s t (PhaseCellBand.width p u) a (a+min n (s-a)))).map
      (fun i => realPartWord (C i))) := by
  rw [cyclicPrincipalBoundary_order t (PhaseCellBand.width p u) a n ha hn,List.map_append]
  congr 1
  · apply List.map_congr_left
    intro i hi
    have hiB : i ∈ haloBoundary s t (PhaseCellBand.width p u) 0 (n-min n (s-a)) := by
      rw [← List.mem_toFinset,bOrder_toFinset] at hi
      exact hi
    have hnot : i ∉ haloVertices s a (a+min n (s-a)) := by
      intro hleft
      exact Finset.disjoint_left.mp (cyclicPrincipalPieces_disjoint a n ha hn)
        hleft (Finset.mem_sdiff.mp hiB).1
    simp only [cyclicReplicaResidualField,ite_eq_right hnot]
  · apply List.map_congr_left
    intro i hi
    have hiB : i ∈ haloBoundary s t (PhaseCellBand.width p u) a (a+min n (s-a)) := by
      rw [← List.mem_toFinset,bOrder_toFinset] at hi
      exact hi
    simp only [cyclicReplicaResidualField,ite_eq_left (Finset.mem_sdiff.mp hiB).1]

theorem cyclicReplicaResiduals_accurate
    (axis : RecoveryAxisBounds s t p u l α d)
    (target rhsExp a n : ℕ) (ha : a < s) (hn : n ≤ s)
    (Fs : List (ZMod s → GaussianInt))
    (hF : ∀ F ∈ Fs, ∀ k,
      ‖value (executionPrecision p l target rhsExp) (F k)‖ ≤ (2 : ℝ)^rhsExp)
    (Cs Ds : List (ZMod s → GaussianInt))
    (hCs : Cs.length = Fs.length) (hDs : Ds.length = Fs.length)
    (hleft : ReplicaCouplingResidualsAccurate
      (axis.cyclicLeftReplicaProblem target rhsExp a n ha Fs hF) Cs)
    (hright : ReplicaCouplingResidualsAccurate
      (axis.cyclicRightReplicaProblem target rhsExp a n hn Fs hF) Ds) :
    ∃ R : (ZMod s → ℝ) → ZMod s → ℝ,
      (∀ rhs, Solves (realMatrix s t p u)
        (cyclicPrincipalInterior s t (PhaseCellBand.width p u) a n) (R rhs) rhs) ∧
      ∀ j : Fin Fs.length, ∀ i ∈ cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n,
        |(value (executionPrecision p l target rhsExp)
          (cyclicReplicaResidualField a n (Cs.getD j.val (fun _ => 0))
            (Ds.getD j.val (fun _ => 0)) i)).re-
          residual (realMatrix s t p u) (cyclicPrincipalInterior s t (PhaseCellBand.width p u) a n) R
            (fun k => (value (executionPrecision p l target rhsExp)
              (Fs.reverse.getD (Fs.length-1-j.val) (fun _ => 0) k)).re) i| ≤
          haloResidualError p u (executionPrecision p l target rhsExp) rhsExp target := by
  obtain ⟨R,hR,hC⟩ := hleft
  obtain ⟨S,hS,hD⟩ := hright
  change ∀ rhs, Solves (realMatrix s t p u)
    (haloInterior s t (PhaseCellBand.width p u) 0 (0+(n-min n (s-a)))) (S rhs) rhs at hS
  simp only [Nat.zero_add] at hS
  let T := fun rhs k => if k ∈ haloInterior s t (PhaseCellBand.width p u) a (a+min n (s-a))
    then R rhs k else S rhs k
  refine ⟨T,cyclicPrincipalInterior_solver p u a n ha hn R S hR hS,?_⟩
  intro j
  have hjC : j.val < Cs.length := by rw [hCs]; exact j.isLt
  have hjD : j.val < Ds.length := by rw [hDs]; exact j.isLt
  have hC' := hC ⟨j.val,hjC⟩
  have hD' := hD ⟨j.val,hjD⟩
  change ∀ i ∈ haloBoundary s t (PhaseCellBand.width p u) a (a+min n (s-a)),
    ‖value (executionPrecision p l target rhsExp) (realPartWord (Cs[j.val] i))-
      (residual (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) a (a+min n (s-a))) R
        (fun k => (value (executionPrecision p l target rhsExp)
          (Fs.reverse.getD (Fs.length-1-j.val) (fun _ => 0) k)).re) i : ℂ)‖ ≤
      haloResidualError p u (executionPrecision p l target rhsExp) rhsExp target at hC'
  change ∀ i ∈ haloBoundary s t (PhaseCellBand.width p u) 0 (0+(n-min n (s-a))),
    ‖value (executionPrecision p l target rhsExp) (realPartWord (Ds[j.val] i))-
      (residual (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) 0 (0+(n-min n (s-a)))) S
        (fun k => (value (executionPrecision p l target rhsExp)
          (Fs.reverse.getD (Fs.length-1-j.val) (fun _ => 0) k)).re) i : ℂ)‖ ≤
      haloResidualError p u (executionPrecision p l target rhsExp) rhsExp target at hD'
  simp only [Nat.zero_add] at hD'
  have he := cyclicPrincipal_residual_pieces_error p u a n ha hn R S
    (fun k => (value (executionPrecision p l target rhsExp)
      (Fs.reverse.getD (Fs.length-1-j.val) (fun _ => 0) k)).re)
    (fun i => (value (executionPrecision p l target rhsExp) (Cs[j.val] i)).re)
    (fun i => (value (executionPrecision p l target rhsExp) (Ds[j.val] i)).re)
    (haloResidualError p u (executionPrecision p l target rhsExp) rhsExp target)
    (by simpa only [value_realPartWord_sub_norm] using hC')
    (by simpa only [value_realPartWord_sub_norm] using hD')
  intro i hi
  simpa only [cyclicReplicaResidualField,List.getD_eq_getElem _ _ hjC,
    List.getD_eq_getElem _ _ hjD,value_realPartWord_re,apply_ite,T] using he i hi

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
