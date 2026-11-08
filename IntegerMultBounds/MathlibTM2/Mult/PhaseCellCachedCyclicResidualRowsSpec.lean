module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedCyclicResidualRows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicReplicaBoundaryFormat
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicReplicaResidualAccuracy

/-! Executed ordered Schur RHS packets with format and original-system accuracy,
derived from the certificates returned by the two existing cached passes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 180 Q A U}

theorem cachedCyclicResidualRows_spec {s t p u l : ℕ} [NeZero s] {α d : ℝ}
    (axis : RecoveryAxisBounds s t p u l α d) (hA : 4 ≤ A)
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
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    let band := PhaseCellBand.width p u
    let B := cyclicPrincipalBoundary s t band a n
    let rows := (Cs.zip Ds).map (fun z => cyclicReplicaBoundaryRow t band a n z.1 z.2)
    ∀ (leftTail rightTail : List (Fin (A+4))) (v : HS 180 Q A U) (S : Stacks 180 A),
    CyclicReplicaBoundaryReady (s := s) t band a n w S →
    S.R 169 = Cs.flatMap (fun C => cstream A w (packedInterval a (min n (s-a)) C))++leftTail →
    S.R 172 = Ds.flatMap (fun D => cstream A w (packedInterval 0 (n-min n (s-a)) D))++rightTail →
    (S.R 179).length = Fs.length → S.R 176 = [] → S.R 177 = [] → S.R 178 = [] →
    ∃ v' m, v'.user = v.user ∧
      m ≤ cyclicReplicaBoundaryBatchCost Fs.length n B.card w ∧
      Exec body cyclicReplicaBoundaryBatch (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R 169 leftTail) 172 rightTail) 6
          (cstream A w rows.flatten))}) ∧
      rows.length = Fs.length ∧ (∀ b ∈ rows, b.length = B.card) ∧
      (∀ b ∈ rows, ∀ z ∈ b, z.im = 0) ∧
      (∀ b ∈ rows, ∀ z ∈ b,
        |gv q z.re| ≤ (2 : ℝ)^couplingRowExponent rhsExp (stableInteriorExponent p rhsExp)
          (8*p+1) (couplingCountExponent p u) ∧
        |gv q z.im| ≤ (2 : ℝ)^couplingRowExponent rhsExp (stableInteriorExponent p rhsExp)
          (8*p+1) (couplingCountExponent p u)) ∧
      ∃ R : (ZMod s → ℝ) → ZMod s → ℝ,
        (∀ rhs, Solves (realMatrix s t p u) (cyclicPrincipalInterior s t band a n) (R rhs) rhs) ∧
        ∀ j : Fin Fs.length, ∀ i ∈ B,
          |(value q (cyclicReplicaResidualField a n (Cs.getD j.val (fun _ => 0))
            (Ds.getD j.val (fun _ => 0)) i)).re-
            residual (realMatrix s t p u) (cyclicPrincipalInterior s t band a n) R
              (fun k => (value q (Fs.reverse.getD (Fs.length-1-j.val) (fun _ => 0) k)).re) i| ≤
            haloResidualError p u q rhsExp target := by
  dsimp only
  intro leftTail rightTail v S ready hleft hright hreplicas h176 h177 h178
  obtain ⟨vf,m,hu,hm,he⟩ := cachedCyclicResidualRows_exec (body := body)
    axis.hst hA (PhaseCellBand.width p u) a n ha hn Cs Ds (hCs.trans hDs.symm)
    (executionWidth p l target rhsExp) leftTail rightTail v S ready hleft hright
    (hreplicas.trans hCs.symm) h176 h177 h178
  obtain ⟨hlen,hrows,hreal,hbound⟩ :=
    cyclicReplicaBoundaryRows_format axis target rhsExp a n ha hn Fs hF Cs Ds hCs hDs hC hD
  refine ⟨vf,m,hu,by simpa only [hCs] using hm,he,hlen,hrows,hreal,hbound,?_⟩
  exact cyclicReplicaResiduals_accurate axis target rhsExp a n ha hn Fs hF Cs Ds hCs hDs
    (replicaCouplingResiduals_accurate _ axis.hp axis.hpacket Cs hCs hC)
    (replicaCouplingResiduals_accurate _ axis.hp axis.hpacket Ds hDs hD)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
