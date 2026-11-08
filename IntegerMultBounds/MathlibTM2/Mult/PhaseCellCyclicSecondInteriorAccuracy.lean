module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExecutedCyclicSecondInterior
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicRecoveryPieceAccuracy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicRecoveryRowRead

/-! The actual second-pass output fields, paired with their saved joint boundary
rows, meet the final cyclic accuracy target in the original replica order. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

theorem cyclicSecondInterior_fields_target {s t p u l a n T A : ℕ} [NeZero s] {α d : ℝ}
    (axis : RecoveryAxisBounds s t p u l α d) (ha : a < s) (hn : n ≤ s) (target : ℕ) :
    let band := PhaseCellBand.width p u
    let B := cyclicPrincipalBoundary s t band a n
    let solveTarget := boundaryRecoveryTarget p target
    let cellTarget := initialSchurTarget p u (boundaryTableBits p solveTarget 2 B.card) 2
    let q := executionPrecision p l cellTarget 2
    let w := executionWidth p l cellTarget 2
    ∀ (Fs : List (ZMod s → GaussianInt)) (hF : ∀ F ∈ Fs, ∀ i, ‖value q (F i)‖ ≤ (2 : ℝ)^2),
    let H := axis.cyclicLeftReplicaProblem cellTarget 2 a n ha Fs hF
    let K := axis.cyclicRightReplicaProblem cellTarget 2 a n hn Fs hF
    ∀ (solutions : List (List GaussianInt)) (J L : ReplicaHaloProblem s),
    solutions.length = Fs.length →
    (∀ solution ∈ solutions, solution.length = B.card ∧ ∀ y ∈ solution, Fits w y) →
    CyclicBoundaryRowsAccurate p t u a n q solveTarget Fs solutions →
    H.SameLayout J → K.SameLayout L →
    J.target = boundaryHaloRecoveryTarget p solveTarget B.card → L.target = boundaryHaloRecoveryTarget p solveTarget B.card →
    let rows := cyclicBoundaryRecoveryRows B solutions Fs
    J.Fs = rows.map (fun row => guardedCouplingRowField (2^15*H.p) H.precision H.t H.u H.band
      H.origin (H.origin+H.span) true row.1 row.2.1) →
    L.Fs = rows.map (fun row => guardedCouplingRowField (2^15*K.p) K.precision K.t K.u K.band
      K.origin (K.origin+K.span) true row.1 row.2.1) →
    ∀ (dstL dstR : Fin T) (tailL tailR : List (Fin (A+4))) (S : Stacks T A),
    RealReplicaHaloOutput J dstL tailL S → RealReplicaHaloOutput L dstR tailR S →
    ∃ Ds Es : List (ZMod s → GaussianInt), Ds.length = Fs.length ∧ Es.length = Fs.length ∧
      S.R dstL = Ds.flatMap (fun D => cstream A w (packedInterval H.origin H.span D))++tailL ∧
      S.R dstR = Es.flatMap (fun E => cstream A w (packedInterval K.origin K.span E))++tailR ∧
      ∀ j : Fin Fs.length,
        let Y := boundarySolutionField B (solutions.getD j.val [])
        let output := cyclicPublicationField t band a n (Ds.getD j.val (fun _ => 0)) (Es.getD j.val (fun _ => 0)) Y
        (∀ i, (Ds.getD j.val (fun _ => 0) i).im = 0) ∧
        (∀ i, (Es.getD j.val (fun _ => 0) i).im = 0) ∧
        (∀ i, Fits w (output i)) ∧
        (∀ i ∉ cyclicPrincipalVertices s a n, output i = 0) ∧ ∀ x : ZMod s → ℝ,
          SchurDominance.Solves (realMatrix s t p u) (cyclicPrincipalVertices s a n) x
            (fun i => (value q (Fs.getD j.val (fun _ => 0) i)).re) →
          PhaseCellInterface.ErrorOn (cyclicPrincipalVertices s a n)
            (fun i => (value q (output i)).re) x (1/(2 : ℝ)^target) := by
  dsimp only
  let band := PhaseCellBand.width p u
  let B := cyclicPrincipalBoundary s t band a n
  let solveTarget := boundaryRecoveryTarget p target
  let cellTarget := initialSchurTarget p u (boundaryTableBits p solveTarget 2 B.card) 2
  let q := executionPrecision p l cellTarget 2
  let w := executionWidth p l cellTarget 2
  intro Fs hF
  let H := axis.cyclicLeftReplicaProblem cellTarget 2 a n ha Fs hF
  let K := axis.cyclicRightReplicaProblem cellTarget 2 a n hn Fs hF
  have hHw : H.wordWidth = w := rfl
  have hKw : K.wordWidth = w := rfl
  have hHq : H.precision = q := rfl
  have hKq : K.precision = q := rfl
  have hKo : K.origin = 0 := rfl
  have hKs : K.span = n-min n (s-a) := rfl
  have hHt : H.t = t := rfl
  have hHb : H.band = band := rfl
  have hHo : H.origin = a := rfl
  have hHs : H.span = min n (s-a) := rfl
  have hKt : K.t = t := rfl
  have hKb : K.band = band := rfl
  intro solutions J L hlen hformat haccuracy layoutL layoutR hJtarget hLtarget hJFs hLFs dstL dstR tailL tailR S hL hR
  obtain ⟨Ds,hDs,hencD,hgoodD⟩ := hL
  obtain ⟨Es,hEs,hencE,hgoodE⟩ := hR
  have hJlen : J.Fs.length = Fs.length := layoutL.count
  have hLlen : L.Fs.length = Fs.length := layoutR.count
  have hDlen : Ds.length = Fs.length := hDs.trans hJlen
  have hElen : Es.length = Fs.length := hEs.trans hLlen
  rw [layoutL.wordWidth,layoutL.origin,layoutL.span,hHw] at hencD
  rw [layoutR.wordWidth,layoutR.origin,layoutR.span,hKw] at hencE
  refine ⟨Ds,Es,hDlen,hElen,?_,?_,?_⟩
  · simpa only [List.flatMap_def] using hencD
  · simpa only [List.flatMap_def] using hencE
  · intro j
    have hjD : j.val < Ds.length := by simpa only [hDlen] using j.isLt
    have hjE : j.val < Es.length := by simpa only [hElen] using j.isLt
    have hjJ : j.val < J.Fs.length := by simpa only [hJlen] using j.isLt
    have hjL : j.val < L.Fs.length := by simpa only [hLlen] using j.isLt
    have hjS : j.val < solutions.length := by simpa only [hlen] using j.isLt
    have hsolmem : solutions.getD j.val [] ∈ solutions := by
      rw [List.getD_eq_getElem _ _ hjS]; exact List.getElem_mem hjS
    have hsolformat := hformat _ hsolmem
    have hfitsD := (hgoodD ⟨j.val,hjD⟩).2.1
    have hfitsE := (hgoodE ⟨j.val,hjE⟩).2.1
    rw [layoutL.wordWidth,hHw] at hfitsD
    rw [layoutR.wordWidth,hKw] at hfitsE
    refine ⟨(by simpa only [List.getD_eq_getElem _ _ hjD] using (hgoodD ⟨j.val,hjD⟩).1),
      (by simpa only [List.getD_eq_getElem _ _ hjE] using (hgoodE ⟨j.val,hjE⟩).1),
      cyclicPublicationField_fits t band a n w _ _ _
      (by simpa only [List.getD_eq_getElem _ _ hjD] using hfitsD)
      (by simpa only [List.getD_eq_getElem _ _ hjE] using hfitsE)
      (boundarySolutionField_fits w B _ hsolformat.1 hsolformat.2),?_,?_⟩
    · apply cyclicPublicationField_off
      intro i hi
      apply boundarySolutionField_off
      intro hiB
      exact hi (Finset.sdiff_subset hiB)
    · intro x hx
      have hboundary := haccuracy j x (by simpa only [cyclicReplica_rhs_read Fs j] using hx)
      have hreadJ : J.Fs.reverse.getD j.val (fun _ => 0) =
          guardedCouplingRowField (2^15*H.p) H.precision H.t H.u H.band H.origin (H.origin+H.span) true
            (boundarySolutionField B (solutions.getD j.val [])) (Fs.getD j.val (fun _ => 0)) := by
        rw [hJFs]
        exact cyclicBoundaryRecoveryRows_map_read _ _ B solutions Fs hlen j
      have hreadL : L.Fs.reverse.getD j.val (fun _ => 0) =
          guardedCouplingRowField (2^15*K.p) K.precision K.t K.u K.band K.origin (K.origin+K.span) true
            (boundarySolutionField B (solutions.getD j.val [])) (Fs.getD j.val (fun _ => 0)) := by
        rw [hLFs]
        exact cyclicBoundaryRecoveryRows_map_read _ _ B solutions Fs hlen j
      have hxL := J.solves j.val hjJ
      have hxR := L.solves j.val hjL
      change SchurDominance.Solves (realMatrix s J.t J.p J.u)
        (haloInterior s J.t J.band J.origin (J.origin+J.span)) (J.x j.val)
        (fun i => (value J.precision (J.Fs.reverse.getD j.val (fun _ => 0) i)).re) at hxL
      change SchurDominance.Solves (realMatrix s L.t L.p L.u)
        (haloInterior s L.t L.band L.origin (L.origin+L.span)) (L.x j.val)
        (fun i => (value L.precision (L.Fs.reverse.getD j.val (fun _ => 0) i)).re) at hxR
      rw [hreadJ,layoutL.precision,layoutL.p,layoutL.t,layoutL.u,layoutL.band,layoutL.origin,layoutL.span,hHq] at hxL
      rw [hreadL,layoutR.precision,layoutR.p,layoutR.t,layoutR.u,layoutR.band,layoutR.origin,layoutR.span,hKq] at hxR
      rw [hKo,hKs,Nat.zero_add] at hxR
      have heD := (hgoodD ⟨j.val,hjD⟩).2.2.2
      have heE := (hgoodE ⟨j.val,hjE⟩).2.2.2
      rw [layoutL.t,layoutL.band,layoutL.origin,layoutL.span,layoutL.precision,hJtarget,hHq,hHt,hHb,hHo,hHs] at heD
      rw [layoutR.t,layoutR.band,layoutR.origin,layoutR.span,layoutR.precision,hLtarget,hKq,hKo,hKs,Nat.zero_add,hKt,hKb] at heE
      apply cyclicRecovery_pieces_target axis ha hn target (Fs.getD j.val (fun _ => 0))
        (by rw [List.getD_eq_getElem _ _ j.isLt]; exact hF _ (List.getElem_mem j.isLt))
        (solutions.getD j.val []) _ _ x (J.x j.val) (L.x j.val)
        (fun i hi => (hboundary.2 i hi).2) (fun i hi => (hboundary.2 i hi).1) hx hxL hxR
      · simpa only [List.getD_eq_getElem _ _ hjD] using heD
      · simpa only [List.getD_eq_getElem _ _ hjE] using heE

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
