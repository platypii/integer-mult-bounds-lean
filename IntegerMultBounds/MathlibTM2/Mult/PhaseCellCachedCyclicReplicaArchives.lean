module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedReplicaPassMasks
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicReplicaResidualAccuracy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicReplicaBoundaryFormat

/-! Instantiate the paired executed passes at the two cyclic pieces. Original
RHS headers, rather than supplied residual archives or certificates, are inputs. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem cachedCyclicReplicaArchives_exec {s t p u l : ℕ} [NeZero s] {α d : ℝ}
    (axis : RecoveryAxisBounds s t p u l α d) (cellTarget rhsExp a n : ℕ)
    (ha : a < s) (hn : n ≤ s)
    (hleftRoom : min n (s-a)+PhaseCellBand.width p u ≤ s)
    (hrightRoom : n-min n (s-a)+PhaseCellBand.width p u ≤ s)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A) :
    let q := executionPrecision p l cellTarget rhsExp
    let band := PhaseCellBand.width p u
    let B := cyclicPrincipalBoundary s t band a n
    ∀ (Fs : List (ZMod s → GaussianInt))
      (hF : ∀ F ∈ Fs, ∀ i, ‖value q (F i)‖ ≤ (2 : ℝ)^rhsExp),
    let H := axis.cyclicLeftReplicaProblem cellTarget rhsExp a n ha Fs hF
    let K := axis.cyclicRightReplicaProblem cellTarget rhsExp a n hn Fs hF
    ∀ (left right : CachedReplicaPassPlacement T),
    (∀ k, left.Owns k → ¬right.Owns k) →
    ∀ (leftDst rightDst : Fin T), leftDst ≠ rightDst →
    (¬left.Owns leftDst ∧ ¬right.Owns leftDst) →
    (¬left.Owns rightDst ∧ ¬right.Owns rightDst) →
    ∀ (leftBuffers rightBuffers : ReplicaLoopBuffers A) (v : HS T Q A U) (S : Stacks T A),
    CachedReplicaPassInput H left leftBuffers S → CachedReplicaPassInput K right rightBuffers S →
    S.R leftDst = [] → S.R rightDst = [] →
    ∃ (vf : HS T Q A U) (mid G : Stacks T A) (m : ℕ), ∃ Cs Ds : List (ZMod s → GaussianInt),
      let F : Stacks T A := {G with R := (Function.update (Function.update G.R leftDst
        (couplingSourceIntervalMaskSymbols true A s t band a (a+min n (s-a)) a (min n (s-a)))) rightDst
        (couplingSourceIntervalMaskSymbols true A s t band 0 (n-min n (s-a)) 0 (n-min n (s-a))))}
      let rows := (Cs.zip Ds).map (fun z => cyclicReplicaBoundaryRow t band a n z.1 z.2)
      vf.user = v.user ∧ m ≤ (cachedReplicaPassCost H+cachedReplicaPassCost K)+
        (placedReplicaBoundaryMaskCost H+placedReplicaBoundaryMaskCost K) ∧
      Exec body (cachedReplicaPassMasks left right leftDst rightDst hR hQ) (mk v S) m (mk vf F) ∧
      CachedReplicaPassPost H left leftBuffers S F Cs ∧ CachedReplicaPassPost K right rightBuffers mid F Ds ∧
      rows.length = Fs.length ∧ (∀ row ∈ rows, row.length = B.card) ∧
      (∀ row ∈ rows, ∀ z ∈ row, z.im = 0) ∧
      (∀ row ∈ rows, ∀ z ∈ row,
        |gv q z.re| ≤ (2 : ℝ)^couplingRowExponent rhsExp (stableInteriorExponent p rhsExp) (8*p+1) (couplingCountExponent p u) ∧
        |gv q z.im| ≤ (2 : ℝ)^couplingRowExponent rhsExp (stableInteriorExponent p rhsExp) (8*p+1) (couplingCountExponent p u)) ∧
      (∀ k, ¬left.Owns k → ¬right.Owns k → F.L k = S.L k) ∧
      (∀ k, ¬left.Owns k → ¬right.Owns k → k ≠ leftDst → k ≠ rightDst →
        F.L k = S.L k ∧ F.R k = S.R k) ∧
      ∃ R : (ZMod s → ℝ) → ZMod s → ℝ,
        (∀ rhs, Solves (realMatrix s t p u) (cyclicPrincipalInterior s t band a n) (R rhs) rhs) ∧
        ∀ j : Fin Fs.length, ∀ i ∈ B,
          |(value q (cyclicReplicaResidualField a n (Cs.getD j.val (fun _ => 0))
            (Ds.getD j.val (fun _ => 0)) i)).re-
            residual (realMatrix s t p u) (cyclicPrincipalInterior s t band a n) R
              (fun k => (value q (Fs.reverse.getD (Fs.length-1-j.val) (fun _ => 0) k)).re) i| ≤
            haloResidualError p u q rhsExp cellTarget := by
  dsimp only
  intro Fs hF left right hdisjoint leftDst rightDst hsep hleftSlot hrightSlot
    leftBuffers rightBuffers v S leftInputs rightInputs hleftDst hrightDst
  let H := axis.cyclicLeftReplicaProblem cellTarget rhsExp a n ha Fs hF
  let K := axis.cyclicRightReplicaProblem cellTarget rhsExp a n hn Fs hF
  obtain ⟨vf,mid,G,m,Cs,Ds,hu,hm,he,hleft,hright,hleftMask,hrightMask,hleftFrame,hframe⟩ :=
    cachedReplicaPassMasks_exec (body := body) H K left right hdisjoint leftDst rightDst hsep hleftSlot hrightSlot
      hR hQ hA hleftRoom ha axis.hpad axis.hp axis.hpacket hrightRoom (NeZero.pos s)
      axis.hpad axis.hp axis.hpacket leftBuffers rightBuffers v S leftInputs rightInputs hleftDst hrightDst
  have hCs : Cs.length = Fs.length := hleft.length
  have hDs : Ds.length = Fs.length := hright.length
  obtain ⟨hlen,hrows,hreal,hbound⟩ := cyclicReplicaBoundaryRows_format axis cellTarget rhsExp a n ha hn
    Fs hF Cs Ds hCs hDs hleft.residual hright.residual
  have hrightMaskValue : couplingSourceIntervalMaskSymbols true A s K.t K.band K.origin
      (K.origin+K.span) K.origin K.span =
      couplingSourceIntervalMaskSymbols true A s t (PhaseCellBand.width p u) 0 (n-min n (s-a)) 0 (n-min n (s-a)) := by
    change couplingSourceIntervalMaskSymbols true A s t (PhaseCellBand.width p u) 0 (0+(n-min n (s-a)))
      0 (n-min n (s-a)) = _
    rw [Nat.zero_add]
  have haccurate := cyclicReplicaResiduals_accurate axis cellTarget rhsExp a n ha hn Fs hF Cs Ds hCs hDs
    hleft.accurate hright.accurate
  rw [hrightMaskValue] at he hleft hright hframe
  exact ⟨vf,mid,G,m,Cs,Ds,hu,hm,he,hleft,hright,hlen,hrows,hreal,hbound,hleftFrame,hframe,haccurate⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
