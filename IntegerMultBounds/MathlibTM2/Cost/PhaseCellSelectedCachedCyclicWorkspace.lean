module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCyclicFactorWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedCyclicReplicaBatch
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedActualResidualBatchWorkspace
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCyclicResidualExportWorkspace

/-! One selected bound for the actual cached passes, export, factor and solve batch. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {Q A : ℕ} {U : Type}

theorem selectedReplicaHaloWidths (ct ce : ℕ) {m : ℕ} (h : Sizes.Big m)
    (i : Fin (Sizes.d m)) [NeZero (Sizes.s m i)] (H : ReplicaHaloProblem (Sizes.s m i))
    (hp : H.p = Sizes.p m) (ht : H.t = Sizes.t m i)
    (hl : H.l = haloInverseRingLog (Sizes.s m i) (Sizes.t m i))
    (hu : H.u ≤ Sizes.p m) (htarget : H.target ≤ ct*Sizes.p m) (hrhs : H.rhsExp ≤ ce*Sizes.p m) :
    let cw := 16*20+8*ct+8*ce+128
    H.wordWidth ≤ cw*Sizes.p m ∧ H.metadataWidth ≤ ((2*cw+426009)*cw)*Sizes.p m := by
  dsimp only
  let cw := 16*20+8*ct+8*ce+128
  obtain ⟨_,_,hw,hV⟩ := selectedHaloGatheredWidths ct ce h i H.u H.target H.rhsExp hu htarget hrhs
  have hwH : H.wordWidth ≤ cw*Sizes.p m := by
    simpa only [ReplicaHaloProblem.wordWidth,hp,ht,hl,cw] using hw
  have hVH : H.metadataWidth ≤ (2*cw+426009)*H.wordWidth := by
    simpa only [ReplicaHaloProblem.metadataWidth,ReplicaHaloProblem.precision,
      ReplicaHaloProblem.wordWidth,hp,ht,hl,cw] using hV
  refine ⟨hwH,?_⟩
  have hm := Nat.mul_le_mul_left (2*cw+426009) hwH
  exact hVH.trans (by simpa only [Nat.mul_assoc] using hm)

noncomputable def cachedCyclicWorkspaceTrafficFactor (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (ct ce : ℕ) : ℕ :=
  let cw := 16*20+8*ct+8*ce+128
  2*cyclicCachedReplicaTrafficFactor (A := A) (U := U) hR hQ ct ce+
    (411*cyclicResidualExportPush (Q := Q) (A := A) (U := U)*(cw+1)+8)+(cw+12)

theorem selectedCachedCyclicReplicaWorkspace_le (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (ct ce cb : ℕ) :
    let cw := 16*20+8*ct+8*ce+128
    ∀ᶠ m : ℕ in atTop, ∀ (_h : Sizes.Big m) (i : Fin (Sizes.d m)) [NeZero (Sizes.s m i)],
      ∀ (H K : ReplicaHaloProblem (Sizes.s m i)) (u target a n replicas : ℕ),
      let p := Sizes.p m
      let s := Sizes.s m i
      let t := Sizes.t m i
      let l := haloInverseRingLog s t
      let N := (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card
      let stage := initialSchurTarget p u (boundaryTableBits p target 2 N) 2
      let q := executionPrecision p l stage 2
      let w := executionWidth p l stage 2
      (∀ D ∈ [H,K], D.p = p ∧ D.t = t ∧ D.l = l ∧ D.u ≤ p ∧
        D.target ≤ ct*p ∧ D.rhsExp ≤ ce*p) →
      H.Fs.length = replicas → K.Fs.length = replicas →
      w ≤ cw*p → PhaseCellBand.width p u ≤ cb*p → u ≤ p →
      PhaseCellBand.width p u ≤ s → a ≤ s → n ≤ s →
      cachedCyclicReplicaWorkspace (P := Empty) (A := A) (U := U) H K hR hQ
        p u l t a n target q w N replicas ≤
        cachedCyclicWorkspaceTrafficFactor (A := A) (U := U) hR hQ ct ce*replicas*t*p+22*Sizes.T m := by
  dsimp only
  let cw := 16*20+8*ct+8*ce+128
  filter_upwards [selectedCachedReplicaPassMasksWorkspace_le (A := A) (U := U) hR hQ ct ce,
    selectedCyclicResidualExportWorkspace_le (Q := Q) (A := A) (U := U) cw,
    selectedActualCyclicFactorWorkspace_le (A := A) (U := U) hR hQ cw cb,
    selectedActualResidualBatchWorkspace_le (A := A) (U := U) hQ cw (24*cb+1)] with m hp he hf hs
  intro h i _ H K u target a n replicas
  let p := Sizes.p m
  let s := Sizes.s m i
  let t := Sizes.t m i
  let l := haloInverseRingLog s t
  let N := (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card
  let stage := initialSchurTarget p u (boundaryTableBits p target 2 N) 2
  let q := executionPrecision p l stage 2
  let w := executionWidth p l stage 2
  intro hprofile hcountH hcountK hw hbP hu hb ha hn
  have hpass := hp h i H K hprofile
  have hwidths (D : ReplicaHaloProblem s) (hD : D ∈ [H,K]) : D.wordWidth ≤ cw*p := by
    obtain ⟨hp,ht,hl,hu,htarget,hrhs⟩ := hprofile D hD
    exact (selectedReplicaHaloWidths ct ce h i D hp ht hl hu htarget hrhs).1
  have hN : N ≤ s := by simpa only [N,ZMod.card] using
    (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card_le_univ
  have hexport := he h i H K n N (hwidths H (by simp)) (hwidths K (by simp)) hn hN
  have hfactor := hf h i u target a n hw hbP hu hb ha hn
  have hqW : q ≤ w := by dsimp only [q,w,executionPrecision,executionWidth]; omega
  have hppos : 1 ≤ p := by have := h.thirteen_le_p; dsimp only [p]; omega
  have hW : 24*PhaseCellBand.width p u+1 ≤ (24*cb+1)*p := by nlinarith only [hbP,hppos]
  have hsolve := hs h i q w N (24*PhaseCellBand.width p u+1) replicas hqW hw hN hW
  rw [hcountH,hcountK] at hpass
  rw [hcountH] at hexport
  unfold cachedCyclicReplicaWorkspace cachedCyclicWorkspaceTrafficFactor
  change cachedReplicaPassMasksWorkspace (A := A) (U := U) H K hR hQ+
    (cyclicReplicaConsumerExportWorkspace (Q := Q) (A := A) (U := U) H K n N+
      (actualCyclicFactorWorkspace (P₀ := Empty) (A := A) (U := U) hR hQ p u l s t a n target+
        preparedResidualBatchWorkspace (A := A) (U := U) Empty hQ q w N (24*PhaseCellBand.width p u+1) replicas)) ≤
    (2*cyclicCachedReplicaTrafficFactor (A := A) (U := U) hR hQ ct ce+
      (411*cyclicResidualExportPush (Q := Q) (A := A) (U := U)*(cw+1)+8)+(cw+12))*replicas*t*p+22*Sizes.T m
  nlinarith only [hpass,hexport,hfactor,hsolve]

end IntegerMultBounds.MathlibTM2.Cost
