module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleasedCachedReplicaCoupling
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetireCouplingMasks
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaCouplingResidualBounds
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReloadReplicaCouplingHeaders

/-! Reuse released numerical storage and retained gather controls. Gather 125
holds the residual archive; shared headers are copied from actual masters. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

noncomputable def releasedRetiredCachedReplicaCoupling {plan : ReplicaInteriorPlacement T}
    (placement : ReplicaCouplingPlacement plan) (output rhs : Fin T) (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  .seq (releasedCachedReplicaCoupling placement output rhs hQ) (retireCouplingMasks placement.bank)

def releasedRetiredCachedReplicaCouplingCost (H : ReplicaHaloProblem s) :=
  releasedCachedReplicaCouplingCost H+(4*(H.span+H.band)+4)

theorem releasedRetiredCachedReplicaCoupling_exec (H : ReplicaHaloProblem s) {plan : ReplicaInteriorPlacement T}
    (placement : ReplicaCouplingPlacement plan) (output rhs : Fin T)
    (houtput : ∀ k, plan.gather k ≠ output) (hrhs : ∀ k, plan.gather k ≠ rhs)
    (hbankOutput : ∀ k, placement.bank k ≠ output) (hbankRhs : ∀ k, placement.bank k ≠ rhs)
    (hsep : output ≠ rhs) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (hspan : H.span+H.band ≤ s) (horigin : H.origin < s)
    (outputTail rhsTail raw resultTail : List (Fin (A+4))) (buffers : ReplicaLoopBuffers A)
    (v : HS T Q A U) (S : Stacks T A)
    (h : ReplicaCouplingCursor H output rhs outputTail rhsTail 0 S)
    (hheaders : ReplicaLoopHeaders H plan.gather buffers S)
    (hbank : embStk weightCacheCoreReg (embStk plan.solver S) = releasedCellBank [] raw resultTail S.inp S.out)
    (hblank : ∀ k ∈ ([(145 : Fin 168),146,147,148,149,151,154,155,156,157,163,164,165]), S.R (placement.bank k) = [])
    (hfresh : ∀ k ∈ [(127 : Fin 168),135,139,140,143,158,166,167], S.R (placement.bank k) = [])
    (h136 : S.R (placement.bank 136) = []) (h159 : S.R (placement.bank 159) = [])
    (h161 : S.R (placement.bank 161) = []) :
    ∃ v' F m, ∃ Ds : List (ZMod s → GaussianInt), v'.user = v.user ∧ m ≤ releasedRetiredCachedReplicaCouplingCost H ∧
      Exec body (releasedRetiredCachedReplicaCoupling placement output rhs hQ) (mk v S) m (mk v' F) ∧
      F.R (plan.gather 122) = [] ∧ F.R output = outputTail ∧ F.R rhs = rhsTail ∧
      RetainedCouplingReady (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band H.origin (H.origin+H.span) raw
        (embStk weightCacheCoreReg (embStk plan.solver F)) ∧
      CouplingIntervalMetadata H.metadataWidth s H.t H.band H.origin (H.origin+H.span) H.origin H.span (embStk placement.bank F) ∧
      F.L = S.L ∧ F.inp = S.inp ∧ F.out = S.out ∧
      (∀ k, (∀ i, placement.bank i ≠ k) → k ∉ [output,rhs,plan.gather 125] → F.R k = S.R k) ∧
      Ds.length = H.Fs.length ∧
      F.R (plan.gather 125) = Ds.flatMap (fun D => cstream A H.wordWidth (packedInterval H.origin H.span D)) ∧
      (∀ j : Fin Ds.length, ReplicaCouplingResidualSpec H (H.Fs.length-1-j.val) Ds[j.val]) ∧
      F.R (placement.bank 138) = cstream A H.wordWidth
        (couplingCoefficientPageInterval (2^15*H.p) H.precision s H.t H.u H.band H.origin (H.origin+H.span) H.origin H.span)++S.R (placement.bank 138) ∧
      (F.R (placement.bank 139)).length =
        (couplingCoefficientPageInterval (2^15*H.p) H.precision s H.t H.u H.band H.origin (H.origin+H.span) H.origin H.span).length ∧
      (F.R (placement.bank 140)).length = 2*H.band+1 ∧
      (∀ k ∈ [(127 : Fin 168),143,166,158,135,167], F.R (placement.bank k) = []) ∧
      (∀ D ∈ Ds, (∀ i, ‖value H.precision (D i)‖ ≤ (2 : ℝ)^replicaResidualExponent H) ∧ (∀ i, Fits H.wordWidth (D i))) ∧
      (embStk weightCacheCoreReg (embStk plan.solver F)).R =
      counterR H.precision H.wordWidth
        (replicaCouplingUnaryBank A (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band
          H.origin (H.origin+H.span) raw resultTail S.inp S.out).R ∧
      (∀ k : Fin 168, 117 ≤ k.val → k ∉ replicaCouplingSetupPorts → F.R (placement.bank k) = S.R (placement.bank k)) := by
  obtain ⟨v₁,J,n,Ds,hu,hn,hex,hclock,hout,hrhsF,hready,hmeta,hL,hi,ho,hframe,hlen,harchive,hgood,
    hpage,hcount,hrows,hfreshJ,hbounds,hnative,hshared,hmask159,hmask161⟩ :=
    releasedCachedReplicaCoupling_exec (body := body) H placement output rhs houtput hrhs hbankOutput hbankRhs
      hsep hQ hA hspan horigin outputTail rhsTail raw resultTail buffers v S h hheaders hbank hblank hfresh h136 h159 h161
  obtain ⟨v₂,hu₂,hex₂⟩ := retireCouplingMasks_exec (body := body) placement.bank placement.bank_injective v₁ J
  let F := retiredCouplingMasksState placement.bank J
  have hmask (k : Fin 168) (hk159 : k ≠ 159) (hk161 : k ≠ 161) : F.R (placement.bank k) = J.R (placement.bank k) :=
    retiredCouplingMasksState_frame _ _ _ (fun hh => hk159 (placement.bank_injective hh))
      (fun hh => hk161 (placement.bank_injective hh))
  have hoff (k : Fin T) (hk : ∀ i, placement.bank i ≠ k) : F.R k = J.R k :=
    retiredCouplingMasksState_frame _ _ _ (hk 159).symm (hk 161).symm
  have hnativeFrame : embStk weightCacheCoreReg (embStk plan.solver F) =
      embStk weightCacheCoreReg (embStk plan.solver J) := by
    rw [← placement.native_view F,← placement.native_view J]
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    exact hmask _ (by have := k.isLt; intro hh; have := congrArg Fin.val hh; simp only [Fin.val_castLE] at this; omega)
      (by have := k.isLt; intro hh; have := congrArg Fin.val hh; simp only [Fin.val_castLE] at this; omega)
  have hlen159 : (J.R (placement.bank 159)).length = H.span+2*H.band := by
    rw [hmask159,List.length_map,couplingRibbonFlags_eq_map false H.s_lt_t H.band H.origin (H.origin+H.span)
      H.origin H.span H.span_fit H.band_fit H.span_fit]
    simp
  have hlen161 : (J.R (placement.bank 161)).length = H.span := by
    rw [hmask161,recoveryGuardIntervalSymbols_length]
  have htime : (2*(J.R (placement.bank 159)).length+2)+(2*(J.R (placement.bank 161)).length+2) =
      4*(H.span+H.band)+4 := by rw [hlen159,hlen161]; omega
  have hex₂' : Exec body (retireCouplingMasks placement.bank) (mk v₁ J) (4*(H.span+H.band)+4) (mk v₂ F) := by
    simpa only [htime] using hex₂
  refine ⟨v₂,F,n+(4*(H.span+H.band)+4),Ds,hu₂.trans hu,by unfold releasedRetiredCachedReplicaCouplingCost; omega,
    .seq hex hex₂',?_,?_,?_,?_,?_,hL,hi,ho,?_,hlen,?_,hgood,?_,?_,?_,?_,hbounds,?_,?_⟩
  · rw [hoff _ (fun i => placement.bank_gather_disjoint i 122)]; exact hclock
  · rw [hoff _ hbankOutput]; exact hout
  · rw [hoff _ hbankRhs]; exact hrhsF
  · rw [hnativeFrame]; exact hready
  · apply hmeta.of_frame (F := embStk placement.bank F) (hmask 163 (by decide) (by decide))
    intro k hk
    have hh : k ≠ 159 ∧ k ≠ 161 := by
      simp only [couplingIntervalPorts,List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact hmask k hh.1 hh.2
  · intro k hk hp
    exact (hoff k hk).trans (hframe k hk hp)
  · rw [hoff _ (fun i => placement.bank_gather_disjoint i 125)]; exact harchive
  · rw [hmask 138 (by decide) (by decide)]; exact hpage
  · rw [hmask 139 (by decide) (by decide)]; exact hcount
  · rw [hmask 140 (by decide) (by decide)]; exact hrows
  · intro k hk
    have hh : k ≠ 159 ∧ k ≠ 161 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [hmask k hh.1 hh.2]; exact hfreshJ k hk
  · rw [hnativeFrame]; exact hnative
  · intro k hk hnot
    by_cases hk159 : k = 159
    · subst k
      simpa [F,retiredCouplingMasksState,placement.bank_injective.ne (by decide : (159 : Fin 168) ≠ 161)] using h159.symm
    by_cases hk161 : k = 161
    · subst k
      simpa [F,retiredCouplingMasksState] using h161.symm
    exact (hmask k hk159 hk161).trans (hshared k hk hnot hk159 hk161)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
