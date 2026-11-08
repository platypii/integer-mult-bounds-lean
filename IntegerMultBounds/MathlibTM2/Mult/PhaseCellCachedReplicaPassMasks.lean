module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedReplicaPassPair
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicReplicaBoundaryMasks

/-! Actual paired first-pass execution supplies both residual certificates and
the metadata used to generate the shared boundary masks. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

noncomputable def cachedReplicaPassMasks (left right : CachedReplicaPassPlacement T)
    (leftDst rightDst : Fin T) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  .seq (cachedReplicaPassPair left right hR hQ)
    (cyclicReplicaBoundaryMasks left.coupling.bank right.coupling.bank leftDst rightDst)

theorem cachedReplicaPassMasks_exec (H K : ReplicaHaloProblem s)
    (left right : CachedReplicaPassPlacement T) (hdisjoint : ∀ k, left.Owns k → ¬right.Owns k)
    (leftDst rightDst : Fin T) (hsep : leftDst ≠ rightDst)
    (hleftSlot : ¬left.Owns leftDst ∧ ¬right.Owns leftDst)
    (hrightSlot : ¬left.Owns rightDst ∧ ¬right.Owns rightDst)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (hspanH : H.span+H.band ≤ s) (horiginH : H.origin < s)
    (hpadH : 2*((s/(H.t-s)+1)-2*H.band) ≤ 2^H.l+1)
    (hpH : 2 ≤ H.p) (hwidthH : 8*H.p ≤ 2^H.u)
    (hspanK : K.span+K.band ≤ s) (horiginK : K.origin < s)
    (hpadK : 2*((s/(K.t-s)+1)-2*K.band) ≤ 2^K.l+1)
    (hpK : 2 ≤ K.p) (hwidthK : 8*K.p ≤ 2^K.u)
    (leftBuffers rightBuffers : ReplicaLoopBuffers A) (v : HS T Q A U) (S : Stacks T A)
    (leftInputs : CachedReplicaPassInput H left leftBuffers S)
    (rightInputs : CachedReplicaPassInput K right rightBuffers S)
    (hleftDst : S.R leftDst = []) (hrightDst : S.R rightDst = []) :
    ∃ (vf : HS T Q A U) (mid G : Stacks T A) (m : ℕ), ∃ Cs Ds : List (ZMod s → GaussianInt),
      let F : Stacks T A := {G with R := (Function.update (Function.update G.R leftDst
        (couplingSourceIntervalMaskSymbols true A s H.t H.band H.origin (H.origin+H.span) H.origin H.span)) rightDst
        (couplingSourceIntervalMaskSymbols true A s K.t K.band K.origin (K.origin+K.span) K.origin K.span))}
      vf.user = v.user ∧ m ≤ (cachedReplicaPassCost H+cachedReplicaPassCost K)+
        (placedReplicaBoundaryMaskCost H+placedReplicaBoundaryMaskCost K) ∧
      Exec body (cachedReplicaPassMasks left right leftDst rightDst hR hQ) (mk v S) m (mk vf F) ∧
      CachedReplicaPassPost H left leftBuffers S F Cs ∧
      CachedReplicaPassPost K right rightBuffers mid F Ds ∧
      F.R leftDst = couplingSourceIntervalMaskSymbols true A s H.t H.band H.origin (H.origin+H.span) H.origin H.span ∧
      F.R rightDst = couplingSourceIntervalMaskSymbols true A s K.t K.band K.origin (K.origin+K.span) K.origin K.span ∧
      (∀ k, ¬left.Owns k → ¬right.Owns k → F.L k = S.L k) ∧
      ∀ k, ¬left.Owns k → ¬right.Owns k → k ≠ leftDst → k ≠ rightDst →
        F.L k = S.L k ∧ F.R k = S.R k := by
  obtain ⟨v₁,mid,G,m₁,Cs,Ds,hu₁,hm₁,he₁,hleft,hright,hmidIn,hmidOut,hmidFrame,hframe⟩ :=
    cachedReplicaPassPair_exec (body := body) H K left right hdisjoint hR hQ hA
      hspanH horiginH hpadH hpH hwidthH hspanK horiginK hpadK hpK hwidthK
      leftBuffers rightBuffers v S leftInputs rightInputs
  have off (job : CachedReplicaPassPlacement T) (dst : Fin T) (h : ¬job.Owns dst) :
      ∀ i, job.coupling.bank i ≠ dst := by
    intro i hi
    apply h
    rw [← hi]
    exact .bank i
  obtain ⟨vf,m₂,hu₂,hm₂,he₂,_,_⟩ := cyclicReplicaBoundaryMasks_exec (body := body)
    H K left.coupling.bank right.coupling.bank left.coupling.bank_injective right.coupling.bank_injective
    leftDst rightDst hsep (off left leftDst hleftSlot.1) (off right rightDst hrightSlot.2)
    (off right leftDst hleftSlot.2) (off left rightDst hrightSlot.1)
    v₁ G hleft.metadata hright.metadata hleft.maskBlank hright.maskBlank
    ((hframe leftDst hleftSlot.1 hleftSlot.2).2.trans hleftDst)
    ((hframe rightDst hrightSlot.1 hrightSlot.2).2.trans hrightDst)
  let F : Stacks T A := {G with R := (Function.update (Function.update G.R leftDst
    (couplingSourceIntervalMaskSymbols true A s H.t H.band H.origin (H.origin+H.span) H.origin H.span)) rightDst
    (couplingSourceIntervalMaskSymbols true A s K.t K.band K.origin (K.origin+K.span) K.origin K.span))}
  have hmaskFrame (k : Fin T) (hl : k ≠ leftDst) (hr : k ≠ rightDst) :
      F.L k = G.L k ∧ F.R k = G.R k := by simp [F,hl,hr]
  have hleftFinal : CachedReplicaPassPost H left leftBuffers S F Cs :=
    hleft.of_frame rfl rfl (fun k hk => hmaskFrame k
      (fun h => hleftSlot.1 (h ▸ hk)) (fun h => hrightSlot.1 (h ▸ hk)))
  have hrightFinal : CachedReplicaPassPost K right rightBuffers mid F Ds :=
    hright.of_frame rfl rfl (fun k hk => hmaskFrame k
      (fun h => hleftSlot.2 (h ▸ hk)) (fun h => hrightSlot.2 (h ▸ hk)))
  refine ⟨vf,mid,G,m₁+m₂,Cs,Ds,hu₂.trans hu₁,Nat.add_le_add hm₁ hm₂,
    Exec.seq he₁ he₂,hleftFinal,hrightFinal,?_,?_,?_,?_⟩
  · simp [hsep]
  · simp
  · intro k hkL hkR; exact (hframe k hkL hkR).1
  · intro k hkL hkR hl hr
    exact ⟨(hmaskFrame k hl hr).1.trans (hframe k hkL hkR).1,
      (hmaskFrame k hl hr).2.trans (hframe k hkL hkR).2⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
