module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedReplicaPass

/-! Execute two disjoint cached interior/residual passes. Their input and output
contracts are transported by the tape frame, not re-established per replica. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

noncomputable def cachedReplicaPassPair (left right : CachedReplicaPassPlacement T)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  .seq (cachedReplicaPass left hR hQ) (cachedReplicaPass right hR hQ)

theorem cachedReplicaPassPair_exec (H K : ReplicaHaloProblem s)
    (left right : CachedReplicaPassPlacement T)
    (hdisjoint : ∀ k, left.Owns k → ¬right.Owns k)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (hspanH : H.span+H.band ≤ s) (horiginH : H.origin < s)
    (hpadH : 2*((s/(H.t-s)+1)-2*H.band) ≤ 2^H.l+1)
    (hpH : 2 ≤ H.p) (hwidthH : 8*H.p ≤ 2^H.u)
    (hspanK : K.span+K.band ≤ s) (horiginK : K.origin < s)
    (hpadK : 2*((s/(K.t-s)+1)-2*K.band) ≤ 2^K.l+1)
    (hpK : 2 ≤ K.p) (hwidthK : 8*K.p ≤ 2^K.u)
    (leftBuffers rightBuffers : ReplicaLoopBuffers A) (v : HS T Q A U) (S : Stacks T A)
    (leftInputs : CachedReplicaPassInput H left leftBuffers S)
    (rightInputs : CachedReplicaPassInput K right rightBuffers S) :
    ∃ vf mid F m, ∃ Cs Ds : List (ZMod s → GaussianInt),
      vf.user = v.user ∧ m ≤ cachedReplicaPassCost H+cachedReplicaPassCost K ∧
      Exec body (cachedReplicaPassPair left right hR hQ) (mk v S) m (mk vf F) ∧
      CachedReplicaPassPost H left leftBuffers S F Cs ∧
      CachedReplicaPassPost K right rightBuffers mid F Ds ∧
      mid.inp = S.inp ∧ mid.out = S.out ∧
      (∀ k, right.Owns k → mid.L k = S.L k ∧ mid.R k = S.R k) ∧
      ∀ k, ¬left.Owns k → ¬right.Owns k → F.L k = S.L k ∧ F.R k = S.R k := by
  obtain ⟨v₁,mid,m₁,Cs,hu₁,hm₁,he₁,hleft,hframe₁⟩ := cachedReplicaPass_exec (body := body)
    H left hR hQ hA hspanH horiginH hpadH hpH hwidthH leftBuffers v S leftInputs
  have hrightFrame (k : Fin T) (hk : right.Owns k) : mid.L k = S.L k ∧ mid.R k = S.R k := by
    apply hframe₁ k
    intro hleft
    exact hdisjoint k hleft hk
  have hrightInputs : CachedReplicaPassInput K right rightBuffers mid :=
    rightInputs.of_frame hleft.input hleft.outputStream hrightFrame
  obtain ⟨vf,F,m₂,Ds,hu₂,hm₂,he₂,hright,hframe₂⟩ := cachedReplicaPass_exec (body := body)
    K right hR hQ hA hspanK horiginK hpadK hpK hwidthK rightBuffers v₁ mid hrightInputs
  have hleftFinal : CachedReplicaPassPost H left leftBuffers S F Cs :=
    hleft.of_frame hright.input hright.outputStream (fun k hk => hframe₂ k (hdisjoint k hk))
  refine ⟨vf,mid,F,m₁+m₂,Cs,Ds,hu₂.trans hu₁,Nat.add_le_add hm₁ hm₂,
    Exec.seq he₁ he₂,hleftFinal,hright,hleft.input,hleft.outputStream,hrightFrame,?_⟩
  intro k hkL hkR
  exact ⟨(hframe₂ k hkR).1.trans (hframe₁ k hkL).1,
    (hframe₂ k hkR).2.trans (hframe₁ k hkL).2⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
