module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedCachedReplicaInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareComplexRecoveryInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareRecoveryHeaders

/-! Reuse complex component expansion and precision conversion, then release the
old replica counter before entering the cached cyclic caller. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {s T Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

namespace CyclicReplicaPlacement

/-- Conversion scratch uses the first 92 factor registers before factor setup.
Both conversions release this range, and neither touches the other cached bank. -/
def leftInputReg (i : Fin 392) : Fin 834 :=
  ⟨if i.val < 300 then i.val else 300+i.val,by have := i.isLt; split_ifs <;> omega⟩

def rightInputReg (i : Fin 392) : Fin 834 := ⟨300+i.val,by have := i.isLt; omega⟩

theorem leftInputReg_injective : Function.Injective leftInputReg := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  change (if i.val < 300 then i.val else 300+i.val) =
    (if j.val < 300 then j.val else 300+j.val) at hv
  split_ifs at hv <;> omega

theorem rightInputReg_injective : Function.Injective rightInputReg := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  change 300+i.val = 300+j.val at hv
  omega

theorem leftInputReg_cached (i : Fin 300) :
    leftInputReg (Fin.castLE (by decide : 300 ≤ 392) i) = leftReg i := by
  apply Fin.ext
  simp [leftInputReg,leftReg,i.isLt]

theorem rightInputReg_cached (i : Fin 300) :
    rightInputReg (Fin.castLE (by decide : 300 ≤ 392) i) = rightReg i := rfl

theorem leftInputReg_right_disjoint (i : Fin 392) (j : Fin 300) :
    leftInputReg i ≠ rightReg j := by
  intro h
  have hv := congrArg Fin.val h
  change (if i.val < 300 then i.val else 300+i.val) = 300+j.val at hv
  have := j.isLt
  split_ifs at hv <;> omega

theorem rightInputReg_left_disjoint (i : Fin 392) (j : Fin 300) :
    rightInputReg i ≠ leftReg j := by
  intro h
  have hv := congrArg Fin.val h
  change 300+i.val = j.val at hv
  have := j.isLt
  omega

end CyclicReplicaPlacement

def prepareCachedComplexInput : Pr Empty 392 Q A U :=
  .seq prepareComplexRecoveryInput (.seq normalizeRecoveryInput (uclear 390))

def prepareCachedComplexInputCost (H : ReplicaHaloProblem s) (W N : ℕ) : ℕ :=
  prepareComplexRecoveryInputCost H.span W N+
    (normalizeRecoveryInputCost H W (2*N)+(2*H.Fs.length+2))

noncomputable def preparedCachedComplexInput (H : ReplicaHaloProblem s)
    (inp : List (Bool ⊕ Bool)) (out : List Bool) : Stacks 392 A :=
  let S := generatedRecoveryInput H inp out
  {S with R := Function.update S.R 390 []}

theorem preparedCachedComplexInput_view (H : ReplicaHaloProblem s)
    (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    embStk (Fin.castLE (by decide : 300 ≤ 392)) (preparedCachedComplexInput (A := A) H inp out) =
      generatedCachedReplicaInput H inp out := by
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  exact Function.update_of_ne (by
    intro he
    have hv := congrArg Fin.val he
    have := i.isLt
    change i.val = 390 at hv
    omega) _ _

theorem preparedCachedComplexInput_scratch (H : ReplicaHaloProblem s)
    (inp : List (Bool ⊕ Bool)) (out : List Bool) (i : Fin 392) (hi : 300 ≤ i.val) :
    (preparedCachedComplexInput (A := A) H inp out).L i = [] ∧
      (preparedCachedComplexInput (A := A) H inp out).R i = [] := by
  refine ⟨rfl,?_⟩
  by_cases he : i = 390
  · subst i; simp [preparedCachedComplexInput]
  · simpa only [preparedCachedComplexInput,Function.update_of_ne he] using
      generatedRecoveryInput_off (A := A) H inp out i (by omega) he

theorem prepareCachedComplexInput_exec (hA : 4 ≤ A) (H : ReplicaHaloProblem s) (W : ℕ)
    (Fs : List (ZMod s → GaussianInt))
    (hfields : H.Fs = recoveryInputFields H.p H.precision (complexComponentFields Fs))
    (hpq : H.p+1 ≤ H.precision) (hW : H.wordWidth ≤ W)
    (inp : List (Bool ⊕ Bool)) (out : List Bool) (v : HS 392 Q A U) :
    ∃ v' steps, v'.user = v.user ∧ steps ≤ prepareCachedComplexInputCost H W Fs.length ∧
      Exec (fun f : Empty => nomatch f) prepareCachedComplexInput
        (mk v (complexRecoveryInput H W Fs inp out)) steps
        (mk v' (preparedCachedComplexInput H inp out)) := by
  have hN : H.Fs.length = 2*Fs.length := by
    rw [hfields,recoveryInputFields_length,complexComponentFields_length]
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := prepareComplexRecoveryInput_exec hA H W Fs hN inp out v
  obtain ⟨v₂,hu₂,he₂⟩ := normalizeRecoveryInput_exec H W (complexComponentFields Fs)
    hfields hpq hW inp out v₁
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (fun f : Empty => nomatch f) 390 v₂ (generatedRecoveryInput H inp out)
  rw [generatedRecoveryInput_count] at he₃
  refine ⟨v₃,n₁+(normalizeRecoveryInputCost H W (complexComponentFields Fs).length+
    (2*H.Fs.length+2)),hu₃.trans (hu₂.trans hu₁),?_,Exec.seq he₁ (Exec.seq he₂ he₃)⟩
  simpa only [prepareCachedComplexInputCost,complexComponentFields_length] using
    Nat.add_le_add_right hn₁ (normalizeRecoveryInputCost H W (complexComponentFields Fs).length+
      (2*H.Fs.length+2))

/-- A placed producer returns cached readiness and releases all of its scratch.
Its frame can preserve the other cyclic bank while the two inputs are prepared. -/
theorem prepareCachedComplexInput_placed_exec (hA : 4 ≤ A) (H : ReplicaHaloProblem s) (W : ℕ)
    (Fs : List (ZMod s → GaussianInt))
    (hfields : H.Fs = recoveryInputFields H.p H.precision (complexComponentFields Fs))
    (hpq : H.p+1 ≤ H.precision) (hW : H.wordWidth ≤ W)
    (e : Fin 392 → Fin T) (he : Function.Injective e) (v : HS T Q A U) (S : Stacks T A)
    (hinput : embStk e S = complexRecoveryInput H W Fs S.inp S.out) :
    ∃ v' G steps, v'.user = v.user ∧ steps ≤ prepareCachedComplexInputCost H W Fs.length ∧
      Exec body (embProg e Empty.elim prepareCachedComplexInput) (mk v S) steps (mk v' G) ∧
      CachedReplicaPassInput H (CachedReplicaPassPlacement.standard.reindex
        (e ∘ Fin.castLE (by decide : 300 ≤ 392)) (he.comp (Fin.castLE_injective _)))
        (generatedRecoveryBuffers H S.inp S.out) G ∧
      (∀ i : Fin 392, 300 ≤ i.val → G.L (e i) = [] ∧ G.R (e i) = []) ∧
      (∀ k, (∀ i, e i ≠ k) → G.L k = S.L k ∧ G.R k = S.R k) := by
  obtain ⟨vf,n,hu,hn,hex⟩ := prepareCachedComplexInput_exec hA H W Fs hfields hpq hW S.inp S.out (embDn e v)
  obtain ⟨v',G,hex',hv',hu',hbank,hframe⟩ := exec_emb (ι := Empty.elim) (body' := body)
    he (fun f => nomatch f) hex v rfl S hinput
  refine ⟨v',G,n,hu'.trans hu,hn,hex',?_,?_,hframe⟩
  · apply (generatedCachedReplicaInput_ready H S.inp S.out).of_reindex_view
    have hh := congrArg (embStk (Fin.castLE (by decide : 300 ≤ 392))) hbank
    exact hh.trans (preparedCachedComplexInput_view H S.inp S.out)
  · intro i hi
    have hL := congrArg (fun B : Stacks 392 A => B.L i) hbank
    have hR := congrArg (fun B : Stacks 392 A => B.R i) hbank
    exact ⟨hL.trans (preparedCachedComplexInput_scratch H S.inp S.out i hi).1,
      hR.trans (preparedCachedComplexInput_scratch H S.inp S.out i hi).2⟩

def ordinaryCachedComplexInput (source work : Fin 392 → Fin T) (tmp : Fin T) : Pr P T Q A U :=
  .seq (prepareRecoveryHeaders source work tmp) (embProg work Empty.elim prepareCachedComplexInput)

/-- Ordinary seed headers and a complex interval archive suffice: derived
headers, component expansion, normalization and scratch retirement all execute. -/
theorem ordinaryCachedComplexInput_exec (hA : 4 ≤ A) (H : ReplicaHaloProblem s) (W : ℕ)
    (Fs : List (ZMod s → GaussianInt))
    (hfields : H.Fs = recoveryInputFields H.p H.precision (complexComponentFields Fs))
    (hpq : H.p+1 ≤ H.precision) (hW : H.wordWidth ≤ W)
    (source work : Fin 392 → Fin T) (hwork : Function.Injective work) (tmp : Fin T)
    (hsourceOff : ∀ i j, source i ≠ work j) (hsourceTmp : ∀ i, source i ≠ tmp)
    (hworkTmp : ∀ i, work i ≠ tmp) (v : HS T Q A U) (S : Stacks T A)
    (hvalues : ∀ i ∈ recoverySeedHeaderPorts,
      (S.R (source i)).length = recoverySeedHeader H W Fs.length i)
    (hblank : ∀ i, i ≠ 124 → S.R (work i) = []) (hleft : ∀ i, S.L (work i) = [])
    (hpayload : S.R (work 124) = cstream A W (Fs.map (packedInterval H.origin H.span)).flatten)
    (htmp : S.R tmp = []) :
    let cost := copyUnaryHeadersCost (fun k => (S.R k).length) (recoverySeedHeaderCopies source work)
    ∃ v' G steps, v'.user = v.user ∧
      steps ≤ cost+completeComplexRecoveryHeadersCost H Fs.length+prepareCachedComplexInputCost H W Fs.length ∧
      Exec body (ordinaryCachedComplexInput source work tmp) (mk v S) steps (mk v' G) ∧
      CachedReplicaPassInput H (CachedReplicaPassPlacement.standard.reindex
        (work ∘ Fin.castLE (by decide : 300 ≤ 392)) (hwork.comp (Fin.castLE_injective _)))
        (generatedRecoveryBuffers H S.inp S.out) G ∧
      (∀ i : Fin 392, 300 ≤ i.val → G.L (work i) = [] ∧ G.R (work i) = []) ∧
      (∀ k, (∀ i, work i ≠ k) → G.L k = S.L k ∧ G.R k = S.R k) := by
  dsimp only
  have hN : H.Fs.length = 2*Fs.length := by
    rw [hfields,recoveryInputFields_length,complexComponentFields_length]
  obtain ⟨v₁,F,n₁,hu₁,hn₁,hinput,hI,hO,hL,hR,he₁,_⟩ := prepareRecoveryHeaders_exec (body := body)
    H W Fs hN source work hwork tmp hsourceOff hsourceTmp hworkTmp v S hvalues hblank hleft hpayload htmp
  have hinput' : embStk work F = complexRecoveryInput H W Fs F.inp F.out := by
    rw [hI,hO]; exact hinput
  obtain ⟨v₂,G,n₂,hu₂,hn₂,he₂,hready,hscratch,hframe⟩ := prepareCachedComplexInput_placed_exec
    (body := body) hA H W Fs hfields hpq hW work hwork v₁ F hinput'
  rw [hI,hO] at hready
  refine ⟨v₂,G,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,Exec.seq he₁ he₂,hready,hscratch,?_⟩
  intro k hk
  exact ⟨(hframe k hk).1.trans (congrFun hL k),
    (hframe k hk).2.trans (hR k (fun i => (hk i).symm))⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
