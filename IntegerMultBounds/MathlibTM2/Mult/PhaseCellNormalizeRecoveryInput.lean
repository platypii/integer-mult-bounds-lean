module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNormalizedRecoveryFields
public import IntegerMultBounds.MathlibTM2.Host.ClosedProgramStock

/-! Normalize an ordinary packed input directly in the cached caller bank.
The disposable precision/width headers are retired before factor generation. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {U : Type}

noncomputable def rawRecoveryInput (H : ReplicaHaloProblem s) (W : ℕ)
    (Fs : List (ZMod s → GaussianInt)) (inp : List (Bool ⊕ Bool)) (out : List Bool) : Stacks 392 A :=
  let S := generatedRecoveryInput H inp out
  {S with R := (Function.update (Function.update (Function.update S.R 124
    (cstream A W (Fs.map (packedInterval H.origin H.span)).flatten)) 129 (List.replicate H.p tick))
      130 (List.replicate W tick))}

def normalizeRecoveryInput : Pr Empty 392 Q A U :=
  .seq (preparedPackedInput 112 129 130 94 131 124 132 133 134 135 136)
    (.seq (uclear 129) (uclear 130))

def normalizeRecoveryInputCost (H : ReplicaHaloProblem s) (W N : ℕ) : ℕ :=
  ((4*H.precision+4*H.p+9)+packedInputConversionCost W (2*H.precision+8)
    (H.precision-H.p-1) (N*H.span)+(2*(H.precision-H.p-1)+2))+(2*H.p+2)+(2*W+2)

theorem normalizeRecoveryInput_exec (H : ReplicaHaloProblem s) (W : ℕ)
    (Fs : List (ZMod s → GaussianInt))
    (hfields : H.Fs = recoveryInputFields H.p H.precision Fs)
    (hpq : H.p+1 ≤ H.precision) (hW : H.wordWidth ≤ W)
    (inp : List (Bool ⊕ Bool)) (out : List Bool) (v : HS 392 Q A U) :
    ∃ v', v'.user = v.user ∧
      Exec (fun f : Empty => nomatch f) normalizeRecoveryInput
        (mk v (rawRecoveryInput H W Fs inp out)) (normalizeRecoveryInputCost H W Fs.length)
        (mk v' (generatedRecoveryInput H inp out)) := by
  let I := generatedRecoveryInput (A := A) H inp out
  let S := rawRecoveryInput (A := A) H W Fs inp out
  let xs := (Fs.map (packedInterval H.origin H.span)).flatten
  have hw : H.wordWidth = 2*H.precision+8 := by
    unfold ReplicaHaloProblem.wordWidth ReplicaHaloProblem.precision executionWidth executionPrecision
    omega
  have hhigh (k : Fin 392) (hk : 126 ≤ k.val) (hne : k ≠ 390) : I.R k = [] :=
    generatedRecoveryInput_off H inp out k hk hne
  have hS (k : Fin 392) (h124 : k ≠ 124) (h129 : k ≠ 129) (h130 : k ≠ 130) : S.R k = I.R k := by
    simp only [S,rawRecoveryInput,I,Function.update_of_ne h130,Function.update_of_ne h129,Function.update_of_ne h124]
  obtain ⟨v₁,hu₁,he₁⟩ := preparedPackedInput_exec (body := fun f : Empty => nomatch f)
    (show ([(112 : Fin 392),129,130,94,131,124,132,133,134,135,136]).Nodup by decide)
    H.p H.precision W hpq (by rwa [←hw]) xs v S
    (by rw [hS 112 (by decide) (by decide) (by decide)]
        change (I.R (replicaRecoveryBatchInterior.gather 112)).length = _
        rw [generatedRecoveryInput_gather H inp out 112 (by decide)]
        simp [generatedRecoveryHeader,replicaFactoryHeaderValue])
    (by simp [S,rawRecoveryInput]) (by simp [S,rawRecoveryInput])
    (by rw [hS 94 (by decide) (by decide) (by decide)]
        change (I.R (replicaRecoveryBatchInterior.gather 94)).length = _
        rw [generatedRecoveryInput_gather H inp out 94 (by decide)]
        simp [generatedRecoveryHeader,replicaFactoryHeaderValue,hw])
    (by simp [S,rawRecoveryInput,xs])
    (by rw [hS 131 (by decide) (by decide) (by decide)]; exact hhigh _ (by decide) (by decide))
    (by rw [hS 132 (by decide) (by decide) (by decide)]; exact hhigh _ (by decide) (by decide))
    (by rw [hS 133 (by decide) (by decide) (by decide)]; exact hhigh _ (by decide) (by decide))
    (by rw [hS 134 (by decide) (by decide) (by decide)]; exact hhigh _ (by decide) (by decide))
    (by rw [hS 135 (by decide) (by decide) (by decide)]; exact hhigh _ (by decide) (by decide))
    (by rw [hS 136 (by decide) (by decide) (by decide)]; exact hhigh _ (by decide) (by decide))
  let J : Stacks 392 A := {S with R := (Function.update S.R 124
    (cstream A (2*H.precision+8) (xs.map (fun z => (2 : GaussianInt)^(H.precision-H.p-1)*z))))}
  obtain ⟨v₂,hu₂,he₂⟩ := uclear_exec (fun f : Empty => nomatch f) 129 v₁ J
  have h129 : J.R 129 = List.replicate H.p tick := by simp [J,S,rawRecoveryInput]
  rw [h129,List.length_replicate] at he₂
  let K : Stacks 392 A := {J with R := Function.update J.R 129 []}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (fun f : Empty => nomatch f) 130 v₂ K
  have h130 : K.R 130 = List.replicate W tick := by simp [K,J,S,rawRecoveryInput]
  rw [h130,List.length_replicate] at he₃
  have hpage : cstream A (2*H.precision+8) (xs.map (fun z => (2 : GaussianInt)^(H.precision-H.p-1)*z)) = I.R 124 := by
    rw [←hw]
    change cstream A H.wordWidth (((Fs.map (packedInterval H.origin H.span)).flatten).map _) = _
    rw [recoveryInputFields_packet]
    change _ = H.Fs.flatMap (fun F => cstream A H.wordWidth (packedInterval H.origin H.span F))
    rw [hfields,cstream_flatten,List.flatMap_def]
    simp only [List.map_map,Function.comp_def]
  have hfinal : {K with R := Function.update K.R 130 []} = I := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h124 : k = 124
    · subst k
      simpa [K,J] using hpage
    by_cases h129k : k = 129
    · subst k; simp [K,hhigh 129 (by decide) (by decide)]
    by_cases h130k : k = 130
    · subst k; simp [hhigh 130 (by decide) (by decide)]
    simp only [K,J,Function.update_of_ne h130k,Function.update_of_ne h129k,Function.update_of_ne h124]
    exact hS k h124 h129k h130k
  have hlen : xs.length = Fs.length*H.span := packedBatch_length H.origin H.span Fs H.span_fit
  refine ⟨v₃,hu₃.trans (hu₂.trans hu₁),?_⟩
  have he := Exec.seq he₁ (Exec.seq he₂ he₃)
  rw [hfinal] at he
  simpa only [normalizeRecoveryInput,normalizeRecoveryInputCost,hlen,Nat.add_assoc] using he

@[irreducible] noncomputable def normalizeRecoveryInputPush : ℕ :=
  mnProgPush (normalizeRecoveryInput (Q := Q) (A := A) (U := U))

theorem normalizeRecoveryInput_exec_within (H : ReplicaHaloProblem s) (W : ℕ)
    (Fs : List (ZMod s → GaussianInt))
    (hfields : H.Fs = recoveryInputFields H.p H.precision Fs)
    (hpq : H.p+1 ≤ H.precision) (hW : H.wordWidth ≤ W)
    (inp : List (Bool ⊕ Bool)) (out : List Bool) (v : HS 392 Q A U) :
    ∃ v', v'.user = v.user ∧ ∀ depth,
      ExecWithin (fun f : Empty => nomatch f)
        (fun d z => mnSize z+d ≤ mnSize (mk v (rawRecoveryInput H W Fs inp out))+depth+
          normalizeRecoveryInputPush (Q := Q) (A := A) (U := U)*normalizeRecoveryInputCost H W Fs.length)
        depth normalizeRecoveryInput (mk v (rawRecoveryInput H W Fs inp out))
        (normalizeRecoveryInputCost H W Fs.length) (mk v' (generatedRecoveryInput H inp out)) := by
  obtain ⟨v',hu,he⟩ := normalizeRecoveryInput_exec H W Fs hfields hpq hW inp out v
  refine ⟨v',hu,?_⟩
  intro depth
  apply mn_native_exec_within he _ (by
    unfold normalizeRecoveryInputPush
    exact WordCmd.empty_native _) depth _ le_rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
