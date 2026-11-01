module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryBatchPlacement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaHaloProblem
public import IntegerMultBounds.MathlibTM2.Host.RegisterBankStock

/-! Ordinary headers and one packed RHS archive initialize the physical caller.
The factor, numerical and recovery banks start empty. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {U : Type}

def generatedRecoveryHeader (H : ReplicaHaloProblem s) (k : Fin 126) : ℕ :=
  if k = 111 then H.origin else if k = 113 then H.origin+H.span else
  if k = 115 then H.metadataWidth else if k = 123 then H.span*H.wordWidth else
    replicaFactoryHeaderValue (2^15*H.p) (H.stage+1) H.precision H.l s H.t H.u H.band H.Fs.length 0 0 H.wordWidth k

noncomputable def generatedRecoveryInput (H : ReplicaHaloProblem s)
    (inp : List (Bool ⊕ Bool)) (out : List Bool) : Stacks 392 A :=
  ⟨inp,out,fun _ => [],fun k =>
    if k = 124 then H.Fs.flatMap (fun F => cstream A H.wordWidth (packedInterval H.origin H.span F)) else
    if k = 390 then List.replicate H.Fs.length tick else
    if hk : k.val < 126 then List.replicate (generatedRecoveryHeader H ⟨k.val,hk⟩) tick else []⟩

noncomputable def generatedRecoveryBuffers (H : ReplicaHaloProblem s)
    (inp : List (Bool ⊕ Bool)) (out : List Bool) : ReplicaLoopBuffers A :=
  ⟨embStk replicaRecoveryBatchInterior.gather (generatedRecoveryInput H inp out),[],[],[],[],[],[],inp,out⟩

theorem generatedRecoveryInput_gather (H : ReplicaHaloProblem s) (inp : List (Bool ⊕ Bool)) (out : List Bool)
    (k : Fin 126) (hk : k ≠ 124) :
    (generatedRecoveryInput (A := A) H inp out).R (replicaRecoveryBatchInterior.gather k) =
      List.replicate (generatedRecoveryHeader H k) tick := by
  have hval : replicaRecoveryBatchInterior.gather k = Fin.castLE (by decide : 126 ≤ 392) k := rfl
  rw [hval]
  have h124 : k.val ≠ 124 := fun he => hk (Fin.ext he)
  simp [generatedRecoveryInput,Fin.ext_iff,h124,k.isLt,show k.val ≠ 390 by have := k.isLt; omega]

theorem generatedRecoveryInput_off (H : ReplicaHaloProblem s) (inp : List (Bool ⊕ Bool)) (out : List Bool)
    (k : Fin 392) (hk : 126 ≤ k.val) (h390 : k ≠ 390) :
    (generatedRecoveryInput (A := A) H inp out).R k = [] := by
  have h124 : k ≠ 124 := by intro he; subst k; norm_num at hk
  simp [generatedRecoveryInput,h124,h390,show ¬k.val < 126 by omega]

theorem generatedRecoveryInput_count (H : ReplicaHaloProblem s) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    ((generatedRecoveryInput (A := A) H inp out).R 390).length = H.Fs.length := by
  simp [generatedRecoveryInput]

theorem generatedRecoveryInput_headers (H : ReplicaHaloProblem s) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    ReplicaLoopHeaders H replicaRecoveryBatchInterior.gather (generatedRecoveryBuffers H inp out)
      (generatedRecoveryInput (A := A) H inp out) := by
  constructor
  · intro r hr h102 h116
    simp only [replicaFactoryHeaderCopies,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | contradiction | (rw [generatedRecoveryInput_gather H inp out _ (by decide)]; simp [generatedRecoveryHeader])
  · rw [generatedRecoveryInput_gather H inp out 111 (by decide)]; simp [generatedRecoveryHeader]
  · rw [generatedRecoveryInput_gather H inp out 113 (by decide)]; simp [generatedRecoveryHeader]
  · rw [generatedRecoveryInput_gather H inp out 115 (by decide)]; simp [generatedRecoveryHeader]
  · rw [generatedRecoveryInput_gather H inp out 123 (by decide)]; simp [generatedRecoveryHeader]
  · change (generatedRecoveryInput (A := A) H inp out).R 124 = _
    simp [generatedRecoveryInput,generatedRecoveryBuffers]
  · intro k hk
    rw [generatedRecoveryInput_gather H inp out k (by intro he; subst k; norm_num at hk)]
    have hz : generatedRecoveryHeader H k = 0 := by
      simp [generatedRecoveryHeader,replicaFactoryHeaderValue,Fin.ext_iff,
        show k.val ≠ 111 by omega,show k.val ≠ 113 by omega,show k.val ≠ 115 by omega,show k.val ≠ 123 by omega,
        show k.val ≠ 114 by omega,show k.val ≠ 101 by omega,show k.val ≠ 112 by omega,show k.val ≠ 108 by omega,
        show k.val ≠ 97 by omega,show k.val ≠ 98 by omega,show k.val ≠ 99 by omega,show k.val ≠ 100 by omega,
        show k.val ≠ 102 by omega,show k.val ≠ 121 by omega,show k.val ≠ 116 by omega,show k.val ≠ 94 by omega]
    simp [hz]
  · intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals rw [generatedRecoveryInput_gather H inp out _ (by decide)]
    all_goals simp [generatedRecoveryHeader,replicaFactoryHeaderValue]

def generatedRecoveryHeaderStock (H : ReplicaHaloProblem s) : ℕ :=
  2^15*H.p+(H.stage+1)+H.precision+H.l+s+H.t+H.u+H.band+H.Fs.length+H.wordWidth+
    H.origin+(H.origin+H.span)+H.metadataWidth+H.span*H.wordWidth

private theorem choice_le {p : Prop} [Decidable p] {a b c : ℕ}
    (ha : a ≤ c) (hb : b ≤ c) : (if p then a else b) ≤ c := by
  split <;> assumption

private theorem recoveryHeader_le_sum (P stage q l s t u band N w origin endpoint V volume : ℕ) (k : Fin 126) :
    (if k = 111 then origin else if k = 113 then endpoint else
      if k = 115 then V else if k = 123 then volume else
        replicaFactoryHeaderValue P stage q l s t u band N 0 0 w k) ≤
      P+stage+q+l+s+t+u+band+N+w+origin+endpoint+V+volume := by
  unfold replicaFactoryHeaderValue
  repeat' apply choice_le
  all_goals omega

theorem generatedRecoveryHeader_le_stock (H : ReplicaHaloProblem s) (k : Fin 126) :
    generatedRecoveryHeader H k ≤ generatedRecoveryHeaderStock H :=
  recoveryHeader_le_sum _ _ _ _ _ _ _ _ _ _ _ _ _ _ k

def generatedRecoveryInputStock (H : ReplicaHaloProblem s) (inp : List (Bool ⊕ Bool)) (out : List Bool) : ℕ :=
  inp.length+out.length+392*generatedRecoveryHeaderStock H+H.Fs.length*(H.span*H.wordWidth)

theorem generatedRecoveryInput_stock_le (H : ReplicaHaloProblem s) (inp : List (Bool ⊕ Bool)) (out : List Bool)
    (v : HS 392 Q A U) :
    mnSize (mk v (generatedRecoveryInput (A := A) H inp out)) ≤
      generatedRecoveryInputStock H inp out := by
  have hlen : (H.Fs.flatMap (fun F => cstream A H.wordWidth (packedInterval H.origin H.span F))).length =
      H.Fs.length*(H.span*H.wordWidth) := by
    simp [List.length_flatMap,length_cstream,packedInterval_length _ H.span_fit,
      List.map_const',List.sum_replicate,smul_eq_mul]
  have hR (k : Fin 392) : ((generatedRecoveryInput (A := A) H inp out).R k).length ≤
      generatedRecoveryHeaderStock H+if k = 124 then H.Fs.length*(H.span*H.wordWidth) else 0 := by
    by_cases h124 : k = 124
    · simp only [generatedRecoveryInput,h124,ite_true,hlen]
      omega
    · by_cases h390 : k = 390
      · subst k
        simp only [generatedRecoveryInput,show (390 : Fin 392) ≠ 124 by decide,ite_false,ite_true,
          List.length_replicate,Nat.add_zero]
        unfold generatedRecoveryHeaderStock
        omega
      · by_cases hk : k.val < 126
        · simpa only [generatedRecoveryInput,if_neg h124,if_neg h390,dif_pos hk,
            List.length_replicate,Nat.add_zero] using generatedRecoveryHeader_le_stock H ⟨k.val,hk⟩
        · simp [generatedRecoveryInput,h124,h390,hk]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun k _ => hR k)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true] at hsum
  rw [mnSize_mk_registerBankStock,registerBankStock_eq_right_sum _ (by intro i; rfl)]
  change inp.length+out.length+_ ≤ inp.length+out.length+392*generatedRecoveryHeaderStock H+H.Fs.length*(H.span*H.wordWidth)
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
