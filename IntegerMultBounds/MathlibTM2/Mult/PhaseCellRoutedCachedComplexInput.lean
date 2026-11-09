module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareCachedComplexInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellMovePrefix
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoreGatherRows

/-! Consume one contiguous batch from shared class exposure. Ambient input is
not scanned again; only this batch moves into the ordinary cached-input producer. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {s T Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

/-- The actual shared exposure stream is the ordered list of input batches
consumed by a structural scan over the computed core indices. -/
theorem coreSupplierStream_batches (width radius L W : ℕ) (Fs : List (ZMod s → GaussianInt)) :
    coreSupplierStream A width radius L W Fs =
      (IntegerMultBounds.NLogN.PhaseCellMatrix.coreGatherIndices s width radius L).flatMap
        (fun k => cstream A W (Fs.map (packedInterval
          (IntegerMultBounds.NLogN.PhaseCellMatrix.coreStart width k-radius) L)).flatten) := by
  let jobs := IntegerMultBounds.NLogN.PhaseCellMatrix.coreGatherIndices s width radius L
  let batch := fun k => cstream A W (Fs.map (packedInterval
    (IntegerMultBounds.NLogN.PhaseCellMatrix.coreStart width k-radius) L)).flatten
  have hh := congrArg (List.map batch) (List.ofFn_get jobs)
  simpa only [List.map_ofFn,Function.comp_def,List.get_eq_getElem,List.flatMap_def,coreSupplierStream,jobs,batch] using
    congrArg List.flatten hh

/-- Fitting movement classes do not wrap, so their second cyclic payload is
empty and their first payload is exactly the shared exposure batch. -/
theorem coreGather_cyclic_partition (width radius L k : ℕ)
    (hk : k ∈ IntegerMultBounds.NLogN.PhaseCellMatrix.coreGatherIndices s width radius L) :
    min L (s-(IntegerMultBounds.NLogN.PhaseCellMatrix.coreStart width k-radius)) = L ∧
      L-min L (s-(IntegerMultBounds.NLogN.PhaseCellMatrix.coreStart width k-radius)) = 0 := by
  obtain ⟨hl,hr,hlen⟩ := IntegerMultBounds.NLogN.PhaseCellMatrix.coreGatherIndices_spec s width radius L k hk
  have hfit : L ≤ s-(IntegerMultBounds.NLogN.PhaseCellMatrix.coreStart width k-radius) := by omega
  simp [Nat.min_eq_left hfit]

def routedCachedComplexInput (source work : Fin 392 → Fin T) (count src saved tmp : Fin T) : Pr P T Q A U :=
  .seq (movePrefix count src (work 124) saved tmp) (ordinaryCachedComplexInput source work tmp)

/-- The routed class prefix is consumed exactly once. The remaining class
archive survives below it, while the numerical bank becomes physically ready. -/
theorem routedCachedComplexInput_exec (hA : 4 ≤ A) (H : ReplicaHaloProblem s) (W : ℕ)
    (Fs : List (ZMod s → GaussianInt))
    (hfields : H.Fs = recoveryInputFields H.p H.precision (complexComponentFields Fs))
    (hpq : H.p+1 ≤ H.precision) (hW : H.wordWidth ≤ W)
    (source work : Fin 392 → Fin T) (hwork : Function.Injective work)
    (count src saved tmp : Fin T) (hreg : [count,src,work 124,saved,tmp].Nodup)
    (hsourceOff : ∀ i j, source i ≠ work j) (hsourceTmp : ∀ i, source i ≠ tmp)
    (hworkTmp : ∀ i, work i ≠ tmp) (hsrcOff : ∀ i, src ≠ work i)
    (hsourceSrc : ∀ i, source i ≠ src)
    (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A+4)))
    (hvalues : ∀ i ∈ recoverySeedHeaderPorts,
      (S.R (source i)).length = recoverySeedHeader H W Fs.length i)
    (hblank : ∀ i, S.R (work i) = []) (hleft : ∀ i, S.L (work i) = [])
    (hsrc : S.R src = cstream A W (Fs.map (packedInterval H.origin H.span)).flatten++tail)
    (hcount : (S.R count).length = Fs.length*H.span*W)
    (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    let cost := copyUnaryHeadersCost (fun k => (S.R k).length) (recoverySeedHeaderCopies source work)
    ∃ v' G steps, v'.user = v.user ∧
      steps ≤ (6*(Fs.length*H.span*W)+6)+
        (cost+completeComplexRecoveryHeadersCost H Fs.length+prepareCachedComplexInputCost H W Fs.length) ∧
      Exec body (routedCachedComplexInput source work count src saved tmp) (mk v S) steps (mk v' G) ∧
      CachedReplicaPassInput H (CachedReplicaPassPlacement.standard.reindex
        (work ∘ Fin.castLE (by decide : 300 ≤ 392)) (hwork.comp (Fin.castLE_injective _)))
        (generatedRecoveryBuffers H S.inp S.out) G ∧ G.R src = tail ∧
      (∀ i : Fin 392, 300 ≤ i.val → G.L (work i) = [] ∧ G.R (work i) = []) ∧
      G.L src = S.L src ∧
      (∀ k, k ≠ src → (∀ i, work i ≠ k) → G.L k = S.L k ∧ G.R k = S.R k) := by
  dsimp only
  let payload := cstream A W (Fs.map (packedInterval H.origin H.span)).flatten
  have hlen : payload.length = Fs.length*H.span*W := by
    simp only [payload,length_cstream]
    rw [packedBatch_length H.origin H.span Fs H.span_fit]
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := movePrefix_exec (body := body) hreg payload tail v S hsrc
    (by rw [hlen]; exact hcount) hsaved htmp
  let F : Stacks T A := {S with R := (Function.update (Function.update S.R src tail)
    (work 124) (payload++S.R (work 124)))}
  have hsource (i : Fin 392) : F.R (source i) = S.R (source i) := by
    simp only [F,Function.update_of_ne (hsourceOff i 124),Function.update_of_ne (hsourceSrc i)]
  have hcopy : copyUnaryHeadersCost (fun k => (F.R k).length) (recoverySeedHeaderCopies source work) =
      copyUnaryHeadersCost (fun k => (S.R k).length) (recoverySeedHeaderCopies source work) := by
    unfold copyUnaryHeadersCost recoverySeedHeaderCopies
    simp only [List.map_map,Function.comp_def,hsource]
  obtain ⟨v₂,G,n₂,hu₂,hn₂,he₂,hready,hscratch,hframe⟩ := ordinaryCachedComplexInput_exec
    (body := body) hA H W Fs hfields hpq hW source work hwork tmp hsourceOff hsourceTmp hworkTmp v₁ F
    (by intro i hi; rw [hsource]; exact hvalues i hi)
    (by intro i hi; simp [F,Function.update_of_ne (fun he => hi (hwork he)),(hsrcOff i).symm,hblank])
    hleft (by simp [F,hblank,payload]) (by simp [F,(hworkTmp 124).symm,(show tmp ≠ src from Ne.symm (by assumption)),htmp])
  rw [hcopy] at hn₂
  refine ⟨v₂,G,(6*payload.length+6)+n₂,hu₂.trans hu₁,?_,Exec.seq he₁ he₂,hready,?_,hscratch,(hframe src (fun i => (hsrcOff i).symm)).1,?_⟩
  · rw [hlen]; exact Nat.add_le_add (le_refl _) hn₂
  · rw [(hframe src (fun i => (hsrcOff i).symm)).2]
    simp [F,(hsrcOff 124)]
  · intro k hk hoff
    refine ⟨(hframe k hoff).1,?_⟩
    simpa only [F,Function.update_of_ne (hoff 124).symm,Function.update_of_ne hk] using (hframe k hoff).2

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
