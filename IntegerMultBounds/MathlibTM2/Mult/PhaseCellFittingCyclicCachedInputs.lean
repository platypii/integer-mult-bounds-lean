module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRoutedCachedComplexInput

/-! One routed batch prepares both cyclic cached banks. The cyclic bank is
injected into the caller so remaining class input and scalar seeds can live
outside factor space, which is reused after conversion scratch is released. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
open CyclicReplicaPlacement
variable {s T Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

private theorem reindex_comp {m n r : ℕ} (job : CachedReplicaPassPlacement m)
    (e : Fin m → Fin n) (he : Function.Injective e) (f : Fin n → Fin r) (hf : Function.Injective f) :
    (job.reindex e he).reindex f hf = job.reindex (f ∘ e) (hf.comp he) := by
  rfl

private theorem reindex_congr {m n : ℕ} (job : CachedReplicaPassPlacement m)
    (e f : Fin m → Fin n) (he : Function.Injective e) (hf : Function.Injective f) (h : e = f) :
    job.reindex e he = job.reindex f hf := by
  subst f
  rfl

def fittingCyclicCachedInputs (bank : Fin 834 → Fin T) (sourceL sourceR : Fin 392 → Fin T)
    (count src saved tmp : Fin T) : Pr P T Q A U :=
  .seq (routedCachedComplexInput sourceL (bank ∘ leftInputReg) count src saved tmp)
    (ordinaryCachedComplexInput sourceR (bank ∘ rightInputReg) tmp)

/-- Both cached inputs execute from one routed complex batch and ordinary
seed headers. The remaining class archive stays outside the cyclic bank. -/
theorem fittingCyclicCachedInputs_exec (bank : Fin 834 → Fin T) (hbank : Function.Injective bank)
    (hA : 4 ≤ A) (H K : ReplicaHaloProblem s) (W : ℕ) (Fs : List (ZMod s → GaussianInt))
    (hfieldsL : H.Fs = recoveryInputFields H.p H.precision (complexComponentFields Fs))
    (hfieldsR : K.Fs = recoveryInputFields K.p K.precision (complexComponentFields Fs))
    (hpqL : H.p+1 ≤ H.precision) (hpqR : K.p+1 ≤ K.precision)
    (hWL : H.wordWidth ≤ W) (hWR : K.wordWidth ≤ W) (hspanR : K.span = 0)
    (sourceL sourceR : Fin 392 → Fin T) (count src saved tmp : Fin T)
    (hreg : [count,src,bank (leftInputReg 124),saved,tmp].Nodup)
    (hsourceOff : ∀ i j, sourceL i ≠ bank j ∧ sourceR i ≠ bank j)
    (hsourceTmp : ∀ i, sourceL i ≠ tmp ∧ sourceR i ≠ tmp)
    (htmpOff : ∀ i, bank i ≠ tmp) (hsrcOff : ∀ i, src ≠ bank i)
    (hsourceSrc : ∀ i, sourceL i ≠ src ∧ sourceR i ≠ src)
    (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A+4)))
    (hvaluesL : ∀ i ∈ recoverySeedHeaderPorts,
      (S.R (sourceL i)).length = recoverySeedHeader H W Fs.length i)
    (hvaluesR : ∀ i ∈ recoverySeedHeaderPorts,
      (S.R (sourceR i)).length = recoverySeedHeader K W Fs.length i)
    (hblank : ∀ i, S.R (bank i) = []) (hleft : ∀ i, S.L (bank i) = [])
    (hsrc : S.R src = cstream A W (Fs.map (packedInterval H.origin H.span)).flatten++tail)
    (hcount : (S.R count).length = Fs.length*H.span*W)
    (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    let copiesL := copyUnaryHeadersCost (fun k => (S.R k).length)
      (recoverySeedHeaderCopies sourceL (bank ∘ leftInputReg))
    let copiesR := copyUnaryHeadersCost (fun k => (S.R k).length)
      (recoverySeedHeaderCopies sourceR (bank ∘ rightInputReg))
    ∃ v' G steps, v'.user = v.user ∧
      steps ≤ ((6*(Fs.length*H.span*W)+6)+
        (copiesL+completeComplexRecoveryHeadersCost H Fs.length+prepareCachedComplexInputCost H W Fs.length))+
        (copiesR+completeComplexRecoveryHeadersCost K Fs.length+prepareCachedComplexInputCost K W Fs.length) ∧
      Exec body (fittingCyclicCachedInputs bank sourceL sourceR count src saved tmp) (mk v S) steps (mk v' G) ∧
      CachedReplicaPassInput H (left.reindex bank hbank) (generatedRecoveryBuffers H S.inp S.out) G ∧
      CachedReplicaPassInput K (right.reindex bank hbank) (generatedRecoveryBuffers K S.inp S.out) G ∧
      G.R src = tail ∧
      (∀ i : Fin 234, G.L (bank (factorReg i)) = [] ∧ G.R (bank (factorReg i)) = []) ∧
      (∀ k, k ≠ src → (∀ i, bank i ≠ k) → G.L k = S.L k ∧ G.R k = S.R k) := by
  dsimp only
  obtain ⟨v₁,F,n₁,hu₁,hn₁,he₁,hl,hsrc',hscratchL,hframeL⟩ := routedCachedComplexInput_exec
    (body := body) hA H W Fs hfieldsL hpqL hWL sourceL (bank ∘ leftInputReg)
    (hbank.comp leftInputReg_injective) count src saved tmp hreg
    (fun i j => (hsourceOff i _).1) (fun i => (hsourceTmp i).1)
    (fun i => htmpOff _) (fun i => hsrcOff _) (fun i => (hsourceSrc i).1) v S tail
    hvaluesL (fun i => hblank _) (fun i => hleft _) hsrc hcount hsaved htmp
  have hfresh (j : Fin 392) : F.L (bank (rightInputReg j)) = [] ∧ F.R (bank (rightInputReg j)) = [] := by
    by_cases hj : j.val < 300
    · let i : Fin 300 := ⟨j.val,hj⟩
      have hview : rightInputReg j = rightReg i := rfl
      rw [hview]
      have hf := hframeL (bank (rightReg i)) (hsrcOff _).symm
        (fun k h => leftInputReg_right_disjoint k i (hbank h))
      exact ⟨hf.1.trans (hleft _),hf.2.trans (hblank _)⟩
    · have heq : leftInputReg j = rightInputReg j := by
        apply Fin.ext
        simp [leftInputReg,rightInputReg,hj]
      rw [←heq]
      exact hscratchL j (by omega)
  have hR (i : Fin 392) : F.R (sourceR i) = S.R (sourceR i) :=
    (hframeL _ (hsourceSrc i).2 (fun j => (hsourceOff i _).2.symm)).2
  have htmp' : F.R tmp = [] := by
    have hr := hreg
    regs_ne hr
    rw [(hframeL tmp (show tmp ≠ src from Ne.symm (by assumption)) (fun i => htmpOff _)).2]
    exact htmp
  have hpayload : F.R (bank (rightInputReg 124)) =
      cstream A W (Fs.map (packedInterval K.origin K.span)).flatten := by
    rw [(hfresh 124).2,hspanR]
    simp [packedInterval,cstream]
  obtain ⟨v₂,G,n₂,hu₂,hn₂,he₂,hr,hscratchR,hframeR⟩ := ordinaryCachedComplexInput_exec
    (body := body) hA K W Fs hfieldsR hpqR hWR sourceR (bank ∘ rightInputReg)
    (hbank.comp rightInputReg_injective) tmp (fun i j => (hsourceOff i _).2)
    (fun i => (hsourceTmp i).2) (fun i => htmpOff _) v₁ F
    (by intro i hi; rw [hR]; exact hvaluesR i hi)
    (fun i _ => (hfresh i).2) (fun i => (hfresh i).1) hpayload htmp'
  have hcopy : copyUnaryHeadersCost (fun k => (F.R k).length)
      (recoverySeedHeaderCopies sourceR (bank ∘ rightInputReg)) =
      copyUnaryHeadersCost (fun k => (S.R k).length)
        (recoverySeedHeaderCopies sourceR (bank ∘ rightInputReg)) := by
    unfold copyUnaryHeadersCost recoverySeedHeaderCopies
    simp only [List.map_map,Function.comp_def,hR]
  rw [hcopy] at hn₂
  have heq : (bank ∘ leftInputReg) ∘ Fin.castLE (by decide : 300 ≤ 392) = bank ∘ leftReg :=
    funext (fun i => congrArg bank (leftInputReg_cached i))
  have hl' : CachedReplicaPassInput H (left.reindex bank hbank) (generatedRecoveryBuffers H S.inp S.out) F := by
    rw [left,reindex_comp]
    rw [reindex_congr _ _ _ _ (hbank.comp leftReg_injective) heq] at hl
    exact hl
  have hin : F.inp = S.inp := hl'.input
  have hout : F.out = S.out := hl'.outputStream
  have hr' : CachedReplicaPassInput K (right.reindex bank hbank) (generatedRecoveryBuffers K S.inp S.out) G := by
    rw [right,reindex_comp]
    rw [hin,hout] at hr
    exact hr
  refine ⟨v₂,G,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,Exec.seq he₁ he₂,?_,hr',?_,?_,?_⟩
  · apply hl'.of_frame (hr'.input.trans hin.symm) (hr'.outputStream.trans hout.symm)
    intro k hk
    obtain ⟨i,hi⟩ := CachedReplicaPassPlacement.reindex_source _ (bank ∘ leftReg)
      (hbank.comp leftReg_injective) (by simpa only [left,reindex_comp] using hk)
    subst k
    exact hframeR _ (fun j h => rightInputReg_left_disjoint j i (hbank h))
  · rw [(hframeR src (fun i => (hsrcOff _).symm)).2,hsrc']
  · intro i
    by_cases hi : i.val < 92
    · let j : Fin 392 := ⟨300+i.val,by omega⟩
      have heq : rightInputReg j = factorReg i := by
        apply Fin.ext
        change 300+(300+i.val) = 600+i.val
        omega
      simpa only [Function.comp_apply,heq] using hscratchR j (by dsimp only [j]; omega)
    · have hLoff (j : Fin 392) : (bank ∘ leftInputReg) j ≠ bank (factorReg i) := by
        intro he
        have hv := congrArg Fin.val (hbank he)
        change (if j.val < 300 then j.val else 300+j.val) = 600+i.val at hv
        have := j.isLt
        split_ifs at hv <;> omega
      have hRoff (j : Fin 392) : (bank ∘ rightInputReg) j ≠ bank (factorReg i) := by
        intro he
        have hv := congrArg Fin.val (hbank he)
        change 300+j.val = 600+i.val at hv
        have := j.isLt
        omega
      have hf₁ := hframeL _ (hsrcOff _).symm hLoff
      have hf₂ := hframeR _ hRoff
      exact ⟨hf₂.1.trans (hf₁.1.trans (hleft _)),hf₂.2.trans (hf₁.2.trans (hblank _))⟩
  · intro k hk hoff
    have h₁ := hframeL k hk (fun i => hoff _)
    have h₂ := hframeR k (fun i => hoff _)
    exact ⟨h₂.1.trans h₁.1,h₂.2.trans h₁.2⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
