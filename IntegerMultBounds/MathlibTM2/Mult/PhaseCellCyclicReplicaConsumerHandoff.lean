module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicReplicaConsumerHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicReplicaArchiveHandoff

/-! Install retained masters and move actual residual archives to the Schur
consumer. The two cached banks and original RHS queues remain available. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open CyclicReplicaPlacement
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 834 Q A U}

def cyclicReplicaConsumerHandoff : Pr P 834 Q A U :=
  .seq cyclicReplicaConsumerHeaders cyclicReplicaArchiveHandoff

def cyclicReplicaConsumerState (S : Stacks 834 A) : Stacks 834 A :=
  cyclicReplicaArchiveHandoffState (cyclicReplicaConsumerHeaderState S)

/-- The consumer installation changes only its six owned factor inputs. -/
theorem cyclicReplicaConsumerState_factor_read (S : Stacks 834 A) (j : Fin 234)
    (hj : j ∉ [(130 : Fin 234),168,169,171,172,229]) :
    (cyclicReplicaConsumerState S).R (factorReg j) = S.R (factorReg j) := by
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hj
  have hh := congrArg (fun R => R.R j)
    (cyclicReplicaArchiveHandoff_factor (cyclicReplicaConsumerHeaderState S))
  have hmove : (cyclicReplicaConsumerState S).R (factorReg j) =
      (cyclicReplicaConsumerHeaderState S).R (factorReg j) := by
    simpa only [cyclicReplicaConsumerState,embStk,Function.comp_apply,
      Function.update_of_ne hj.2.2.2.2.1,Function.update_of_ne hj.2.2.1] using hh
  exact hmove.trans (cyclicReplicaConsumerHeaders_read S _
    (fun he => hj.1 (factorReg_injective he))
    (fun he => hj.2.1 (factorReg_injective he))
    (fun he => hj.2.2.2.1 (factorReg_injective he))
    (fun he => hj.2.2.2.2.2 (factorReg_injective he)))

structure CyclicReplicaConsumerPost {s : ℕ} [NeZero s] (H K : ReplicaHaloProblem s)
    (leftBuffers rightBuffers : ReplicaLoopBuffers A) (S F : Stacks 834 A)
    (Cs Ds : List (ZMod s → GaussianInt)) : Prop where
  width : F.R (factorReg 130) = List.replicate H.wordWidth tick
  leftVolume : F.R (factorReg 168) = List.replicate (H.span*H.wordWidth) tick
  rightVolume : F.R (factorReg 171) = List.replicate (K.span*K.wordWidth) tick
  replicas : F.R (factorReg 229) = List.replicate H.Fs.length tick
  leftArchive : F.R (factorReg 169) = Cs.flatMap (fun D => cstream A H.wordWidth (packedInterval H.origin H.span D))
  rightArchive : F.R (factorReg 172) = Ds.flatMap (fun D => cstream A K.wordWidth (packedInterval K.origin K.span D))
  leftBank : embStk left.coupling.bank F = embStk left.coupling.bank S
  rightBank : embStk right.coupling.bank F = embStk right.coupling.bank S
  leftRhs : ReplicaRecoveryRhsHeaders H left.plan.gather leftBuffers F
  rightRhs : ReplicaRecoveryRhsHeaders K right.plan.gather rightBuffers F

theorem cyclicReplicaConsumerHandoff_exec {s : ℕ} [NeZero s] (H K : ReplicaHaloProblem s)
    (leftBuffers rightBuffers : ReplicaLoopBuffers A) (S₀ S₁ : Stacks 834 A)
    (Cs Ds : List (ZMod s → GaussianInt)) (v : HS 834 Q A U) (S : Stacks 834 A)
    (hl : CachedReplicaPassPost H left leftBuffers S₀ S Cs)
    (hr : CachedReplicaPassPost K right rightBuffers S₁ S Ds)
    (hblank : ∀ k ∈ [(130 : Fin 234),168,169,171,172,174,175,229], S.R (factorReg k) = []) :
    let F := cyclicReplicaConsumerState S
    ∃ vf m, vf.user = v.user ∧
      m ≤ (4*(H.Fs.length+H.wordWidth+H.span*H.wordWidth+K.span*K.wordWidth)+17)+
        (4*(H.Fs.length*(H.span*H.wordWidth)+K.Fs.length*(K.span*K.wordWidth))+8) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+0+
        2*(4*(H.Fs.length+H.wordWidth+H.span*H.wordWidth+K.span*K.wordWidth)+17)) 0
        cyclicReplicaConsumerHandoff (mk v S) m (mk vf F) ∧
      CyclicReplicaConsumerPost H K leftBuffers rightBuffers S F Cs Ds := by
  let C := cyclicReplicaConsumerHeaderState S
  obtain ⟨v₁,hu₁,he₁⟩ := cyclicReplicaConsumerHeaders_exec (body := body) v S (hblank 175 (by simp))
  obtain ⟨hwidth,hvolL,hvolR,hcount,hcopyCost⟩ := cyclicReplicaConsumerHeaders_values H K
    leftBuffers rightBuffers S₀ S₁ S Cs Ds hl hr (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> exact hblank _ (by simp))
  have htmp : C.R (factorReg 174) = [] := by
    rw [cyclicReplicaConsumerHeaders_read S _ (by decide) (by decide) (by decide) (by decide)]
    exact hblank 174 (by simp)
  have h169 : C.R (factorReg 169) = [] := by
    rw [cyclicReplicaConsumerHeaders_read S _ (by decide) (by decide) (by decide) (by decide)]
    exact hblank 169 (by simp)
  have h172 : C.R (factorReg 172) = [] := by
    rw [cyclicReplicaConsumerHeaders_read S _ (by decide) (by decide) (by decide) (by decide)]
    exact hblank 172 (by simp)
  have harchL : C.R (left.plan.gather 125) = Cs.flatMap
      (fun D => cstream A H.wordWidth (packedInterval H.origin H.span D)) :=
    (cyclicReplicaConsumerHeaders_frame S _ (Or.inl (.gather 125))).2.trans hl.archive
  have harchR : C.R (right.plan.gather 125) = Ds.flatMap
      (fun D => cstream A K.wordWidth (packedInterval K.origin K.span D)) :=
    (cyclicReplicaConsumerHeaders_frame S _ (Or.inr (.gather 125))).2.trans hr.archive
  have hlenL : (C.R (left.plan.gather 125)).length = H.Fs.length*(H.span*H.wordWidth) := by
    rw [harchL,List.length_flatMap]
    simp only [length_cstream,packedInterval_length _ H.span_fit,List.map_const',List.sum_replicate,hl.length,smul_eq_mul]
  have hlenR : (C.R (right.plan.gather 125)).length = K.Fs.length*(K.span*K.wordWidth) := by
    rw [harchR,List.length_flatMap]
    simp only [length_cstream,packedInterval_length _ K.span_fit,List.map_const',List.sum_replicate,hr.length,smul_eq_mul]
  have heHeaders := mn_native_exec_within he₁ 2
    (copyUnaryHeaders_native (factorReg 175) cyclicReplicaConsumerHeaderCopies) 0 _ (le_refl _)
  rw [hcopyCost] at heHeaders
  obtain ⟨vf,hu₂,he₂⟩ := cyclicReplicaArchiveHandoff_exec_within (body := body) v₁ C htmp
    0 (mnSize (mk v S)+0+2*(4*(H.Fs.length+H.wordWidth+H.span*H.wordWidth+K.span*K.wordWidth)+17))
    heHeaders.final
  have hbankL : embStk left.coupling.bank C = embStk left.coupling.bank S := by
    refine Stacks.ext rfl rfl rfl ?_
    funext i; exact (cyclicReplicaConsumerHeaders_frame S _ (Or.inl (.bank i))).2
  have hbankR : embStk right.coupling.bank C = embStk right.coupling.bank S := by
    refine Stacks.ext rfl rfl rfl ?_
    funext i; exact (cyclicReplicaConsumerHeaders_frame S _ (Or.inr (.bank i))).2
  have hrhsL : ReplicaRecoveryRhsHeaders H left.plan.gather leftBuffers C :=
    ReplicaRecoveryRhsHeaders.of_frame H left.plan.gather leftBuffers S C hl.recoveryRhs
      (fun i => (cyclicReplicaConsumerHeaders_frame S _ (Or.inl (.gather i))).2)
  have hrhsR : ReplicaRecoveryRhsHeaders K right.plan.gather rightBuffers C :=
    ReplicaRecoveryRhsHeaders.of_frame K right.plan.gather rightBuffers S C hr.recoveryRhs
      (fun i => (cyclicReplicaConsumerHeaders_frame S _ (Or.inr (.gather i))).2)
  have hheaders (j : Fin 234) (hj169 : j ≠ 169) (hj172 : j ≠ 172) :
      (cyclicReplicaConsumerState S).R (factorReg j) = C.R (factorReg j) := by
    have hh := congrArg (fun R => R.R j) (cyclicReplicaArchiveHandoff_factor C)
    simpa only [cyclicReplicaConsumerState, C, embStk,Function.comp_apply,Function.update_of_ne hj172,Function.update_of_ne hj169] using hh
  refine ⟨vf,_,hu₂.trans hu₁,?_,ExecWithin.seq heHeaders he₂,⟨?_,?_,?_,?_,?_,?_,
    (cyclicReplicaArchiveHandoff_banks C).1.trans hbankL,
    (cyclicReplicaArchiveHandoff_banks C).2.trans hbankR,
    (cyclicReplicaArchiveHandoff_recoveryRhs H K leftBuffers rightBuffers C hrhsL hrhsR).1,
    (cyclicReplicaArchiveHandoff_recoveryRhs H K leftBuffers rightBuffers C hrhsL hrhsR).2⟩⟩
  · rw [hlenL,hlenR]
  · exact (hheaders 130 (by decide) (by decide)).trans hwidth
  · exact (hheaders 168 (by decide) (by decide)).trans hvolL
  · exact (hheaders 171 (by decide) (by decide)).trans hvolR
  · exact (hheaders 229 (by decide) (by decide)).trans hcount
  · change (cyclicReplicaArchiveHandoffState C).R (factorReg 169) = _
    simpa only [harchL,h169,List.append_nil] using (cyclicReplicaArchiveHandoff_archives C).1
  · change (cyclicReplicaArchiveHandoffState C).R (factorReg 172) = _
    simpa only [harchR,h172,List.append_nil] using (cyclicReplicaArchiveHandoff_archives C).2

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
