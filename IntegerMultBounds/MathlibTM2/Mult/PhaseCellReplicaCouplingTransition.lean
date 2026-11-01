module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaCouplingCursor
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaCouplingResidual

/-! One replica transition stages matching inputs, computes and archives the
residual, and restores the complete shared bank before advancing the cursor. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

noncomputable def replicaCouplingTransition {plan : ReplicaInteriorPlacement T}
    (placement : ReplicaCouplingPlacement plan) (volume output rhs dst saved tmp : Fin T)
    (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  .seq (stageReplicaCouplingRow volume output rhs (placement.bank 132) (placement.bank 93) saved tmp)
    (replicaCouplingResidual placement volume dst saved tmp hQ false)

theorem ReplicaCouplingCursor.couple (H : ReplicaHaloProblem s) {plan : ReplicaInteriorPlacement T}
    (placement : ReplicaCouplingPlacement plan) (volume output rhs dst saved tmp : Fin T)
    (hreg : [volume,output,rhs,placement.bank 132,placement.bank 93,placement.bank 110,dst,saved,tmp].Nodup)
    (houtput : ∀ i, placement.bank i ≠ output) (hrhs : ∀ i, placement.bank i ≠ rhs)
    (hdst : ∀ i, placement.bank i ≠ dst) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (hw5 : 5 ≤ H.wordWidth) (hqw : H.precision+4 ≤ H.wordWidth) (hsep : H.span+H.band ≤ s)
    (V : ℕ) (hwide : 8*(H.t+1)^2+4*H.band+8 < 2^V)
    (hfitV : H.origin+(H.span+2*H.band)+s < 2^V)
    (has : ∀ j < H.span, ∀ z ∈ couplingCoefficientWords (2^15*H.p) H.precision s H.t H.u H.band (H.origin+j), Fits H.wordWidth z ∧ z.im = 0)
    (outputTail rhsTail pageTail raw : List (Fin (A+4))) (r : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (h : ReplicaCouplingCursor H output rhs outputTail rhsTail r S) (hr : r < H.Fs.length)
    (hready : RetainedCouplingReady (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band H.origin (H.origin+H.span) raw
      (embStk weightCacheCoreReg (embStk plan.solver S)))
    (hvolume : (S.R volume).length = H.span*H.wordWidth) (hsaved : S.R saved = []) (htmp : S.R tmp = [])
    (hrows : (S.R (placement.bank 140)).length = 2*H.band+1)
    (hpage : S.R (placement.bank 138) = cstream A H.wordWidth
      (couplingCoefficientPageInterval (2^15*H.p) H.precision s H.t H.u H.band H.origin (H.origin+H.span) H.origin H.span)++pageTail)
    (hcount : (S.R (placement.bank 139)).length =
      (couplingCoefficientPageInterval (2^15*H.p) H.precision s H.t H.u H.band H.origin (H.origin+H.span) H.origin H.span).length)
    (hgeometry : CouplingIntervalMetadata V s H.t H.band H.origin (H.origin+H.span) H.origin H.span (embStk placement.bank S))
    (hfresh : ∀ k ∈ [(127 : Fin 168),143,166,158,135,167], S.R (placement.bank k) = []) :
    ∃ C R : ZMod s → GaussianInt, ∃ v' F n, v'.user = v.user ∧
      n ≤ stageReplicaCouplingRowCost (H.span*H.wordWidth)+
        (replicaLocalCouplingCost false (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band H.origin (H.origin+H.span) H.origin H.span V+
          finishReplicaCouplingRowCost (H.span*H.wordWidth)) ∧
      Exec body (replicaCouplingTransition placement volume output rhs dst saved tmp hQ) (Host.mk v S) n (Host.mk v' F) ∧
      ReplicaCouplingCursor H output rhs outputTail rhsTail (r+1) F ∧
      ReplicaHaloRowSpec H r C ∧ R = H.Fs.reverse.getD r (fun _ => 0) ∧
      F.R dst = cstream A H.wordWidth (packedInterval H.origin H.span
        (guardedCouplingRowField (2^15*H.p) H.precision H.t H.u H.band H.origin (H.origin+H.span) false C R))++S.R dst ∧
      embStk placement.bank F = embStk placement.bank S ∧ F.L = S.L ∧ F.inp = S.inp ∧ F.out = S.out ∧
      (∀ k, k ∉ [output,rhs,dst] → F.R k = S.R k) := by
  have hregs := hreg
  regs_ne hregs
  obtain ⟨C,R,v₁,J,hu₁,he₁,hcursor,hfield,hrhsRow,hC,hR,_,hframe,hleft,hi,ho⟩ :=
    ReplicaCouplingCursor.stage (body := body) H volume output rhs (placement.bank 132) (placement.bank 93) saved tmp
      (by regs_nodup) outputTail rhsTail r v S h hr hvolume hsaved htmp 0
  have hbankFrame (k : Fin 168) (h132 : k ≠ 132) (h93 : k ≠ 93) : J.R (placement.bank k) = S.R (placement.bank k) := by
    apply hframe
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨houtput k,hrhs k,placement.bank_injective.ne h132,placement.bank_injective.ne h93⟩
  have hreadyJ : RetainedCouplingReady (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band H.origin (H.origin+H.span) raw
      (embStk weightCacheCoreReg (embStk plan.solver J)) := by
    apply hready.of_frame (S' := embStk weightCacheCoreReg (embStk plan.solver J))
    · exact congrArg (fun L => L ∘ plan.solver ∘ weightCacheCoreReg) hleft
    · intro k h93 _ _
      change J.R (plan.solver (weightCacheCoreReg k)) = S.R (plan.solver (weightCacheCoreReg k))
      rw [← placement.bank_native k]
      apply hbankFrame
      · intro hh
        have hv : k.val = 132 := congrArg Fin.val hh
        have hk := k.isLt
        omega
      · intro hh
        apply h93
        exact Fin.ext (congrArg (fun j : Fin 168 => j.val) hh)
  have hgeometryJ : CouplingIntervalMetadata V s H.t H.band H.origin (H.origin+H.span) H.origin H.span (embStk placement.bank J) := by
    apply hgeometry.of_frame (hbankFrame 163 (by decide) (by decide))
    intro k hk
    apply hbankFrame
    all_goals simp only [couplingIntervalPorts,List.mem_cons,List.not_mem_nil,or_false] at hk
    all_goals rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hfreshJ (k : Fin 168) (hk : k ∈ [(127 : Fin 168),143,166,158,135,167]) : J.R (placement.bank k) = [] := by
    have hn : k ≠ 132 ∧ k ≠ 93 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [hbankFrame k hn.1 hn.2]
    exact hfresh k hk
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := replicaCouplingResidual_exec (body := body) placement volume dst saved tmp hQ false
    hA hw5 hqw H.s_lt_t C R H.span_fit (S.R (placement.bank 132)) pageTail (S.R (placement.bank 93)) raw
    v₁ J hreadyJ rfl rfl hsep hfield (hfreshJ 127 (by simp))
    (by rw [hbankFrame 140 (by decide) (by decide)]; exact hrows)
    (by rw [hbankFrame 138 (by decide) (by decide)]; exact hpage) hrhsRow (hfreshJ 143 (by simp))
    hC.2.1 has V (hfreshJ 166 (by simp))
    (by rw [hbankFrame 139 (by decide) (by decide)]; exact hcount)
    (by have hh := H.span_fit; omega) H.span_fit H.band_fit hwide hfitV hgeometryJ
    (hfreshJ 158 (by simp)) (hfreshJ 135 (by simp)) (hfreshJ 167 (by simp)) (by regs_nodup)
    (by rw [hframe volume (by simp [‹volume ≠ output›,‹volume ≠ rhs›,‹volume ≠ placement.bank 132›,‹volume ≠ placement.bank 93›])]; exact hvolume)
    (by rw [hframe saved (by simp [‹output ≠ saved›.symm,‹rhs ≠ saved›.symm,‹placement.bank 132 ≠ saved›.symm,‹placement.bank 93 ≠ saved›.symm])]; exact hsaved)
    (by rw [hframe tmp (by simp [‹output ≠ tmp›.symm,‹rhs ≠ tmp›.symm,‹placement.bank 132 ≠ tmp›.symm,‹placement.bank 93 ≠ tmp›.symm])]; exact htmp)
  let ys := cstream A H.wordWidth (packedInterval H.origin H.span
    (guardedCouplingRowField (2^15*H.p) H.precision H.t H.u H.band H.origin (H.origin+H.span) false C R))
  let F := replicaResidualState placement dst (S.R (placement.bank 132)) (S.R (placement.bank 93)) ys J
  have hRbank (k : Fin 168) : F.R (placement.bank k) = S.R (placement.bank k) := by
    by_cases h132 : k = 132
    · subst k
      simp [F,replicaResidualState,hdst 132,placement.bank_injective.ne (by decide : (132 : Fin 168) ≠ 93)]
    by_cases h93 : k = 93
    · subst k
      simp [F,replicaResidualState,hdst 93]
    simp only [F,replicaResidualState,Function.update_of_ne (hdst k),
      Function.update_of_ne (placement.bank_injective.ne h93),Function.update_of_ne (placement.bank_injective.ne h132)]
    exact hbankFrame k h132 h93
  refine ⟨C,R,v₂,F,stageReplicaCouplingRowCost (H.span*H.wordWidth)+n₂,hu₂.trans hu₁,by omega,
    .seq he₁.toExec he₂,?_,hC,hR,?_,?_,hleft,hi,ho,?_⟩
  · apply ReplicaCouplingCursor.of_frame H output rhs outputTail rhsTail (r+1) J F hcursor
    · simp [F,replicaResidualState,‹output ≠ dst›,(houtput 132).symm,(houtput 93).symm]
    · simp [F,replicaResidualState,‹rhs ≠ dst›,(hrhs 132).symm,(hrhs 93).symm]
  · simp only [F,replicaResidualState,Function.update_self]
    rw [hframe dst (by simp [‹output ≠ dst›.symm,‹rhs ≠ dst›.symm,(hdst 132).symm,(hdst 93).symm])]
  · exact Stacks.ext hi ho (congrArg (fun L => L ∘ placement.bank) hleft) (funext hRbank)

  · intro k hk
    by_cases h132 : k = placement.bank 132
    · subst k; exact hRbank 132
    by_cases h93 : k = placement.bank 93
    · subst k; exact hRbank 93
    have hn : k ≠ output ∧ k ≠ rhs ∧ k ≠ dst := by simpa using hk
    simp only [F,replicaResidualState,Function.update_of_ne hn.2.2,
      Function.update_of_ne h93,Function.update_of_ne h132]
    apply hframe
    simpa using ⟨hn.1,hn.2.1,h132,h93⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
