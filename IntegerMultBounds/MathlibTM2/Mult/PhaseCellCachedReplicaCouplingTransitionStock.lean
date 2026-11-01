module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaCouplingStageFrame
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedReplicaCouplingResidualStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedReplicaCouplingTransition
public import IntegerMultBounds.MathlibTM2.StackInvariantShift
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaCouplingStock

/-! A cached replica transition reuses the common staging and endpoint frames.
Masks and coefficient pages are restored before the next replica consumes them. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

noncomputable def cachedReplicaCouplingTransitionWorkspace (H : ReplicaHaloProblem s) (K V : ℕ) : ℕ :=
  2*stageReplicaCouplingRowCost (H.span*H.wordWidth)+
    (cachedReplicaLocalCouplingWorkspace (Q := Q) (A := A) (U := U) (2^15*H.p) K H.precision H.wordWidth
      s H.t H.u H.band H.origin (H.origin+H.span) H.origin H.span V+
        2*finishReplicaCouplingRowCost (H.span*H.wordWidth))

theorem ReplicaCouplingCursor.couple_cached_within (H : ReplicaHaloProblem s) {plan : ReplicaInteriorPlacement T}
    (placement : ReplicaCouplingPlacement plan) (volume output rhs dst saved tmp : Fin T)
    (hreg : [volume,output,rhs,placement.bank 132,placement.bank 93,placement.bank 110,dst,saved,tmp].Nodup)
    (houtput : ∀ i, placement.bank i ≠ output) (hrhs : ∀ i, placement.bank i ≠ rhs)
    (hdst : ∀ i, placement.bank i ≠ dst) (hQ : SS.states ≤ Q) (K : ℕ)
    (hpush : mnProgPush (rmulOne (P := Empty) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ K) (hA : 96 ≤ A)
    (hw5 : 5 ≤ H.wordWidth) (hqw : H.precision+4 ≤ H.wordWidth) (hsep : H.span+H.band ≤ s)
    (V : ℕ) (hNV : H.span < 2^V)
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
    (hfresh : ∀ k ∈ [(127 : Fin 168),143,166,158,135,167], S.R (placement.bank k) = [])
    (h159 : S.R (placement.bank 159) = (couplingRibbonFlags (s := s) false H.t H.band H.origin
      (H.origin+H.span) H.origin H.span).map (fun flag => pairSym A flag flag))
    (h161 : S.R (placement.bank 161) = recoveryGuardIntervalSymbols true A s H.t (2*H.band)
      H.origin (H.origin+H.span) H.origin H.span) :
    ∃ C R : ZMod s → GaussianInt, ∃ v' F n, v'.user = v.user ∧
      n ≤ stageReplicaCouplingRowCost (H.span*H.wordWidth)+
        (cachedReplicaLocalCouplingCost false (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band H.origin (H.origin+H.span) H.origin H.span V+
          finishReplicaCouplingRowCost (H.span*H.wordWidth)) ∧
      (∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
          cachedReplicaCouplingTransitionWorkspace (Q := Q) (A := A) (U := U) H K V)
        depth (cachedReplicaCouplingTransition placement volume output rhs dst saved tmp hQ)
          (Host.mk v S) n (Host.mk v' F)) ∧
      ReplicaCouplingCursor H output rhs outputTail rhsTail (r+1) F ∧
      ReplicaHaloRowSpec H r C ∧ R = H.Fs.reverse.getD r (fun _ => 0) ∧
      F.R dst = cstream A H.wordWidth (packedInterval H.origin H.span
        (guardedCouplingRowField (2^15*H.p) H.precision H.t H.u H.band H.origin (H.origin+H.span) false C R))++S.R dst ∧
      embStk placement.bank F = embStk placement.bank S ∧ F.L = S.L ∧ F.inp = S.inp ∧ F.out = S.out ∧
      (∀ k, k ∉ [output,rhs,dst] → F.R k = S.R k) ∧
      mnSize (Host.mk v' F) ≤ mnSize (Host.mk v S) := by
  have hregs := hreg
  regs_ne hregs
  obtain ⟨C,R,v₁,J,hu₁,he₁,hcursor,hfield,hrhsRow,hC,hR,_,hframe,hleft,hi,ho⟩ :=
    ReplicaCouplingCursor.stage (body := body) H volume output rhs (placement.bank 132) (placement.bank 93) saved tmp
      (by regs_nodup) outputTail rhsTail r v S h hr hvolume hsaved htmp 0
  have hstage : ReplicaCouplingStageFrame placement output rhs S J := ⟨hleft,hi,ho,hframe⟩
  have hbankFrame := hstage.bank_right houtput hrhs
  have hreadyJ := hstage.ready houtput hrhs raw hready
  have hgeometryJ := hstage.geometry houtput hrhs hgeometry
  have hfreshJ (k : Fin 168) (hk : k ∈ [(127 : Fin 168),143,166,158,135,167]) : J.R (placement.bank k) = [] := by
    have hn : k ≠ 132 ∧ k ≠ 93 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [hbankFrame k hn.1 hn.2]
    exact hfresh k hk
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := cachedReplicaCouplingResidual_exec_within (body := body) placement volume dst saved tmp hQ false K hpush
    hA hw5 hqw H.s_lt_t C R H.span_fit (S.R (placement.bank 132)) pageTail (S.R (placement.bank 93)) raw
    v₁ J hreadyJ rfl rfl hsep hfield (hfreshJ 127 (by simp))
    (by rw [hbankFrame 140 (by decide) (by decide)]; exact hrows)
    (by rw [hbankFrame 138 (by decide) (by decide)]; exact hpage) hrhsRow (hfreshJ 143 (by simp))
    hC.2.1 has V (hfreshJ 166 (by simp))
    (by rw [hbankFrame 139 (by decide) (by decide)]; exact hcount)
    H.span_fit H.band_fit hNV hgeometryJ
    ((hbankFrame 159 (by decide) (by decide)).trans h159)
    ((hbankFrame 161 (by decide) (by decide)).trans h161)
    (hfreshJ 158 (by simp)) (hfreshJ 135 (by simp)) (hfreshJ 167 (by simp)) (by regs_nodup)
    (by rw [hframe volume (by simp [‹volume ≠ output›,‹volume ≠ rhs›,‹volume ≠ placement.bank 132›,‹volume ≠ placement.bank 93›])]; exact hvolume)
    (by rw [hframe saved (by simp [‹output ≠ saved›.symm,‹rhs ≠ saved›.symm,‹placement.bank 132 ≠ saved›.symm,‹placement.bank 93 ≠ saved›.symm])]; exact hsaved)
    (by rw [hframe tmp (by simp [‹output ≠ tmp›.symm,‹rhs ≠ tmp›.symm,‹placement.bank 132 ≠ tmp›.symm,‹placement.bank 93 ≠ tmp›.symm])]; exact htmp) 0
  let ys := cstream A H.wordWidth (packedInterval H.origin H.span
    (guardedCouplingRowField (2^15*H.p) H.precision H.t H.u H.band H.origin (H.origin+H.span) false C R))
  let F := replicaResidualState placement dst (S.R (placement.bank 132)) (S.R (placement.bank 93)) ys J
  obtain ⟨hcursorF,harchive,hbankF,hleftF,hinF,houtF,hframeF⟩ :=
    hstage.finish_residual H houtput hrhs hdst ‹output ≠ dst› ‹rhs ≠ dst› outputTail rhsTail ys r hcursor
  have hsize := he₁.final
  have hex : ExecWithin body
      (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+cachedReplicaCouplingTransitionWorkspace (Q := Q) (A := A) (U := U) H K V)
      0 (cachedReplicaCouplingTransition placement volume output rhs dst saved tmp hQ)
      (Host.mk v S) (stageReplicaCouplingRowCost (H.span*H.wordWidth)+n₂) (Host.mk v₂ F) := by
    refine .seq (he₁.mono ?_) (he₂.mono ?_)
    all_goals intro d z hz; dsimp only [cachedReplicaCouplingTransitionWorkspace] at *; omega
  have hstock := ReplicaCouplingCursor.stock_le H output rhs dst (by regs_nodup) outputTail rhsTail r
    v v₂ S F h hcursorF hr hleftF hinF houtF hframeF
    (by
      have ha : F.R dst = ys++S.R dst := harchive
      rw [ha]
      simp [ys,packedInterval_length _ H.span_fit,Nat.add_comm])
  refine ⟨C,R,v₂,F,stageReplicaCouplingRowCost (H.span*H.wordWidth)+n₂,hu₂.trans hu₁,by omega,
    ?_,hcursorF,hC,hR,harchive,hbankF,hleftF,hinF,houtF,hframeF,hstock⟩
  intro depth
  simpa only [Nat.zero_add,Nat.add_right_comm] using mn_exec_within_shift hex depth

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
