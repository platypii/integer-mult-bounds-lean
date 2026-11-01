module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedReplicaCouplingLoopStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializedCachedReplicaCouplingLoop

/-! Generate the loop clock from the retained replica-count master. The complete
cached shared-bank loop restores that master and releases its private counter.
Mask generation is shared setup and is not charged per replica. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

theorem initializedCachedReplicaCouplingLoop_exec_within (H : ReplicaHaloProblem s) {plan : ReplicaInteriorPlacement T}
    (placement : ReplicaCouplingPlacement plan) (volume output rhs dst saved tmp count : Fin T)
    (hreg : [plan.gather 121,volume,output,rhs,placement.bank 132,placement.bank 93,placement.bank 110,dst,saved,tmp,count].Nodup)
    (houtput : ∀ i, placement.bank i ≠ output) (hrhs : ∀ i, placement.bank i ≠ rhs)
    (hdst : ∀ i, placement.bank i ≠ dst) (hcountBank : ∀ i, placement.bank i ≠ count) (hQ : SS.states ≤ Q) (K : ℕ)
    (hpush : mnProgPush (rmulOne (P := Empty) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ K) (hA : 96 ≤ A)
    (hw5 : 5 ≤ H.wordWidth) (hqw : H.precision+4 ≤ H.wordWidth) (hsep : H.span+H.band ≤ s)
    (V : ℕ) (hNV : H.span < 2^V)
    (has : ∀ j < H.span, ∀ z ∈ couplingCoefficientWords (2^15*H.p) H.precision s H.t H.u H.band (H.origin+j), Fits H.wordWidth z ∧ z.im = 0)
    (outputTail rhsTail pageTail raw : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (h : ReplicaCouplingCursor H output rhs outputTail rhsTail 0 S) (hcountBlank : S.R count = []) (hmaster : (S.R (plan.gather 121)).length = H.Fs.length)
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
    ∃ v' F m, ∃ Ds : List (ZMod s → GaussianInt), v'.user = v.user ∧
      m ≤ (4*H.Fs.length+4)+H.Fs.length*(cachedReplicaCouplingTransitionCost H V+3)+2 ∧
      (∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          ((8*H.Fs.length+8)+cachedReplicaCouplingTransitionWorkspace (Q := Q) (A := A) (U := U) H K V))
        depth (initializedCachedReplicaCouplingLoop placement volume output rhs dst saved tmp count hQ) (mk v S) m (mk v' F)) ∧
      F.R count = [] ∧ F.R output = outputTail ∧ F.R rhs = rhsTail ∧
      embStk placement.bank F = embStk placement.bank S ∧ F.L = S.L ∧ F.inp = S.inp ∧ F.out = S.out ∧
      (∀ k, k ∉ [output,rhs,dst] → F.R k = S.R k) ∧
      Ds.length = H.Fs.length ∧
      F.R dst = Ds.flatMap (fun D => cstream A H.wordWidth (packedInterval H.origin H.span D))++S.R dst ∧
      (∀ j : Fin Ds.length, ReplicaCouplingResidualSpec H (H.Fs.length-1-j.val) (Ds[j.val]'j.isLt)) := by
  have hregs := hreg
  regs_ne hregs
  obtain ⟨v₁,hu₁,he₁⟩ := ucopy_exec (body := body) (a := plan.gather 121) (b := count) (t := saved)
    (by assumption) (by assumption) (by exact ‹saved ≠ count›.symm) v S hsaved
  let J : Stacks T A := {S with R := Function.update S.R count (List.replicate H.Fs.length tick)}
  have he₁' : Exec body (ucopy (plan.gather 121) count saved) (mk v S) (4*H.Fs.length+4) (mk v₁ J) := by
    simpa [J,hmaster,hcountBlank] using he₁
  have hbank : embStk placement.bank J = embStk placement.bank S := embStk_updateR_off S count _ hcountBank
  have hbankR (k : Fin 168) : J.R (placement.bank k) = S.R (placement.bank k) := congrFun (congrArg Stacks.R hbank) k
  have hnative : embStk weightCacheCoreReg (embStk plan.solver J) = embStk weightCacheCoreReg (embStk plan.solver S) := by
    rw [← placement.native_view J,← placement.native_view S,hbank]
  obtain ⟨v₂,F,m,Ds,hu₂,hm,hex,hcountF,hout,hrhsF,hbankF,hL,hi,ho,hframe,hlen,harchive,hgood⟩ :=
    cachedReplicaCouplingLoop_exec_within (body := body) H placement volume output rhs dst saved tmp count (by regs_nodup)
      houtput hrhs hdst hcountBank hQ K hpush hA hw5 hqw hsep V hNV has outputTail rhsTail pageTail raw v₁ J
      (ReplicaCouplingCursor.of_frame H output rhs outputTail rhsTail 0 S J h
        (by simp [J,‹output ≠ count›]) (by simp [J,‹rhs ≠ count›]))
      (by simp [J]) (by rw [hnative]; exact hready)
      (by simpa [J,‹volume ≠ count›] using hvolume)
      (by simpa [J,‹saved ≠ count›] using hsaved) (by simpa [J,‹tmp ≠ count›] using htmp)
      (by rw [hbankR 140]; exact hrows) (by rw [hbankR 138]; exact hpage)
      (by rw [hbankR 139]; exact hcount) (by rw [hbank]; exact hgeometry)
      (by intro k hk; rw [hbankR k]; exact hfresh k hk)
      (by rw [hbankR 159]; exact h159) (by rw [hbankR 161]; exact h161)
  refine ⟨v₂,F,(4*H.Fs.length+4)+m,Ds,hu₂.trans hu₁,by omega,?_,hcountF,hout,hrhsF,
    hbankF.trans hbank,hL,hi,ho,?_,hlen,?_,hgood⟩
  · intro depth
    have ht₁ := mn_native_exec_within he₁' 2 (by
      simp [ucopy,umulSym,scanR,drainR,popDo,keepIn,pushN,moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush])
      depth _ (le_refl _)
    have hs := ht₁.final
    refine .seq (ht₁.mono ?_) ((hex depth).mono ?_)
    all_goals intro d z hz; omega
  · intro k hk
    by_cases hkc : k = count
    · subst k
      exact hcountF.trans hcountBlank.symm
    · rw [hframe k (by
        simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hk ⊢
        exact ⟨hkc,hk⟩)]
      exact Function.update_of_ne hkc _ _
  · simpa only [J,Function.update_of_ne ‹dst ≠ count›] using harchive

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
