module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedReplicaCouplingLoop
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedReplicaCouplingTransitionStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedLoopSharedStock
public import IntegerMultBounds.MathlibTM2.StackExecutionUnique

/-! The cached traversal reuses one transition reserve. Execution uniqueness
joins its resource trace to the established archive and accuracy theorem. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

theorem cachedReplicaCouplingLoop_exec_within (H : ReplicaHaloProblem s) {plan : ReplicaInteriorPlacement T}
    (placement : ReplicaCouplingPlacement plan) (volume output rhs dst saved tmp count : Fin T)
    (hreg : [volume,output,rhs,placement.bank 132,placement.bank 93,placement.bank 110,dst,saved,tmp,count].Nodup)
    (houtput : ∀ i, placement.bank i ≠ output) (hrhs : ∀ i, placement.bank i ≠ rhs)
    (hdst : ∀ i, placement.bank i ≠ dst) (hcountBank : ∀ i, placement.bank i ≠ count) (hQ : SS.states ≤ Q) (K : ℕ)
    (hpush : mnProgPush (rmulOne (P := Empty) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ K) (hA : 96 ≤ A)
    (hw5 : 5 ≤ H.wordWidth) (hqw : H.precision+4 ≤ H.wordWidth) (hsep : H.span+H.band ≤ s)
    (V : ℕ) (hNV : H.span < 2^V)
    (has : ∀ j < H.span, ∀ z ∈ couplingCoefficientWords (2^15*H.p) H.precision s H.t H.u H.band (H.origin+j), Fits H.wordWidth z ∧ z.im = 0)
    (outputTail rhsTail pageTail raw : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (h : ReplicaCouplingCursor H output rhs outputTail rhsTail 0 S) (hcountLen : (S.R count).length = H.Fs.length)
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
      m ≤ H.Fs.length*(cachedReplicaCouplingTransitionCost H V+3)+2 ∧
      (∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          cachedReplicaCouplingTransitionWorkspace (Q := Q) (A := A) (U := U) H K V)
        depth (cachedReplicaCouplingLoop placement volume output rhs dst saved tmp count hQ) (mk v S) m (mk v' F)) ∧
      F.R count = [] ∧ F.R output = outputTail ∧ F.R rhs = rhsTail ∧
      embStk placement.bank F = embStk placement.bank S ∧ F.L = S.L ∧ F.inp = S.inp ∧ F.out = S.out ∧
      (∀ k, k ∉ [count,output,rhs,dst] → F.R k = S.R k) ∧
      Ds.length = H.Fs.length ∧
      F.R dst = Ds.flatMap (fun D => cstream A H.wordWidth (packedInterval H.origin H.span D))++S.R dst ∧
      (∀ j : Fin Ds.length, ReplicaCouplingResidualSpec H (H.Fs.length-1-j.val) (Ds[j.val]'j.isLt)) := by
  have hregs := hreg
  regs_ne hregs
  obtain ⟨vf,G,m,Ds,hu,hm,hex,hrest⟩ := cachedReplicaCouplingLoop_exec (body := body) H placement
    volume output rhs dst saved tmp count hreg houtput hrhs hdst hcountBank hQ hA hw5 hqw hsep V hNV has
    outputTail rhsTail pageTail raw v S h hcountLen hready hvolume hsaved htmp hrows hpage hcount hgeometry hfresh h159 h161
  let Inv (r : ℕ) (F : Stacks T A) : Prop :=
    ReplicaCouplingCursor H output rhs outputTail rhsTail r F ∧
      embStk placement.bank F = embStk placement.bank S ∧ F.R volume = S.R volume ∧
      F.R saved = S.R saved ∧ F.R tmp = S.R tmp
  have hstable : ∀ r F xs, Inv r F → Inv r {F with R := Function.update F.R count xs} := by
    intro r F xs hI
    obtain ⟨hc,hbank,hv,hs,ht⟩ := hI
    refine ⟨ReplicaCouplingCursor.of_frame H output rhs outputTail rhsTail r F _ hc
      (by simp [‹output ≠ count›]) (by simp [‹rhs ≠ count›]),
      (embStk_updateR_off F count xs hcountBank).trans hbank,?_,?_,?_⟩
    · simpa only [Function.update_of_ne ‹volume ≠ count›] using hv
    · simpa only [Function.update_of_ne ‹saved ≠ count›] using hs
    · simpa only [Function.update_of_ne ‹tmp ≠ count›] using ht
  have hstep : ∀ r < H.Fs.length, ∀ (vi : HS T Q A U) F, Inv r F →
      ∃ v' J n, v'.user = vi.user ∧ n ≤ cachedReplicaCouplingTransitionCost H V ∧
        (∀ depth, ExecWithin body
          (fun d z => mnSize z+d ≤ mnSize (mk vi F)+depth+
            cachedReplicaCouplingTransitionWorkspace (Q := Q) (A := A) (U := U) H K V)
          depth (cachedReplicaCouplingTransition placement volume output rhs dst saved tmp hQ) (mk vi F) n (mk v' J)) ∧
        J.R count = F.R count ∧ Inv (r+1) J ∧ mnSize (mk v' J) ≤ mnSize (mk vi F) := by
    intro r hr vi F hI
    obtain ⟨hc,hbank,hv,hs,ht⟩ := hI
    have hbankR (k : Fin 168) : F.R (placement.bank k) = S.R (placement.bank k) :=
      congrFun (congrArg Stacks.R hbank) k
    have hnative : embStk weightCacheCoreReg (embStk plan.solver F) = embStk weightCacheCoreReg (embStk plan.solver S) := by
      rw [← placement.native_view F,← placement.native_view S,hbank]
    obtain ⟨C,R,v',J,n,hu,hn,hex,hcursor,hC,hR,harchive,hbankJ,hL,hi,ho,hframe,hstock⟩ :=
      ReplicaCouplingCursor.couple_cached_within (body := body) H placement volume output rhs dst saved tmp (by regs_nodup)
        houtput hrhs hdst hQ K hpush hA hw5 hqw hsep V hNV has outputTail rhsTail pageTail raw r vi F hc hr
        (by rw [hnative]; exact hready) (by rw [hv]; exact hvolume)
        (by rw [hs]; exact hsaved) (by rw [ht]; exact htmp)
        (by rw [hbankR 140]; exact hrows) (by rw [hbankR 138]; exact hpage)
        (by rw [hbankR 139]; exact hcount) (by rw [hbank]; exact hgeometry)
        (by intro k hk; rw [hbankR k]; exact hfresh k hk)
        (by rw [hbankR 159]; exact h159) (by rw [hbankR 161]; exact h161)
    refine ⟨v',J,n,hu,hn,hex,?_,⟨hcursor,hbankJ.trans hbank,?_,?_,?_⟩,hstock⟩
    · exact hframe count (by simp [‹output ≠ count›.symm,‹rhs ≠ count›.symm,‹dst ≠ count›.symm])
    · exact (hframe volume (by simp [‹volume ≠ output›,‹volume ≠ rhs›,‹volume ≠ dst›])).trans hv
    · exact (hframe saved (by simp [‹output ≠ saved›.symm,‹rhs ≠ saved›.symm,‹dst ≠ saved›.symm])).trans hs
    · exact (hframe tmp (by simp [‹output ≠ tmp›.symm,‹rhs ≠ tmp›.symm,‹dst ≠ tmp›.symm])).trans ht
  obtain ⟨v',F,n,_,_,htrace,_,_⟩ := countedLoop_exec_costs_within count
    (cachedReplicaCouplingTransition placement volume output rhs dst saved tmp hQ) H.Fs.length
    (fun _ => cachedReplicaCouplingTransitionCost H V) Inv
    (cachedReplicaCouplingTransitionWorkspace (Q := Q) (A := A) (U := U) H K V)
    hstable hstep v S hcountLen ⟨h,rfl,rfl,rfl,rfl⟩
  obtain ⟨htime,hfinal⟩ := (htrace 0).toExec.unique hex
  refine ⟨vf,G,m,Ds,hu,hm,?_,hrest⟩
  intro depth
  exact (htrace depth).cast htime hfinal

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
