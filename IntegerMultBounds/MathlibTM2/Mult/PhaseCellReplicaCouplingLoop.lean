module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaCouplingTransition
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedLoop

/-! Structural traversal of all replica rows. Shared pages and counters restore
at each step; physical archive rows retain the matching accuracy witnesses. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

def ReplicaCouplingResidualSpec (H : ReplicaHaloProblem s) (r : ℕ) (D : ZMod s → GaussianInt) : Prop :=
  ∃ C, ReplicaHaloRowSpec H r C ∧ D = guardedCouplingRowField (2^15*H.p) H.precision H.t H.u H.band
    H.origin (H.origin+H.span) false C (H.Fs.reverse.getD r (fun _ => 0))

def replicaCouplingTransitionCost (H : ReplicaHaloProblem s) (V : ℕ) :=
  stageReplicaCouplingRowCost (H.span*H.wordWidth)+
    (replicaLocalCouplingCost false (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band H.origin (H.origin+H.span) H.origin H.span V+
      finishReplicaCouplingRowCost (H.span*H.wordWidth))

noncomputable def replicaCouplingLoop {plan : ReplicaInteriorPlacement T}
    (placement : ReplicaCouplingPlacement plan) (volume output rhs dst saved tmp count : Fin T)
    (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  countedLoop count (replicaCouplingTransition placement volume output rhs dst saved tmp hQ)

/-- The archive and accuracy induction depends only on a row transition's
cursor, frame and exact residual endpoint. Numerical workers are supplied last. -/
theorem replicaCouplingTraversal_exec (H : ReplicaHaloProblem s) {plan : ReplicaInteriorPlacement T}
    (placement : ReplicaCouplingPlacement plan) (volume output rhs dst saved tmp count : Fin T)
    (hreg : [volume,output,rhs,placement.bank 132,placement.bank 93,placement.bank 110,dst,saved,tmp,count].Nodup)
    (hcountBank : ∀ i, placement.bank i ≠ count) (step : Pr P T Q A U) (stepCost : ℕ)
    (outputTail rhsTail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (h : ReplicaCouplingCursor H output rhs outputTail rhsTail 0 S) (hcountLen : (S.R count).length = H.Fs.length)
    (hcouple : ∀ r < H.Fs.length, ∀ (vi : HS T Q A U) F,
      ReplicaCouplingCursor H output rhs outputTail rhsTail r F →
      embStk placement.bank F = embStk placement.bank S → F.R volume = S.R volume →
      F.R saved = S.R saved → F.R tmp = S.R tmp →
      ∃ C R : ZMod s → GaussianInt, ∃ vf G m, vf.user = vi.user ∧ m ≤ stepCost ∧
        Exec body step (mk vi F) m (mk vf G) ∧
        ReplicaCouplingCursor H output rhs outputTail rhsTail (r+1) G ∧
        ReplicaHaloRowSpec H r C ∧ R = H.Fs.reverse.getD r (fun _ => 0) ∧
        G.R dst = cstream A H.wordWidth (packedInterval H.origin H.span
          (guardedCouplingRowField (2^15*H.p) H.precision H.t H.u H.band H.origin (H.origin+H.span) false C R))++F.R dst ∧
        embStk placement.bank G = embStk placement.bank F ∧ G.L = F.L ∧ G.inp = F.inp ∧ G.out = F.out ∧
        (∀ k, k ∉ [output,rhs,dst] → G.R k = F.R k)) :
    ∃ v' F m, ∃ Ds : List (ZMod s → GaussianInt), v'.user = v.user ∧
      m ≤ H.Fs.length*(stepCost+3)+2 ∧
      Exec body (countedLoop count step) (mk v S) m (mk v' F) ∧
      F.R count = [] ∧ F.R output = outputTail ∧ F.R rhs = rhsTail ∧
      embStk placement.bank F = embStk placement.bank S ∧ F.L = S.L ∧ F.inp = S.inp ∧ F.out = S.out ∧
      (∀ k, k ∉ [count,output,rhs,dst] → F.R k = S.R k) ∧ Ds.length = H.Fs.length ∧
      F.R dst = Ds.flatMap (fun D => cstream A H.wordWidth (packedInterval H.origin H.span D))++S.R dst ∧
      (∀ j : Fin Ds.length, ReplicaCouplingResidualSpec H (H.Fs.length-1-j.val) (Ds[j.val]'j.isLt)) := by
  have hregs := hreg
  regs_ne hregs
  let Inv := fun r F => ReplicaCouplingCursor H output rhs outputTail rhsTail r F ∧
    embStk placement.bank F = embStk placement.bank S ∧ F.R volume = S.R volume ∧
    F.R saved = S.R saved ∧ F.R tmp = S.R tmp ∧ F.L = S.L ∧ F.inp = S.inp ∧ F.out = S.out ∧
    (∀ k, k ∉ [count,output,rhs,dst] → F.R k = S.R k) ∧
    ∃ Ds : List (ZMod s → GaussianInt), Ds.length = r ∧
      F.R dst = Ds.flatMap (fun D => cstream A H.wordWidth (packedInterval H.origin H.span D))++S.R dst ∧
      ∀ j : Fin Ds.length, ReplicaCouplingResidualSpec H (r-1-j.val) Ds[j.val]
  have hstable : ∀ r F xs, Inv r F → Inv r {F with R := Function.update F.R count xs} := by
    intro r F xs hI
    obtain ⟨hc,hbank,hv,hs,ht,hL,hi,ho,hframe,Ds,hlen,harchive,hgood⟩ := hI
    refine ⟨ReplicaCouplingCursor.of_frame H output rhs outputTail rhsTail r F _ hc
      (by simp [‹output ≠ count›]) (by simp [‹rhs ≠ count›]),?_,?_,?_,?_,hL,hi,ho,?_,Ds,hlen,?_,hgood⟩
    · exact (embStk_updateR_off F count xs hcountBank).trans hbank
    · simpa [‹volume ≠ count›] using hv
    · simpa [‹saved ≠ count›] using hs
    · simpa [‹tmp ≠ count›] using ht
    · intro k hk
      have hn : k ≠ count := fun he => hk (by simp [he])
      exact (Function.update_of_ne hn _ _).trans (hframe k hk)
    · simpa [‹dst ≠ count›] using harchive
  have hstep : ∀ r < H.Fs.length, ∀ (vi : HS T Q A U) F, Inv r F →
      ∃ vf G m, vf.user = vi.user ∧ m ≤ stepCost ∧
        Exec body step (mk vi F) m (mk vf G) ∧
        G.R count = F.R count ∧ Inv (r+1) G := by
    intro r hr vi F hI
    obtain ⟨hc,hbank,hv,hs,ht,hL,hi,ho,hframe,Ds,hlen,harchive,hgood⟩ := hI
    obtain ⟨C,R,vf,G,m,hu,hm,hex,hcursor,hC,hR,hresidual,hbankG,hLG,hiG,hoG,hframeG⟩ :=
      hcouple r hr vi F hc hbank hv hs ht
    let D := guardedCouplingRowField (2^15*H.p) H.precision H.t H.u H.band H.origin (H.origin+H.span) false C R
    refine ⟨vf,G,m,hu,hm,hex,hframeG count (by simp [‹output ≠ count›.symm,‹rhs ≠ count›.symm,‹dst ≠ count›.symm]),
      hcursor,hbankG.trans hbank,?_,?_,?_,hLG.trans hL,hiG.trans hi,hoG.trans ho,?_,D::Ds,by simp [hlen],?_,?_⟩
    · exact (hframeG volume (by simp [‹volume ≠ output›,‹volume ≠ rhs›,‹volume ≠ dst›])).trans hv
    · exact (hframeG saved (by simp [‹output ≠ saved›.symm,‹rhs ≠ saved›.symm,‹dst ≠ saved›.symm])).trans hs
    · exact (hframeG tmp (by simp [‹output ≠ tmp›.symm,‹rhs ≠ tmp›.symm,‹dst ≠ tmp›.symm])).trans ht
    · intro k hk
      apply (hframeG k ?_).trans (hframe k hk)
      intro hm
      apply hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hm ⊢
      exact Or.inr hm
    · simpa only [List.flatMap_cons,List.append_assoc] using hresidual.trans (congrArg (fun xs => cstream A H.wordWidth (packedInterval H.origin H.span D)++xs) harchive)
    · intro ⟨j,hj⟩
      cases j with
      | zero =>
        refine ⟨C,hC,?_⟩
        simpa only [Nat.add_sub_cancel,Nat.sub_zero,List.getElem_cons_zero] using congrArg
          (fun R => guardedCouplingRowField (2^15*H.p) H.precision H.t H.u H.band H.origin (H.origin+H.span) false C R) hR
      | succ j =>
        have hj' : j < Ds.length := by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using hj
        have hh := hgood ⟨j,hj'⟩
        simpa only [List.getElem_cons_succ,show r+1-1-(j+1) = r-1-j by omega] using hh
  have hinitial : Inv 0 S := by
    refine ⟨h,rfl,rfl,rfl,rfl,rfl,rfl,rfl,(by intro k hk; rfl),[],rfl,rfl,?_⟩
    intro j
    exact Fin.elim0 j
  obtain ⟨v',F,m,hu,hm,hex,hcountF,hI⟩ := countedLoop_exec (body := body) count
    step H.Fs.length
    (stepCost) Inv hstable hstep v S hcountLen hinitial
  obtain ⟨hc,hbank,_,_,_,hL,hi,ho,hframe,Ds,hlen,harchive,hgood⟩ := hI
  obtain ⟨hout,hrhsF⟩ := ReplicaCouplingCursor.finished H output rhs outputTail rhsTail F hc
  exact ⟨v',F,m,Ds,hu,hm,hex,hcountF,hout,hrhsF,hbank,hL,hi,ho,hframe,hlen,harchive,hgood⟩


theorem replicaCouplingLoop_exec (H : ReplicaHaloProblem s) {plan : ReplicaInteriorPlacement T}
    (placement : ReplicaCouplingPlacement plan) (volume output rhs dst saved tmp count : Fin T)
    (hreg : [volume,output,rhs,placement.bank 132,placement.bank 93,placement.bank 110,dst,saved,tmp,count].Nodup)
    (houtput : ∀ i, placement.bank i ≠ output) (hrhs : ∀ i, placement.bank i ≠ rhs)
    (hdst : ∀ i, placement.bank i ≠ dst) (hcountBank : ∀ i, placement.bank i ≠ count) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (hw5 : 5 ≤ H.wordWidth) (hqw : H.precision+4 ≤ H.wordWidth) (hsep : H.span+H.band ≤ s)
    (V : ℕ) (hwide : 8*(H.t+1)^2+4*H.band+8 < 2^V)
    (hfitV : H.origin+(H.span+2*H.band)+s < 2^V)
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
    (hfresh : ∀ k ∈ [(127 : Fin 168),143,166,158,135,167], S.R (placement.bank k) = []) :
    ∃ v' F m, ∃ Ds : List (ZMod s → GaussianInt), v'.user = v.user ∧
      m ≤ H.Fs.length*(replicaCouplingTransitionCost H V+3)+2 ∧
      Exec body (replicaCouplingLoop placement volume output rhs dst saved tmp count hQ) (mk v S) m (mk v' F) ∧
      F.R count = [] ∧ F.R output = outputTail ∧ F.R rhs = rhsTail ∧
      embStk placement.bank F = embStk placement.bank S ∧ F.L = S.L ∧ F.inp = S.inp ∧ F.out = S.out ∧
      (∀ k, k ∉ [count,output,rhs,dst] → F.R k = S.R k) ∧
      Ds.length = H.Fs.length ∧
      F.R dst = Ds.flatMap (fun D => cstream A H.wordWidth (packedInterval H.origin H.span D))++S.R dst ∧
      (∀ j : Fin Ds.length, ReplicaCouplingResidualSpec H (H.Fs.length-1-j.val) Ds[j.val]) := by
  have hregs := hreg
  regs_ne hregs
  apply replicaCouplingTraversal_exec (body := body) H placement volume output rhs dst saved tmp count hreg hcountBank
    (replicaCouplingTransition placement volume output rhs dst saved tmp hQ) (replicaCouplingTransitionCost H V)
    outputTail rhsTail v S h hcountLen
  intro r hr vi F hc hbank hv hs ht
  have hbankR (k : Fin 168) : F.R (placement.bank k) = S.R (placement.bank k) :=
    congrFun (congrArg Stacks.R hbank) k
  have hnative : embStk weightCacheCoreReg (embStk plan.solver F) = embStk weightCacheCoreReg (embStk plan.solver S) := by
    rw [← placement.native_view F,← placement.native_view S,hbank]
  obtain ⟨C,R,vf,G,m,hu,hm,hex,hcursor,hC,hR,hresidual,hbankG,hLG,hiG,hoG,hframeG⟩ :=
    ReplicaCouplingCursor.couple (body := body) H placement volume output rhs dst saved tmp (by regs_nodup)
      houtput hrhs hdst hQ hA hw5 hqw hsep V hwide hfitV has outputTail rhsTail pageTail raw r vi F hc hr
      (by rw [hnative]; exact hready) (by rw [hv]; exact hvolume)
      (by rw [hs]; exact hsaved) (by rw [ht]; exact htmp)
      (by rw [hbankR 140]; exact hrows) (by rw [hbankR 138]; exact hpage)
      (by rw [hbankR 139]; exact hcount) (by rw [hbank]; exact hgeometry)
      (by intro k hk; rw [hbankR k]; exact hfresh k hk)
  exact ⟨C,R,vf,G,m,hu,hm,hex,hcursor,hC,hR,hresidual,hbankG,hLG,hiG,hoG,hframeG⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
