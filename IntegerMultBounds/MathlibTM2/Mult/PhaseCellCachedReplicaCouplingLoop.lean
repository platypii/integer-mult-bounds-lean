module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaCouplingLoop
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedReplicaCouplingTransition

/-! Instantiate the common counted traversal with cached coupling transitions.
Restored shared banks carry both mask streams through all replica rows. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

def cachedReplicaCouplingTransitionCost (H : ReplicaHaloProblem s) (V : ℕ) :=
  stageReplicaCouplingRowCost (H.span*H.wordWidth)+
    (cachedReplicaLocalCouplingCost false (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band
      H.origin (H.origin+H.span) H.origin H.span V+finishReplicaCouplingRowCost (H.span*H.wordWidth))

noncomputable def cachedReplicaCouplingLoop {plan : ReplicaInteriorPlacement T}
    (placement : ReplicaCouplingPlacement plan) (volume output rhs dst saved tmp count : Fin T)
    (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  countedLoop count (cachedReplicaCouplingTransition placement volume output rhs dst saved tmp hQ)

theorem cachedReplicaCouplingLoop_exec (H : ReplicaHaloProblem s) {plan : ReplicaInteriorPlacement T}
    (placement : ReplicaCouplingPlacement plan) (volume output rhs dst saved tmp count : Fin T)
    (hreg : [volume,output,rhs,placement.bank 132,placement.bank 93,placement.bank 110,dst,saved,tmp,count].Nodup)
    (houtput : ∀ i, placement.bank i ≠ output) (hrhs : ∀ i, placement.bank i ≠ rhs)
    (hdst : ∀ i, placement.bank i ≠ dst) (hcountBank : ∀ i, placement.bank i ≠ count) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
      Exec body (cachedReplicaCouplingLoop placement volume output rhs dst saved tmp count hQ) (mk v S) m (mk v' F) ∧
      F.R count = [] ∧ F.R output = outputTail ∧ F.R rhs = rhsTail ∧
      embStk placement.bank F = embStk placement.bank S ∧ F.L = S.L ∧ F.inp = S.inp ∧ F.out = S.out ∧
      (∀ k, k ∉ [count,output,rhs,dst] → F.R k = S.R k) ∧
      Ds.length = H.Fs.length ∧
      F.R dst = Ds.flatMap (fun D => cstream A H.wordWidth (packedInterval H.origin H.span D))++S.R dst ∧
      (∀ j : Fin Ds.length, ReplicaCouplingResidualSpec H (H.Fs.length-1-j.val) Ds[j.val]) := by
  have hregs := hreg
  regs_ne hregs
  apply replicaCouplingTraversal_exec (body := body) H placement volume output rhs dst saved tmp count hreg hcountBank
    (cachedReplicaCouplingTransition placement volume output rhs dst saved tmp hQ) (cachedReplicaCouplingTransitionCost H V)
    outputTail rhsTail v S h hcountLen
  intro r hr vi F hc hbank hv hs ht
  have hbankR (k : Fin 168) : F.R (placement.bank k) = S.R (placement.bank k) :=
    congrFun (congrArg Stacks.R hbank) k
  have hnative : embStk weightCacheCoreReg (embStk plan.solver F) = embStk weightCacheCoreReg (embStk plan.solver S) := by
    rw [← placement.native_view F,← placement.native_view S,hbank]
  obtain ⟨C,R,vf,G,m,hu,hm,hex,hcursor,hC,hR,hresidual,hbankG,hLG,hiG,hoG,hframeG⟩ :=
    ReplicaCouplingCursor.couple_cached (body := body) H placement volume output rhs dst saved tmp (by regs_nodup)
      houtput hrhs hdst hQ hA hw5 hqw hsep V hNV has outputTail rhsTail pageTail raw r vi F hc hr
      (by rw [hnative]; exact hready) (by rw [hv]; exact hvolume)
      (by rw [hs]; exact hsaved) (by rw [ht]; exact htmp)
      (by rw [hbankR 140]; exact hrows) (by rw [hbankR 138]; exact hpage)
      (by rw [hbankR 139]; exact hcount) (by rw [hbank]; exact hgeometry)
      (by intro k hk; rw [hbankR k]; exact hfresh k hk)
    (by rw [hbankR 159]; exact h159) (by rw [hbankR 161]; exact h161)
  exact ⟨C,R,vf,G,m,hu,hm,hex,hcursor,hC,hR,hresidual,hbankG,hLG,hiG,hoG,hframeG⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
