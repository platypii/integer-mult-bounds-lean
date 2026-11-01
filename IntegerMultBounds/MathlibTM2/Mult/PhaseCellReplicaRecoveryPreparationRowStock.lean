module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCollectedReplicaRecoveryRhsStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryPreparationRow
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedReplicaBoundaryRowStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaBoundaryFactory
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryPreparationStock

/-! One amortized recovery-preparation row: solve the actual residual using
retained factors, construct the modified RHS, and move both results to archives. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 257 Q A U}

noncomputable def replicaRecoveryPreparationRowWorkspace (H : ReplicaHaloProblem s)
    (hQ : SS.states ≤ Q) (push : BoundarySolvePushBounds (A := A) (U := U) hQ) (c M : ℕ) : ℕ :=
  (c*replicaBoundaryRhsCost H+push.workspace H.precision H.wordWidth (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card (12*H.band+1))+collectedReplicaRecoveryRhsWorkspace (Q := Q) (A := A) (U := U) H M

theorem replicaRecoveryPreparationRow_exec_within (H : ReplicaHaloProblem s) (target : ℕ)
    (hQ : SS.states ≤ Q) (hA : 96 ≤ A) (hp : 2 ≤ H.p) (hwidth : 8*H.p ≤ 2^H.u)
    (hsep : H.span+H.band ≤ s)
    (htarget : H.target = boundaryHaloTarget H.p H.u (boundaryRecoveryTarget H.p target) H.rhsExp
      (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card)
    (columns : List (ZMod s → GaussianInt))
    (push : BoundarySolvePushBounds (A := A) (U := U) hQ) (c : ℕ)
    (hpush : mnNativePushBound c (replicaBoundaryRhs (P := Empty) (Q := Q) (A := A) (U := U)))
    (M : ℕ) (hpushM : mnProgPush (rmulOne (P := Empty) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ M) (r : ℕ) (hr : r < H.Fs.length)
    (D : ZMod s → GaussianInt) (hD : ReplicaCouplingResidualSpec H r D)
    (x : ZMod s → ℝ)
    (hx : Solves (realMatrix s H.t H.p H.u) (haloVertices s H.origin (H.origin+H.span)) x
      (fun i => (value H.precision (H.Fs.reverse.getD r (fun _ => 0) i)).re))
    (rhsQueueTail residualTail : List (Fin (A+4))) (v : HS 257 Q A U) (S : Stacks 257 A)
    (hfactor : ReplicaBoundaryFactorData H target columns (embStk (Fin.castLE (by decide : 242 ≤ 257)) S))
    (hleft : ∀ i : Fin 242, S.L (Fin.castLE (by decide : 242 ≤ 257) i) =
      S.L (Fin.castLE (by decide : 255 ≤ 257) (replicaBoundaryPhaseReg i)))
    (hphysical : ReplicaBoundaryRhsReady H (embStk replicaBoundaryPhaseReg
      (embStk (Fin.castLE (by decide : 255 ≤ 257)) S)))
    (hcore : ReplicaRecoveryCoreReady H (12*H.band+1) (embStk (Fin.castLE (by decide : 248 ≤ 257)) S))
    (h116 : S.R 116 = []) (h167 : S.R 167 = [])
    (hsource : S.R 93 = cstream A H.wordWidth
      (packedInterval H.origin H.span (H.Fs.reverse.getD r (fun _ => 0)))++rhsQueueTail)
    (hresidual : S.R 238 = cstream A H.wordWidth (packedInterval H.origin H.span D)++residualTail) :
    let Y := boundarySolutionField (haloBoundary s H.t H.band H.origin (H.origin+H.span))
      (replicaBoundarySolution H (12*H.band+1) columns D)
    Nonempty (ReplicaRecoveryRow H target r Y x) ∧
    ∃ v' F n, v'.user = v.user ∧ n ≤ replicaRecoveryPreparationRowCost H ∧
      (∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          replicaRecoveryPreparationRowWorkspace H hQ push c M)
        depth (replicaRecoveryPreparationRow hQ) (mk v S) n (mk v' F)) ∧
      F.R 93 = rhsQueueTail ∧ F.R 238 = residualTail ∧ F.R 110 = S.R 110 ∧ F.R 132 = S.R 132 ∧
      F.R 125 = cstream A H.wordWidth (packedInterval H.origin H.span Y)++S.R 125 ∧
      F.R 256 = cstream A H.wordWidth (packedInterval H.origin H.span (replicaRecoveryRhs H r Y))++S.R 256 ∧
      ReplicaBoundaryFactorData H target columns (embStk (Fin.castLE (by decide : 242 ≤ 257)) F) ∧
      ReplicaRecoveryCoreReady H (12*H.band+1) (embStk (Fin.castLE (by decide : 248 ≤ 257)) F) ∧
      ReplicaBoundaryRhsReady H (embStk replicaBoundaryPhaseReg (embStk (Fin.castLE (by decide : 255 ≤ 257)) F)) ∧
      F.R 116 = [] ∧ F.R 167 = [] ∧
      (∀ k : Fin 257, k ∉ [93,110,116,125,132,143,167,238,256] → F.R k = S.R k) ∧
      F.L = S.L ∧ F.inp = S.inp ∧ F.out = S.out ∧ mnSize (mk v' F) = mnSize (mk v S) := by
  dsimp only
  let solution := replicaBoundarySolution H (12*H.band+1) columns D
  obtain ⟨hlen,hfits,haccuracy⟩ := ReplicaCouplingResidualSpec.boundary_solution H A
    (boundaryRecoveryTarget H.p target) (12*H.band+1) columns (by omega) hp hwidth htarget
    hfactor.prepared.length hfactor.prepared.format hfactor.prepared.stage hfactor.error r hr D hD x hx
  refine ⟨replicaRecoveryRow_of_boundary_solution H target r htarget hp hwidth hr solution x hlen hfits haccuracy hx,?_⟩
  let e : Fin 255 → Fin 257 := Fin.castLE (by decide)
  have hinj : Function.Injective e := by intro i j he; exact Fin.ext (congrArg (fun k : Fin 257 => k.val) he)
  let words := cstream A H.wordWidth solution++residualTail
  let T : Stacks 257 A := {S with R := Function.update (Function.update S.R 238 words) 143 []}
  obtain ⟨vi,m,hu,hm,he,hcoreJ,hpagesJ,hphysicalJ⟩ := retainedReplicaBoundaryRow_exec_within
    (body := fun z : Empty => nomatch z) H hQ hA hp hwidth (boundaryRecoveryTarget H.p target)
    (12*H.band+1) columns push c hpush htarget hfactor.prepared r hr D hD (embDn e v) (embStk e S) residualTail
    hleft hphysical hresidual hcore hfactor.pages
  obtain ⟨v₁,hv₁,hu₁,he₁⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim) hinj
    (fun z => nomatch z) (he 0).toExec v rfl S rfl
  have ht : embOvr e (retainedReplicaBoundaryState (embStk e S) words).get S = T := by
    unfold retainedReplicaBoundaryState
    rw [embOvr_updateR_updateR hinj]
    rfl
  have hproj : embStk e T = retainedReplicaBoundaryState (embStk e S) words := by
    rw [←ht,embStk_ovr hinj]
  have hcoreT : ReplicaRecoveryCoreReady H (12*H.band+1)
      (embStk (Fin.castLE (by decide : 248 ≤ 257)) T) := by
    change ReplicaRecoveryCoreReady H _ (embStk (Fin.castLE (by decide : 248 ≤ 255)) (embStk e T))
    rw [hproj]
    exact hcoreJ
  have hphysicalT : ReplicaBoundaryRhsReady H (embStk replicaBoundaryPhaseReg (embStk e T)) := by
    rw [hproj]
    exact hphysicalJ
  have hframeT (k : Fin 257) (hk : k ∉ [143,238]) : T.R k = S.R k := by
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hk
    simp [T,hk.1,hk.2]
  obtain ⟨v₂,F,n,hu₂,hn,he₂,h93,h238,h110,h132,h125,h256,hcoreF,hphysicalF,h116F,h167F,hframeF,hLF,hinp,hout⟩ :=
    collectedReplicaRecoveryRhs_exec_within (body := body) H hQ hA hsep r (12*H.band+1) solution hlen hfits
      rhsQueueTail residualTail M hpushM v₁ T hphysicalT hcoreT
      ((hframeT 116 (by decide)).trans h116) ((hframeT 167 (by decide)).trans h167)
      ((hframeT 93 (by decide)).trans hsource) (by simp [T,words])
  have hL : F.L = S.L := hLF
  have hframeAll (k : Fin 257) (hk : k ∉ [93,238,125,256]) : F.R k = S.R k := by
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hk
    by_cases h110k : k = 110
    · subst k; exact h110.trans (hframeT 110 (by decide))
    by_cases h132k : k = 132
    · subst k; exact h132.trans (hframeT 132 (by decide))
    by_cases h116k : k = 116
    · subst k; exact h116F.trans h116.symm
    by_cases h167k : k = 167
    · subst k; exact h167F.trans h167.symm
    by_cases h143k : k = 143
    · subst k
      rw [hframeF 143 (by decide)]
      change [] = S.R 143
      exact hcore.rhs.symm
    apply (hframeF k ?_).trans (hframeT k ?_)
    · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
      exact ⟨hk.1,h110k,h116k,hk.2.2.1,h132k,h167k,hk.2.1,hk.2.2.2⟩
    · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
      exact ⟨h143k,hk.2.1⟩
  have hstock : mnSize (mk v₂ F) = mnSize (mk v S) := by
    apply replicaRecoveryPreparation_stock H r D
      (boundarySolutionField (haloBoundary s H.t H.band H.origin (H.origin+H.span)) solution)
      rhsQueueTail residualTail v v₂ S F hsource hresidual h93 h238 ?_ ?_ hframeAll hL hinp hout
    · rw [h125,hframeT 125 (by decide)]
    · rw [h256,hframeT 256 (by decide)]
  have hhigh (k : Fin 242) (hk : 168 ≤ k.val) (h238 : k ≠ 238) :
      F.R (Fin.castLE (by decide : 242 ≤ 257) k) = S.R (Fin.castLE (by decide : 242 ≤ 257) k) := by
    apply (hframeF _ ?_).trans (hframeT _ ?_)
    all_goals
      simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff,Fin.castLE] at h238 ⊢
      have hi := k.isLt
      norm_num at h238 ⊢
      omega
  refine ⟨v₂,F,m+n,hu₂.trans (hu₁.trans hu),by unfold replicaRecoveryPreparationRowCost; omega,
    (fun depth => by
      have hb := exec_emb_within_stock_of_exec (ι := Empty.elim) (body' := body)
        hinj (fun z => nomatch z) (he depth) v rfl S rfl he₁
      exact mn_seq_within_add (a := (c*replicaBoundaryRhsCost H+push.workspace H.precision H.wordWidth (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card (12*H.band+1))) (b := collectedReplicaRecoveryRhsWorkspace (Q := Q) (A := A) (U := U) H M)
        (hb.cast rfl (congrArg (mk v₁) ht)) (he₂ depth)),h93,h238,
    h110.trans (hframeT 110 (by decide)),h132.trans (hframeT 132 (by decide)),?_,?_,?_,hcoreF,hphysicalF,
    h116F,h167F,?_,hL,hinp,hout,hstock⟩
  · rw [h125,hframeT 125 (by decide)]
  · rw [h256,hframeT 256 (by decide)]
  · apply ReplicaBoundaryFactorData.of_runtime_frame H target columns hfactor
      (congrArg (fun L => L ∘ Fin.castLE (by decide : 242 ≤ 257)) hL) ?_ ?_ hhigh
    · intro k hk
      apply (hframeF _ ?_).trans (hframeT _ ?_)
      all_goals
        simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff,Fin.castLE]
        norm_num
        omega
    · exact (hframeF 119 (by decide)).trans (hframeT 119 (by decide))
  · intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hk
    exact (hframeF k (by simp_all)).trans (hframeT k (by simp_all))

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
