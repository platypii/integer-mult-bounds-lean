module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedBankLoop
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryPreparationCursor
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryPreparationRow

/-! Prepare every recovery RHS in one counted traversal. The numerical batch
and both aligned archives are consequences of the executed row transition. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.NLogN.SchurDominance IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 258 Q A U}

def replicaRecoveryPreparationWorkerReg : Fin 257 → Fin 258 := Fin.castLE (by decide)

noncomputable def replicaRecoveryPreparationLoop (hQ : SS.states ≤ Q) : Pr P 258 Q A U :=
  countedLoop 257 (embProg replicaRecoveryPreparationWorkerReg Empty.elim
    (replicaRecoveryPreparationRow (P := Empty) hQ))

theorem replicaRecoveryPreparationLoop_exec (H : ReplicaHaloProblem s) (target : ℕ)
    (hQ : SS.states ≤ Q) (hA : 96 ≤ A) (hp : 2 ≤ H.p) (hwidth : 8*H.p ≤ 2^H.u)
    (hsep : H.span+H.band ≤ s)
    (htarget : H.target = boundaryHaloTarget H.p H.u (boundaryRecoveryTarget H.p target) H.rhsExp
      (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card)
    (columns : List (ZMod s → GaussianInt)) (X : ℕ → ZMod s → ℝ)
    (hX : ∀ r < H.Fs.length, Solves (realMatrix s H.t H.p H.u) (haloVertices s H.origin (H.origin+H.span)) (X r)
      (fun i => (value H.precision (H.Fs.reverse.getD r (fun _ => 0) i)).re))
    (residualTail rhsTail boundaryTail recoveryTail : List (Fin (A+4)))
    (v : HS 258 Q A U) (G : Stacks 258 A) :
    let S := embStk replicaRecoveryPreparationWorkerReg G
    (G.R 257).length = H.Fs.length →
    ReplicaRecoveryPreparationCursor H target X residualTail rhsTail boundaryTail recoveryTail 0 S →
    ReplicaBoundaryFactorData H target columns (embStk (Fin.castLE (by decide : 242 ≤ 257)) S) →
    (∀ i : Fin 242, S.L (Fin.castLE (by decide : 242 ≤ 257) i) =
      S.L (Fin.castLE (by decide : 255 ≤ 257) (replicaBoundaryPhaseReg i))) →
    ReplicaBoundaryRhsReady H (embStk replicaBoundaryPhaseReg (embStk (Fin.castLE (by decide : 255 ≤ 257)) S)) →
    ReplicaRecoveryCoreReady H (12*H.band+1) (embStk (Fin.castLE (by decide : 248 ≤ 257)) S) →
    S.R 116 = [] → S.R 167 = [] →
    ∃ v' G' n, ∃ B : ReplicaRecoveryBatch H target X,
      v'.user = v.user ∧ n ≤ H.Fs.length*(replicaRecoveryPreparationRowCost H+3)+2 ∧
      Exec body (replicaRecoveryPreparationLoop hQ) (mk v G) n (mk v' G') ∧ G'.R 257 = [] ∧
      let F := embStk replicaRecoveryPreparationWorkerReg G'
      F.R 238 = residualTail ∧ F.R 93 = rhsTail ∧
      F.R 125 = (List.ofFn B.boundary).flatMap
        (fun Y => cstream A H.wordWidth (packedInterval H.origin H.span Y))++boundaryTail ∧
      F.R 256 = B.inputs.reverse.flatMap
        (fun R => cstream A H.wordWidth (packedInterval H.origin H.span R))++recoveryTail ∧
      ReplicaBoundaryFactorData H target columns (embStk (Fin.castLE (by decide : 242 ≤ 257)) F) ∧
      ReplicaRecoveryCoreReady H (12*H.band+1) (embStk (Fin.castLE (by decide : 248 ≤ 257)) F) ∧
      ReplicaBoundaryRhsReady H (embStk replicaBoundaryPhaseReg (embStk (Fin.castLE (by decide : 255 ≤ 257)) F)) ∧
      F.R 116 = [] ∧ F.R 167 = [] ∧ F.L = S.L ∧ F.inp = S.inp ∧ F.out = S.out ∧
      F.R 110 = S.R 110 ∧ F.R 132 = S.R 132 ∧
      (∀ k : Fin 257, k ∉ [93,110,116,125,132,143,167,238,256] → F.R k = S.R k) ∧
      mnSize (mk (embDn replicaRecoveryPreparationWorkerReg v') F) =
        mnSize (mk (embDn replicaRecoveryPreparationWorkerReg v) S) := by
  dsimp only
  intro hcount hcursor hfactor hleft hphysical hcore h116 h167
  let S := embStk replicaRecoveryPreparationWorkerReg G
  let Inv := fun r (F : Stacks 257 A) =>
    ReplicaRecoveryPreparationCursor H target X residualTail rhsTail boundaryTail recoveryTail r F ∧
    ReplicaBoundaryFactorData H target columns (embStk (Fin.castLE (by decide : 242 ≤ 257)) F) ∧
    ReplicaRecoveryCoreReady H (12*H.band+1) (embStk (Fin.castLE (by decide : 248 ≤ 257)) F) ∧
    ReplicaBoundaryRhsReady H (embStk replicaBoundaryPhaseReg (embStk (Fin.castLE (by decide : 255 ≤ 257)) F)) ∧
    F.R 116 = [] ∧ F.R 167 = [] ∧ F.L = S.L ∧ F.inp = S.inp ∧ F.out = S.out ∧
    F.R 110 = S.R 110 ∧ F.R 132 = S.R 132 ∧
    (∀ k : Fin 257, k ∉ [93,110,116,125,132,143,167,238,256] → F.R k = S.R k) ∧
    mnSize (mk (embDn replicaRecoveryPreparationWorkerReg v) F) =
      mnSize (mk (embDn replicaRecoveryPreparationWorkerReg v) S)
  have hstep : ∀ r < H.Fs.length, ∀ (vi : HS 257 Q A U) F, Inv r F →
      ∃ vf J n, vf.user = vi.user ∧ n ≤ replicaRecoveryPreparationRowCost H ∧
        Exec (fun z : Empty => nomatch z) (replicaRecoveryPreparationRow hQ) (mk vi F) n (mk vf J) ∧ Inv (r+1) J := by
    intro r hr vi F hI
    obtain ⟨hc,hfactorF,hcoreF,hphysicalF,h116F,h167F,hL,hinp,hout,h110,h132,hframe,hstockF⟩ := hI
    obtain ⟨D,Ds,hlen,hD,hres,hgood,hrhs⟩ := hc.head hr
    obtain ⟨hY,vf,J,n,hu,hn,he,h93,h238,h110J,h132J,h125,h256,hfactorJ,hcoreJ,hphysicalJ,
      h116J,h167J,hframeJ,hLJ,hinpJ,houtJ,hstockJ⟩ :=
      (show Nonempty (ReplicaRecoveryRow H target (H.Fs.length-1-r)
          (boundarySolutionField (haloBoundary s H.t H.band H.origin (H.origin+H.span))
            (replicaBoundarySolution H (12*H.band+1) columns D)) (X (H.Fs.length-1-r))) ∧ _ from
        replicaRecoveryPreparationRow_exec (body := fun z : Empty => nomatch z) H target hQ hA hp hwidth hsep
          htarget columns (H.Fs.length-1-r) (by omega) D hD (X (H.Fs.length-1-r)) (hX _ (by omega))
          ((H.Fs.drop (r+1)).flatMap (fun C => cstream A H.wordWidth (packedInterval H.origin H.span C))++rhsTail)
          (Ds.flatMap (fun D => cstream A H.wordWidth (packedInterval H.origin H.span D))++residualTail)
          vi F hfactorF (by intro i; rw [hL]; exact hleft i) hphysicalF hcoreF h116F h167F hrhs hres)
    have hcJ := hc.advance hr Ds hlen hgood _ hY J h238 h93 h125 h256
    exact ⟨vf,J,n,hu,hn,he,hcJ,hfactorJ,hcoreJ,hphysicalJ,h116J,h167J,
      hLJ.trans hL,hinpJ.trans hinp,houtJ.trans hout,h110J.trans h110,h132J.trans h132,
      (fun k hk => (hframeJ k hk).trans (hframe k hk)),hstockJ.trans hstockF⟩
  have hinitial : Inv 0 S :=
    ⟨hcursor,hfactor,hcore,hphysical,h116,h167,rfl,rfl,rfl,rfl,rfl,(fun _ _ => rfl),rfl⟩
  obtain ⟨v',G',n,hu,hn,he,hcountF,hfinal⟩ := countedBankLoop_exec (body := body)
    replicaRecoveryPreparationWorkerReg (by intro i j he; exact Fin.ext (congrArg (fun k : Fin 258 => k.val) he))
    257 (by intro i he; have hh := congrArg (fun k : Fin 258 => k.val) he; have hi := i.isLt
            change i.val = 257 at hh; omega)
    (replicaRecoveryPreparationRow hQ) H.Fs.length (replicaRecoveryPreparationRowCost H) Inv hstep v G hcount hinitial
  obtain ⟨hc,hfactorF,hcoreF,hphysicalF,h116F,h167F,hL,hinp,hout,h110,h132,hframe,hstock⟩ := hfinal
  obtain ⟨h238,h93,B,h125,h256⟩ := hc.finished
  exact ⟨v',G',n,B,hu,hn,he,hcountF,h238,h93,h125,h256,hfactorF,hcoreF,hphysicalF,
    h116F,h167F,hL,hinp,hout,h110,h132,hframe,hstock⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
