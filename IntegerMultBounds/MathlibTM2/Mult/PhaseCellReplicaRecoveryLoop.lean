module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedBankLoop
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryTransition
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCompleteReplicaRow

/-! A counted traversal of actual residual/original-RHS pairs. Shared setup
is retained, and every archived output has the original full-halo error bound. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.NLogN.SchurDominance IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.BandFactor IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 256 Q A U}

def replicaRecoveryWorkerReg : Fin 255 → Fin 256 := Fin.castLE (by decide)

noncomputable def replicaRecoveryLoop (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 256 Q A U :=
  countedLoop 255 (embProg replicaRecoveryWorkerReg Empty.elim (completeReplicaRow (P := Empty) hR hQ))

def RecoveredReplicaArchive (H : ReplicaHaloProblem s) (target : ℕ) (X : ℕ → ZMod s → ℝ)
    (outputTail : List (Fin (A+4))) (F : Stacks 255 A) : Prop :=
  ∃ Es : List (ZMod s → GaussianInt), Es.length = H.Fs.length ∧
        F.R 125 = Es.flatMap (fun E => cstream A H.wordWidth (packedInterval H.origin H.span E))++outputTail ∧
        ∀ j : Fin Es.length, RecoveredReplicaRowSpec (A := A) H target X (H.Fs.length-1-j.val) Es[j.val]

theorem replicaRecoveryLoop_exec (H : ReplicaHaloProblem s)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A) (hp : 2 ≤ H.p) (hwidth : 8*H.p ≤ 2^H.u)
    (hsep : H.span+H.band ≤ s)
    (hpad : 2*((s/(H.t-s)+1)-2*H.band) ≤ 2^H.l+1)
    (target W : ℕ) (columns : List (ZMod s → GaussianInt)) :
    let I := haloInterior s H.t H.band H.origin (H.origin+H.span)
    let B := haloBoundary s H.t H.band H.origin (H.origin+H.span)
    let bits := boundaryTableBits H.p (boundaryRecoveryTarget H.p target) H.rhsExp B.card
    H.target = boundaryHaloTarget H.p H.u (boundaryRecoveryTarget H.p target) H.rhsExp B.card →
    PreparedBoundaryColumns A H.p bits H.precision H.wordWidth W B columns →
    (∀ i ∈ B, ∀ j ∈ B, |bandBoundaryTable B W (computedBoundaryTable A H.precision H.wordWidth B columns) i j-
      (SchurDominance.run (realMatrix s H.t H.p H.u) (haloVertices s H.origin (H.origin+H.span)) I.toList).1 i j| ≤ 1/(2 : ℝ)^bits) →
    ∀ (X : ℕ → ZMod s → ℝ),
    (∀ r < H.Fs.length, Solves (realMatrix s H.t H.p H.u) (haloVertices s H.origin (H.origin+H.span)) (X r)
      (fun i => (value H.precision (H.Fs.reverse.getD (H.Fs.length-1-r) (fun _ => 0) i)).re)) →
    ∀ (residualTail rhsTail outputTail : List (Fin (A+4))),
    ∀ (v : HS 256 Q A U) (G : Stacks 256 A),
    let S := embStk replicaRecoveryWorkerReg G
    (G.R 255).length = H.Fs.length →
    ReplicaRecoveryCursor H (RecoveredReplicaRowSpec (A := A) H target X) residualTail rhsTail outputTail 0 S →
    (∀ i : Fin 242, S.L (Fin.castLE (by decide) i) = S.L (replicaBoundaryPhaseReg i)) →
    PackedBoundaryFactorPages
      (cstream A H.wordWidth ((naturalLineLc H.precision (factorNewtonSteps H.p H.precision) W B.card
        (factorRankIntegerMatrix B W columns)).map colC).flatten)
      (cstream A H.wordWidth ((naturalLineUc H.precision (factorNewtonSteps H.p H.precision) W B.card
        (factorRankIntegerMatrix B W columns)).map colC).flatten)
      (cstream A H.wordWidth ((naturalLineRcs H.precision (factorNewtonSteps H.p H.precision) W B.card
        (factorRankIntegerMatrix B W columns)).map fun z => (⟨z,0⟩ : GaussianInt)))
      (embStk (Fin.castLE (by decide : 242 ≤ 255)) S) →
    ReplicaBoundaryRhsReady H (embStk replicaBoundaryPhaseReg S) →
    ReplicaRecoveryCoreReady H W (embStk (Fin.castLE (by decide : 248 ≤ 255)) S) →
    S.R 116 = [] → S.R 167 = [] →
    ∃ v' G' n, v'.user = v.user ∧ n ≤ H.Fs.length*(completeReplicaRowCost H target W+3)+2 ∧
      Exec body (replicaRecoveryLoop hR hQ) (Host.mk v G) n (Host.mk v' G') ∧
      G'.R 255 = [] ∧
      let F := embStk replicaRecoveryWorkerReg G'
      F.R 238 = residualTail ∧ F.R 93 = rhsTail ∧
      RecoveredReplicaArchive H target X outputTail F ∧
      ReplicaRecoveryCoreReady H W (embStk (Fin.castLE (by decide : 248 ≤ 255)) F) ∧
      ReplicaBoundaryRhsReady H (embStk replicaBoundaryPhaseReg F) ∧
      F.R 116 = [] ∧ F.R 167 = [] ∧ F.L = S.L ∧ F.inp = S.inp ∧ F.out = S.out ∧
      F.R 110 = S.R 110 ∧ F.R 132 = S.R 132 ∧
      (∀ k : Fin 255, 248 ≤ k.val → F.R k = S.R k) ∧
      (∀ bo hf df, PackedBoundaryFactorPages bo hf df (embStk (Fin.castLE (by decide : 242 ≤ 255)) S) →
        PackedBoundaryFactorPages bo hf df (embStk (Fin.castLE (by decide : 242 ≤ 255)) F)) := by
  dsimp only
  intro htarget hcolumns htable X hX residualTail rhsTail outputTail v G
    hcount hcursor hleft hpages hphysical hcore h116 h167
  let S := embStk replicaRecoveryWorkerReg G
  let Inv := fun r F =>
    ReplicaRecoveryCursor H (RecoveredReplicaRowSpec (A := A) H target X) residualTail rhsTail outputTail r F ∧
    ReplicaRecoveryCoreReady H W (embStk (Fin.castLE (by decide : 248 ≤ 255)) F) ∧
    ReplicaBoundaryRhsReady H (embStk replicaBoundaryPhaseReg F) ∧
    F.R 116 = [] ∧ F.R 167 = [] ∧ F.L = S.L ∧ F.inp = S.inp ∧ F.out = S.out ∧
    F.R 110 = S.R 110 ∧ F.R 132 = S.R 132 ∧
    (∀ k : Fin 255, 248 ≤ k.val → F.R k = S.R k) ∧
    (∀ bo hf df, PackedBoundaryFactorPages bo hf df (embStk (Fin.castLE (by decide : 242 ≤ 255)) S) →
      PackedBoundaryFactorPages bo hf df (embStk (Fin.castLE (by decide : 242 ≤ 255)) F))
  have hstep : ∀ r < H.Fs.length, ∀ (vi : HS 255 Q A U) F, Inv r F →
      ∃ vf J n, vf.user = vi.user ∧ n ≤ completeReplicaRowCost H target W ∧
        Exec (fun z : Empty => nomatch z) (completeReplicaRow hR hQ)
          (Host.mk vi F) n (Host.mk vf J) ∧ Inv (r+1) J := by
    intro r hr vi F hI
    obtain ⟨hc,hcoreF,hphysicalF,h116F,h167F,hL,hinp,hout,h110,h132,hpersistent,hfactor⟩ := hI
    obtain ⟨vf,J,n,hu,hn,he,hcJ,h110J,h132J,hcoreJ,hphysicalJ,h116J,h167J,hLJ,hinpJ,houtJ,
      hpersistentJ,hfactorJ⟩ := ReplicaRecoveryCursor.execute (body := fun z : Empty => nomatch z)
        H hR hQ hA hp hwidth hsep hpad target W columns htarget hcolumns htable X hX
        residualTail rhsTail outputTail r vi F hc hr
        (by intro i; rw [hL]; exact hleft i)
        (hfactor _ _ _ hpages) hphysicalF hcoreF h116F h167F
    exact ⟨vf,J,n,hu,hn,he,hcJ,hcoreJ,hphysicalJ,h116J,h167J,hLJ.trans hL,
      hinpJ.trans hinp,houtJ.trans hout,h110J.trans h110,h132J.trans h132,
      (fun k hk => (hpersistentJ k hk).2.trans (hpersistent k hk)),
      (fun bo hf df h => hfactorJ bo hf df (hfactor bo hf df h))⟩
  have hinitial : Inv 0 S :=
    ⟨hcursor,hcore,hphysical,h116,h167,rfl,rfl,rfl,rfl,rfl,
      (fun k hk => rfl),(fun bo hf df h => h)⟩
  obtain ⟨v',G',n,hu,hn,he,h255,hI⟩ := countedBankLoop_exec (body := body)
    replicaRecoveryWorkerReg (by intro i j hij; exact Fin.ext (congrArg (fun k : Fin 256 => k.val) hij))
    255 (by intro i hi; have hv := congrArg Fin.val hi; have hb := i.isLt; change i.val = 255 at hv; omega)
    (completeReplicaRow (P := Empty) hR hQ) H.Fs.length (completeReplicaRowCost H target W)
    Inv hstep v G hcount hinitial
  obtain ⟨hc,hcoreF,hphysicalF,h116F,h167F,hL,hinp,hout,h110,h132,hpersistent,hfactor⟩ := hI
  obtain ⟨hres,hrhs,houtput⟩ := hc.finished H _ _ _ _ _
  exact ⟨v',G',n,hu,hn,he,h255,hres,hrhs,houtput,hcoreF,hphysicalF,
    h116F,h167F,hL,hinp,hout,h110,h132,hpersistent,hfactor⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
