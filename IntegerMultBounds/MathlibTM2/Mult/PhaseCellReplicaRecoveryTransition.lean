module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryCursor
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCompleteReplicaRow

/-! The actual complete row advances the paired recovery cursor and publishes
a suffix-independent full-halo accuracy witness for the recovered field. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.NLogN.SchurDominance IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.BandFactor IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 255 Q A U}

def RecoveredReplicaRowSpec (H : ReplicaHaloProblem s) (target : ℕ) (X : ℕ → ZMod s → ℝ)
    (r : ℕ) (E : ZMod s → GaussianInt) : Prop :=
  (∀ i, Fits H.wordWidth (E i)) ∧
    PhaseCellInterface.ErrorOn (haloVertices s H.origin (H.origin+H.span))
      (fun i => (packedIntervalRead H.precision H.wordWidth H.origin
        (cstream A H.wordWidth (packedInterval H.origin H.span E)) i).re) (X r) (1/(2 : ℝ)^target)

theorem ReplicaRecoveryCursor.execute (H : ReplicaHaloProblem s)
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
    ∀ (residualTail rhsTail outputTail : List (Fin (A+4))) r,
    ∀ (v : HS 255 Q A U) (S : Stacks 255 A),
    ReplicaRecoveryCursor H (RecoveredReplicaRowSpec (A := A) H target X) residualTail rhsTail outputTail r S →
    r < H.Fs.length →
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
    ∃ v' F n, v'.user = v.user ∧ n ≤ completeReplicaRowCost H target W ∧
      Exec body (completeReplicaRow hR hQ) (Host.mk v S) n (Host.mk v' F) ∧
      ReplicaRecoveryCursor H (RecoveredReplicaRowSpec (A := A) H target X) residualTail rhsTail outputTail (r+1) F ∧
      F.R 110 = S.R 110 ∧ F.R 132 = S.R 132 ∧
      ReplicaRecoveryCoreReady H W (embStk (Fin.castLE (by decide : 248 ≤ 255)) F) ∧
      ReplicaBoundaryRhsReady H (embStk replicaBoundaryPhaseReg F) ∧
      F.R 116 = [] ∧ F.R 167 = [] ∧ F.L = S.L ∧ F.inp = S.inp ∧ F.out = S.out ∧
      (∀ k : Fin 255, 248 ≤ k.val → F.L k = S.L k ∧ F.R k = S.R k) ∧
      (∀ bo hf df, PackedBoundaryFactorPages bo hf df (embStk (Fin.castLE (by decide : 242 ≤ 255)) S) →
        PackedBoundaryFactorPages bo hf df (embStk (Fin.castLE (by decide : 242 ≤ 255)) F)) := by
  dsimp only
  intro htarget hcolumns htable X hX residualTail rhsTail outputTail r v S
    hcursor hr hleft hpages hphysical hcore h116 h167
  obtain ⟨D,Ds,hlen,hD,hres,hgood,hrhs⟩ := hcursor.head H _ _ _ _ _ _ hr
  obtain ⟨v',F,n,E,hu,hn,he,h93,h238,h110,h132,h125,hfits,herror,hcoreF,hphysicalF,
    h116F,h167F,hL,hinp,hout,hpersistent,hfactor⟩ := completeReplicaRow_exec
      (body := body) H hR hQ hA hp hwidth hsep hpad target W columns htarget hcolumns htable
      (H.Fs.length-1-r) (by omega) D hD (X r) (hX r hr)
      ((H.Fs.drop (r+1)).flatMap (fun R => cstream A H.wordWidth (packedInterval H.origin H.span R))++rhsTail)
      (Ds.flatMap (fun D => cstream A H.wordWidth (packedInterval H.origin H.span D))++residualTail)
      v S hleft hpages hphysical hcore h116 h167 hrhs hres
  have hE : RecoveredReplicaRowSpec (A := A) H target X r E := by
    refine ⟨hfits,?_⟩
    intro i hi
    have hh := herror i hi
    obtain ⟨ha,hb⟩ := (mem_haloVertices _ _ _).mp hi
    have hread := packedIntervalRead_suffix H.precision H.wordWidth H.origin H.span E
      ([] : List (Fin (A+4))) (S.R 125) H.span_fit i ha hb
    simp only [List.append_nil] at hread
    rw [h125] at hh
    change ‖(packedIntervalRead H.precision H.wordWidth H.origin
      (cstream A H.wordWidth (packedInterval H.origin H.span E)) i).re-X r i‖ ≤ _
    rw [hread]
    exact hh
  exact ⟨v',F,n,hu,hn,he,
    hcursor.advance H _ _ _ _ _ _ hr Ds hlen hgood E hE F h238 h93 h125,
    h110,h132,hcoreF,hphysicalF,h116F,h167F,hL,hinp,hout,hpersistent,hfactor⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
