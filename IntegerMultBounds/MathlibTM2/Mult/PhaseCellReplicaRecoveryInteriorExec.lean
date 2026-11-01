module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryBatchSource
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRealReplicaHaloOutput

/-! Install the computed recovery RHS archive and execute the existing shared
interior controller once, including its paid real projection. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

noncomputable def replicaRecoveryInterior (plan : ReplicaInteriorPlacement T) (source dst : Fin T)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  .seq (reverseCopyRows (plan.gather 121) (plan.gather 89) (plan.gather 123) source
    (plan.gather 88) (plan.gather 124) (plan.gather 104) (plan.gather 105))
    (realInitializedReplicaHaloLoop plan dst hR hQ)

def replicaRecoveryInteriorTime (H J : ReplicaHaloProblem s) :=
  reverseCopyRowsCost H.Fs.length (H.span*H.wordWidth)+
    (allocateZeroLineCost J.Fs.length (J.span*J.wordWidth)+
      (placedHaloLengthKeysCost s J.t J.band J.origin (J.origin+J.span) J.metadataWidth+
        (((haloLengthKeys s J.t J.band J.origin (J.origin+J.span)).map (fun L => J.keyCost L+3)).sum+2)))+
    realReplicaRowsCost J.Fs.length (J.span*J.wordWidth)

noncomputable def replicaRecoveryInteriorWorkspace (H J : ReplicaHaloProblem s) (hQ : SS.states ≤ Q) (R K : ℕ) :=
  2*reverseCopyRowsCost H.Fs.length (H.span*H.wordWidth)+
    (2*allocateZeroLineCost J.Fs.length (J.span*J.wordWidth)+
      (3*placedHaloLengthKeysCost s J.t J.band J.origin (J.origin+J.span) J.metadataWidth+
        ((haloLengthKeys s J.t J.band J.origin (J.origin+J.span)).map
          (J.keyWorkspace (A := A) (U := U) hQ R K)).sum))+
    2*realReplicaRowsCost J.Fs.length (J.span*J.wordWidth)

theorem replicaRecoveryInterior_exec_within (H : ReplicaHaloProblem s) (target : ℕ) (X : ℕ → ZMod s → ℝ)
    (B : ReplicaRecoveryBatch H target X) (htarget)
    (plan : ReplicaInteriorPlacement T) (source dst : Fin T)
    (hsourceSep : ∀ k, plan.gather k ≠ source)
    (hgd : ∀ k, plan.gather k ≠ dst) (hsd : ∀ k, plan.solver k ≠ dst)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (hp : 2 ≤ H.p) (hwidth : 8*H.p ≤ 2^H.u)
    (hpad : 2*((s/(H.t-s)+1)-2*H.band) ≤ 2^H.l+1) (R K : ℕ)
    (hpushR : mnProgPush (rpProg (P := Empty) (Q := Q) (A := A) (U := U)
      Fixed.ringReg Fixed.hostReg Fixed.layout.ι_inj (by decide) hR) ≤ R)
    (hpushK : mnProgPush (cmulBlock cr (rmulOne (P := Empty) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr)) ≤ K)
    (buffers : ReplicaLoopBuffers A) (borrowed : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (headers : ReplicaLoopHeaders H plan.gather buffers S)
    (hsource : S.R source = B.inputs.reverse.flatMap
      (fun R => cstream A H.wordWidth (packedInterval H.origin H.span R))++borrowed)
    (hbank : embStk weightCacheCoreReg (embStk plan.solver S) =
      releasedCellBank [] buffers.rhsTail buffers.solverOutputTail S.inp S.out)
    (hcache : S.R (plan.solver 117) = buffers.cacheTail)
    (hsolverFresh : ∀ k ∈ [(118 : Fin 121),119,120], S.R (plan.solver k) = [])
    (hinput : S.inp = buffers.input) (houtput : S.out = buffers.output)
    (hkeys : S.R (plan.gather 87) = buffers.keyTail) (hdst : S.R dst = buffers.accumulatorTail)
    (h86 : S.R (plan.gather 86) = []) (h119 : S.R (plan.gather 119) = []) (depth : ℕ) :
    ∃ v' F n, v'.user = v.user ∧ n ≤ replicaRecoveryInteriorTime H (B.problem htarget) ∧
      RealReplicaHaloOutput (B.problem htarget) dst buffers.accumulatorTail F ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        replicaRecoveryInteriorWorkspace (A := A) (U := U) H (B.problem htarget) hQ R K) depth
        (replicaRecoveryInterior plan source dst hR hQ) (mk v S) n (mk v' F) := by
  let J := B.problem htarget
  let M := {S with R := Function.update S.R (plan.gather 124) (B.inputs.flatMap
    (fun R => cstream A H.wordWidth (packedInterval H.origin H.span R))++S.R (plan.gather 124))}
  let nextBuffers := {buffers with packedRhsTail := S.R (plan.gather 124), savedGather := embStk plan.gather M}
  obtain ⟨v₀,n₀,hu₀,hn₀,he₀,hheaders⟩ := B.source_headers_exec_within (body := body) htarget
    plan.gather plan.gather_injective source hsourceSep buffers borrowed v S headers hsource depth
  have hsolver : embStk plan.solver M = embStk plan.solver S := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    simp [M,embStk,(plan.disjoint 124 k).symm]
  have hg (k : Fin 126) (hk : k ≠ 124) : M.R (plan.gather k) = S.R (plan.gather k) := by
    simp [M,plan.gather_injective.eq_iff,hk]
  obtain ⟨v₁,F,n₁,hu₁,hn₁,hstate,he₁⟩ := initializedReplicaHaloLoop_exec_within (body := body)
    J plan dst hgd hsd hR hQ hA hpad R K hpushR hpushK nextBuffers v₀ M hheaders
    (by rw [hsolver]; exact hbank)
    (by exact (congrFun (congrArg Stacks.R hsolver) 117).trans hcache)
    (by intro k hk; exact (congrFun (congrArg Stacks.R hsolver) k).trans (hsolverFresh k hk))
    hinput houtput rfl ((hg 87 (by decide)).trans hkeys)
    (by simpa [M,(hgd 124).symm] using hdst)
    ((hg 86 (by decide)).trans h86) ((hg 119 (by decide)).trans h119) depth
  let W := 2*allocateZeroLineCost J.Fs.length (J.span*J.wordWidth)+
    (3*placedHaloLengthKeysCost s J.t J.band J.origin (J.origin+J.span) J.metadataWidth+
      ((haloLengthKeys s J.t J.band J.origin (J.origin+J.span)).map
        (J.keyWorkspace (A := A) (U := U) hQ R K)).sum)
  obtain ⟨v₂,G,n₂,hu₂,hn₂,he₂,hfields,hgather⟩ := realInitializedReplicaHaloLoop_finish (body := body)
    J plan dst hgd hR hQ (by omega) nextBuffers v₀ v₁ M F n₁ depth W hu₁ he₁ hstate (J.dominates hp hwidth)
  refine ⟨v₂,G,n₀+n₂,hu₂.trans hu₀,?_,hfields,?_⟩
  · change n₀+n₂ ≤ replicaRecoveryInteriorTime H J
    unfold replicaRecoveryInteriorTime
    omega
  · have hsize := he₀.final
    change mnSize (mk v₀ M)+depth ≤ mnSize (mk v S)+depth+
      2*reverseCopyRowsCost H.Fs.length (H.span*H.wordWidth) at hsize
    apply ExecWithin.seq (he₀.mono ?_) (he₂.mono ?_)
    all_goals
      intro d z hz
      change mnSize z+d ≤ mnSize (mk v S)+depth+
        replicaRecoveryInteriorWorkspace (A := A) (U := U) H J hQ R K
      unfold replicaRecoveryInteriorWorkspace
      try dsimp only [W] at hz
      omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
