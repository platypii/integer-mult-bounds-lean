module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNormalizeRecoveryInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedRecoveryInputExec

/-! Physical normalization, factor generation and complete cached recovery
execute consecutively on one bank, with all conversion and cleanup work paid. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.SchurDominance IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {U : Type}

noncomputable def normalizedGeneratedRecovery (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr Empty 392 Q A U :=
  .seq normalizeRecoveryInput (generatedFirstCachedReplicaRecovery hR hQ)

theorem normalizedGeneratedRecovery_exec_within (H : ReplicaHaloProblem s) (W : ℕ)
    (Fs : List (ZMod s → GaussianInt))
    (hfields : H.Fs = recoveryInputFields H.p H.precision Fs)
    (hpq : H.p+1 ≤ H.precision) (hW : H.wordWidth ≤ W) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (hspan : H.span+H.band ≤ s) (horigin : H.origin < s)
    (R K : ℕ)
    (hpushR : mnProgPush (rpProg (P := Empty) (Q := Q) (A := A) (U := U)
      Fixed.ringReg Fixed.hostReg Fixed.layout.ι_inj (by decide) hR) ≤ R)
    (hpushK : mnProgPush (cmulBlock cr (rmulOne (P := Empty) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr)) ≤ K)
    (hpad : 2*((s/(H.t-s)+1)-2*H.band) ≤ 2^H.l+1)
    (inp : List (Bool ⊕ Bool)) (out : List Bool) (v : HS 392 Q A U) (depth : ℕ)
    (hp : 2 ≤ H.p) (hwidth : 8*H.p ≤ 2^H.u)
    (target : ℕ)
    (push : BoundarySolvePushBounds (A := A) (U := U) hQ) (c : ℕ)
    (hpush : mnNativePushBound c (replicaBoundaryRhs (P := Empty) (Q := Q) (A := A) (U := U)))
    (M : ℕ) (hpushM : mnProgPush (rmulOne (P := Empty) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ M)
    (X : ℕ → ZMod s → ℝ)
    (hX : ∀ r < H.Fs.length, Solves (realMatrix s H.t H.p H.u) (haloVertices s H.origin (H.origin+H.span)) (X r)
      (fun i => (value H.precision (H.Fs.reverse.getD r (fun _ => 0) i)).re))
    (htarget : H.target = boundaryHaloTarget H.p H.u (boundaryRecoveryTarget H.p target) H.rhsExp
      (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card) :
    ∃ B : ReplicaRecoveryBatch H target X, ∃ Ds : List (ZMod s → GaussianInt), ∃ v' G n outputs,
      Ds.length = H.Fs.length ∧ v'.user = v.user ∧ n ≤ normalizeRecoveryInputCost H W Fs.length+generatedReplicaBoundaryFactoryCost H target+firstCachedReplicaRecoveryTime H (B.problem htarget) ∧
      List.Forall₂ (ReplicaRecoveryAssemblyOutput B Ds) (List.finRange H.Fs.length) outputs ∧
      G.R 257 = [] ∧ G.R 247 = [] ∧
      G.R 391 = outputs.reverse.flatten ∧
      ExecWithin (fun f : Empty => nomatch f) (fun d z => mnSize z+d ≤ mnSize (mk v (rawRecoveryInput H W Fs inp out))+depth+
        (normalizeRecoveryInputPush (Q := Q) (A := A) (U := U)*normalizeRecoveryInputCost H W Fs.length+
          generatedRecoveryInputStock H [] []+
        generatedFirstCachedReplicaRecoveryWorkspace H (B.problem htarget) target hR hQ push c M R K))
        depth (normalizedGeneratedRecovery hR hQ) (mk v (rawRecoveryInput H W Fs inp out)) n (mk v' G) ∧ (G.inp = inp ∧ G.out = out) := by
  obtain ⟨v₁,hu₁,he₁⟩ := normalizeRecoveryInput_exec_within H W Fs hfields hpq hW inp out v
  obtain ⟨B,Ds,v',G,n,outputs,hlen,hu,hn,hcert,h257,h247,h391,he₂,hstreams⟩ :=
    generatedRecoveryInput_exec_within (body := fun f : Empty => nomatch f) H hR hQ hA hspan horigin
      R K hpushR hpushK hpad inp out v₁ depth hp hwidth target push c hpush M hpushM X hX htarget
  refine ⟨B,Ds,v',G,normalizeRecoveryInputCost H W Fs.length+n,outputs,hlen,hu.trans hu₁,
    by omega,hcert,h257,h247,h391,?_,hstreams⟩
  have hio : inp.length+out.length ≤ mnSize (mk v (rawRecoveryInput H W Fs inp out)) := by
    rw [mnSize_mk_registerBankStock]
    change inp.length+out.length ≤ inp.length+out.length+_
    omega
  refine .seq ((he₁ depth).mono ?_) (he₂.mono ?_)
  all_goals
    intro d z hz
    dsimp only [generatedRecoveryInputStock,List.length_nil] at hz ⊢
    omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
