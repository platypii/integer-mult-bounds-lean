module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedRecoveryInputBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedFirstCachedReplicaRecovery

/-! Execute the complete physical caller from its explicit ordinary input bank,
with no caller-readiness premises or generated-factor assumptions. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.SchurDominance IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 392 Q A U}

theorem generatedRecoveryInput_exec_within (H : ReplicaHaloProblem s) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
      Ds.length = H.Fs.length ∧ v'.user = v.user ∧ n ≤ generatedReplicaBoundaryFactoryCost H target+firstCachedReplicaRecoveryTime H (B.problem htarget) ∧
      List.Forall₂ (ReplicaRecoveryAssemblyOutput B Ds) (List.finRange H.Fs.length) outputs ∧
      G.R 257 = [] ∧ G.R 247 = [] ∧
      G.R 391 = outputs.reverse.flatten ∧
      ExecWithin body (fun d z => mnSize z+d ≤ generatedRecoveryInputStock H inp out+depth+
        generatedFirstCachedReplicaRecoveryWorkspace H (B.problem htarget) target hR hQ push c M R K)
        depth (generatedFirstCachedReplicaRecovery hR hQ) (mk v (generatedRecoveryInput H inp out)) n (mk v' G) ∧ (G.inp = inp ∧ G.out = out) := by
  let S := generatedRecoveryInput (A := A) H inp out
  have hsetup (i : Fin 255) : S.R (replicaRecoverySetupWorkerReg i) = [] := by
    apply generatedRecoveryInput_off
    · by_contra hlow
      have hi : (replicaRecoverySetupWorkerReg i).val < 126 := by omega
      apply replicaRecoveryPreparationCallerReg_gather_disjoint
        (Fin.castLE (by decide : 255 ≤ 258) i) ⟨_,hi⟩
      rw [replicaRecoveryPreparationCallerReg_worker]
      exact Fin.ext rfl
    · intro he
      have hv := congrArg Fin.val he
      change (replicaRecoveryCallerWorkerReg i).val = 390 at hv
      have hi := (replicaRecoveryCallerWorkerReg i).isLt
      omega
  have hsolver (i : Fin 121) : S.R (replicaRecoveryBatchInterior.solver i) = [] := by
    apply generatedRecoveryInput_off
    · change 126 ≤ 126+i.val
      omega
    · intro he
      have hv := congrArg Fin.val he
      change 126+i.val = 390 at hv
      have hi := i.isLt
      omega
  have hgather (k : Fin 126) (hk : k ≠ 124) (hz : generatedRecoveryHeader H k = 0) :
      S.R (replicaRecoveryBatchInterior.gather k) = [] := by
    rw [generatedRecoveryInput_gather H inp out k hk,hz]
    rfl
  obtain ⟨B,Ds,v',G,n,outputs,hlen,hu,hn,hcert,h257,h247,h391,he,hstreams⟩ :=
    generatedFirstCachedReplicaRecovery_exec_within (body := body) H hR hQ hA hspan horigin R K hpushR hpushK
      hpad (generatedRecoveryBuffers H inp out) v S (generatedRecoveryInput_headers H inp out) rfl rfl
      (hsolver 117) (by intro k _; exact hsolver k) rfl rfl rfl
      (hgather 87 (by decide) (by simp [generatedRecoveryHeader,replicaFactoryHeaderValue]))
      (generatedRecoveryInput_off H inp out 247 (by decide) (by decide))
      (hgather 86 (by decide) (by simp [generatedRecoveryHeader,replicaFactoryHeaderValue]))
      (hgather 119 (by decide) (by simp [generatedRecoveryHeader,replicaFactoryHeaderValue]))
      depth hp hwidth target
      (by intro i
          have hh := hsetup (Fin.castLE (by decide : 242 ≤ 255) i)
          rw [replicaRecoverySetupWorkerReg_eq] at hh
          exact hh)
      (by intro i; rfl) (by intro i _; rfl)
      (by intro k _
          refine ⟨rfl,?_⟩
          have hh := hsetup (Fin.castLE (by decide : 248 ≤ 255) k)
          rw [replicaRecoverySetupWorkerReg_eq] at hh
          exact hh)
      push c hpush M hpushM X hX htarget (by intro i _; exact hsetup i)
      (generatedRecoveryInput_count H inp out)
      (generatedRecoveryInput_off H inp out 391 (by decide) (by decide))
      (generatedRecoveryInput_off H inp out 248 (by decide) (by decide))
  refine ⟨B,Ds,v',G,n,outputs,hlen,hu,hn,hcert,h257,h247,h391,?_,hstreams⟩
  have hinit := generatedRecoveryInput_stock_le H inp out v
  exact he.mono (by intro d z hz; dsimp only [S] at hz; omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
