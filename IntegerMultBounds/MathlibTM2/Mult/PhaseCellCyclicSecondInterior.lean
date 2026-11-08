module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellResumedReplicaInterior
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicRecoveryJobs

/-! Both second interior passes execute beside the saved boundary archives.
Two blank extension tapes provide the disposable gather workspace. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

namespace CyclicSecondInteriorPlacement
abbrev extend : Fin 840 → Fin 842 := Fin.castLE (by decide)
def left : CachedReplicaPassPlacement 842 := CyclicRecoveryPlacement.leftJob.reindex extend (Fin.castLE_injective _)
def right : CachedReplicaPassPlacement 842 := CyclicRecoveryPlacement.rightJob.reindex extend (Fin.castLE_injective _)

theorem fresh_ne_old (k : Fin 842) (hk : 840 ≤ k.val) (i : Fin 840) : k ≠ extend i := by
  intro he
  have hv := congrArg (fun j : Fin 842 => j.val) he
  change k.val = i.val at hv
  have := i.isLt
  omega

theorem fresh_not_owned (job : CachedReplicaPassPlacement 840) (k : Fin 842) (hk : 840 ≤ k.val) :
    ¬(job.reindex extend (Fin.castLE_injective _)).Owns k := by
  intro h
  obtain ⟨i,_,he⟩ := CachedReplicaPassPlacement.reindex_owns_source _ extend (Fin.castLE_injective _) h
  exact fresh_ne_old k hk i he.symm

theorem disjoint (k : Fin 842) (hl : left.Owns k) : ¬right.Owns k := by
  intro hr
  obtain ⟨i,hi,hei⟩ := CachedReplicaPassPlacement.reindex_owns_source _ extend (Fin.castLE_injective _) hl
  obtain ⟨j,hj,hej⟩ := CachedReplicaPassPlacement.reindex_owns_source _ extend (Fin.castLE_injective _) hr
  have hij : i = j := Fin.castLE_injective _ (hei.trans hej.symm)
  subst j
  exact CyclicRecoveryPlacement.jobs_disjoint i hi hj
end CyclicSecondInteriorPlacement

open CyclicSecondInteriorPlacement
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 842 Q A U}

noncomputable def cyclicSecondInterior (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 842 Q A U :=
  .seq (resumedReplicaInterior left 840 (fun i => fresh_ne_old 840 (by decide) (CyclicRecoveryPlacement.leftJob.plan.gather i))
    (fun i => fresh_ne_old 840 (by decide) (CyclicRecoveryPlacement.leftJob.plan.solver i)) hR hQ)
    (resumedReplicaInterior right 841 (fun i => fresh_ne_old 841 (by decide) (CyclicRecoveryPlacement.rightJob.plan.gather i))
    (fun i => fresh_ne_old 841 (by decide) (CyclicRecoveryPlacement.rightJob.plan.solver i)) hR hQ)

theorem cyclicSecondInterior_exec (H K J L : ReplicaHaloProblem s)
    (layoutL : H.SameLayout J) (layoutR : K.SameLayout L)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (hpL : 2 ≤ H.p) (hwL : 8*H.p ≤ 2^H.u) (hpR : 2 ≤ K.p) (hwR : 8*K.p ≤ 2^K.u)
    (hpadL : 2*((s/(H.t-s)+1)-2*H.band) ≤ 2^H.l+1)
    (hpadR : 2*((s/(K.t-s)+1)-2*K.band) ≤ 2^K.l+1)
    (buffersL buffersR : ReplicaLoopBuffers A) (borrowedL borrowedR : List (Fin (A+4)))
    (v : HS 842 Q A U) (S : Stacks 840 A)
    (readyL : ReplicaInteriorResumeReady H CyclicRecoveryPlacement.leftJob buffersL S)
    (readyR : ReplicaInteriorResumeReady K CyclicRecoveryPlacement.rightJob buffersR S)
    (controlsL : ReplicaAssemblyControls H CyclicRecoveryPlacement.leftJob.plan.gather (CyclicRecoveryPlacement.bank 239) S)
    (controlsR : ReplicaAssemblyControls K CyclicRecoveryPlacement.rightJob.plan.gather (CyclicRecoveryPlacement.bank 238) S)
    (hsourceL : S.R (CyclicRecoveryPlacement.leftJob.plan.solver 110) = J.Fs.reverse.flatMap
      (fun R => cstream A H.wordWidth (packedInterval H.origin H.span R))++borrowedL)
    (hsourceR : S.R (CyclicRecoveryPlacement.rightJob.plan.solver 110) = L.Fs.reverse.flatMap
      (fun R => cstream A K.wordWidth (packedInterval K.origin K.span R))++borrowedR) :
    let E := extendStacks (by decide : 840 ≤ 842) S
    ∃ vf G n, vf.user = v.user ∧
      n ≤ releaseReplicaInteriorBankCost left.plan E+replicaRecoveryInteriorTime H J+
        (releaseReplicaInteriorBankCost right.plan E+replicaRecoveryInteriorTime K L) ∧
      RealReplicaHaloOutput J left.output buffersL.accumulatorTail G ∧
      RealReplicaHaloOutput L right.output buffersR.accumulatorTail G ∧
      G.R (left.plan.gather 125) = S.R (CyclicRecoveryPlacement.leftJob.plan.gather 125) ∧
      G.R (right.plan.gather 125) = S.R (CyclicRecoveryPlacement.rightJob.plan.gather 125) ∧
      Exec body (cyclicSecondInterior hR hQ) (mk v E) n (mk vf G) ∧
      ReplicaAssemblyControls H left.plan.gather (extend (CyclicRecoveryPlacement.bank 239)) G ∧
      ReplicaAssemblyControls K right.plan.gather (extend (CyclicRecoveryPlacement.bank 238)) G ∧
      (∀ k, ¬left.Owns k → ¬right.Owns k → k ≠ 840 → k ≠ 841 → G.L k = E.L k ∧ G.R k = E.R k) := by
  dsimp only
  let E := extendStacks (by decide : 840 ≤ 842) S
  have hread (i : Fin 840) : E.R (extend i) = S.R i :=
    congrArg (fun C : Stacks 840 A => C.R i) (embStk_extendStacks (by decide : 840 ≤ 842) S)
  obtain ⟨vi,F,m,huL,hmL,hfieldsL,harchL,hstreamsL,heL,hframeL,hcontrolsL⟩ := resumedReplicaInterior_exec (body := body)
    H J layoutL left 840 (fun i => fresh_ne_old 840 (by decide) (CyclicRecoveryPlacement.leftJob.plan.gather i))
    (fun i => fresh_ne_old 840 (by decide) (CyclicRecoveryPlacement.leftJob.plan.solver i))
    (fresh_ne_old 840 (by decide) _) hR hQ hA hpL hwL hpadL buffersL borrowedL v E
    (readyL.extend (by decide)) (extendStacks_fresh (by decide : 840 ≤ 842) S 840 (by decide)).2
    ((hread _).trans hsourceL)
  have hright (k : Fin 842) (hk : right.Owns k) : F.L k = E.L k ∧ F.R k = E.R k :=
    hframeL k (fun hl => disjoint k hl hk)
      (fun he => fresh_not_owned CyclicRecoveryPlacement.rightJob 840 (by decide) (he ▸ hk))
  have readyRF : ReplicaInteriorResumeReady K right buffersR F :=
    (readyR.extend (by decide)).of_frame (F := F) hstreamsL.1 hstreamsL.2 hright
  have hblankR : F.R 841 = [] :=
    (hframeL 841 (fresh_not_owned CyclicRecoveryPlacement.leftJob 841 (by decide)) (by decide)).2.trans
      (extendStacks_fresh (by decide : 840 ≤ 842) S 841 (by decide)).2
  obtain ⟨vf,G,n,huR,hmR,hfieldsR,harchR,hstreamsR,heR,hframeR,hcontrolsR⟩ := resumedReplicaInterior_exec (body := body)
    K L layoutR right 841 (fun i => fresh_ne_old 841 (by decide) (CyclicRecoveryPlacement.rightJob.plan.gather i))
    (fun i => fresh_ne_old 841 (by decide) (CyclicRecoveryPlacement.rightJob.plan.solver i))
    (fresh_ne_old 841 (by decide) _) hR hQ hA hpR hwR hpadR buffersR borrowedR vi F readyRF hblankR
    (((hright _ (.solver 110)).2.trans (hread _)).trans hsourceR)
  have hleft (k : Fin 842) (hk : left.Owns k) : G.L k = F.L k ∧ G.R k = F.R k :=
    hframeR k (disjoint k hk)
      (fun he => fresh_not_owned CyclicRecoveryPlacement.leftJob 841 (by decide) (he ▸ hk))
  have hcost : releaseReplicaInteriorBankCost right.plan F = releaseReplicaInteriorBankCost right.plan E :=
    releaseReplicaInteriorBankCost_eq right.plan E F (fun i => (hright _ (.solver i)).2)
  have hnative (i : Fin 240) : ¬left.Owns (extend (CyclicRecoveryPlacement.bank i)) ∧
      ¬right.Owns (extend (CyclicRecoveryPlacement.bank i)) := by
    constructor
    · intro h
      obtain ⟨k,hk,heq⟩ := CachedReplicaPassPlacement.reindex_owns_source _ extend (Fin.castLE_injective _) h
      exact CyclicRecoveryPlacement.native_left_disjoint i k hk (Fin.castLE_injective _ heq)
    · intro h
      obtain ⟨k,hk,heq⟩ := CachedReplicaPassPlacement.reindex_owns_source _ extend (Fin.castLE_injective _) h
      exact CyclicRecoveryPlacement.native_right_disjoint i k hk (Fin.castLE_injective _ heq)
  have hnativeFrame (i : Fin 240) : G.R (extend (CyclicRecoveryPlacement.bank i)) = S.R (CyclicRecoveryPlacement.bank i) :=
    ((hframeR _ (hnative i).2 (fresh_ne_old 841 (by decide) _).symm).2.trans
      (hframeL _ (hnative i).1 (fresh_ne_old 840 (by decide) _).symm).2).trans (hread _)
  obtain ⟨fields,hlen,hencoded,hgood⟩ := hfieldsL
  refine ⟨vf,G,m+n,huR.trans huL,?_,⟨fields,hlen,(hleft _ .output).2.trans hencoded,hgood⟩,
    hfieldsR,((hleft _ (.gather 125)).2.trans harchL).trans (hread _),
    (harchR.trans (hright _ (.gather 125)).2).trans (hread _),Exec.seq heL heR,?_,?_,?_⟩
  · rw [hcost] at hmR
    exact Nat.add_le_add hmL hmR
  · exact controlsL.transport (hnativeFrame 239)
      (((hleft _ (.gather 94)).2.trans (hcontrolsL 94 (by simp))).trans (hread _))
      (((hleft _ (.gather 121)).2.trans (hcontrolsL 121 (by simp))).trans (hread _))
  · exact controlsR.transport (hnativeFrame 238)
      ((hcontrolsR 94 (by simp)).trans ((hright _ (.gather 94)).2.trans (hread _)))
      ((hcontrolsR 121 (by simp)).trans ((hright _ (.gather 121)).2.trans (hread _)))
  · intro k hkL hkR hk840 hk841
    have hl := hframeL k hkL hk840
    have hr := hframeR k hkR hk841
    exact ⟨hr.1.trans hl.1,hr.2.trans hl.2⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
