module

public import IntegerMultBounds.MathlibTM2.Routing.LiveDescriptorExec

/-! Execute arbitrary live descriptor job lists through one common workspace.
Every job's readiness follows from the initial bank and survives earlier core
output writes; no freshly prepared intermediate banks or execution premises occur. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

structure LiveDescriptorJob (N J : ℕ) where
  index : Fin J
  dst : Fin N

noncomputable section

variable {N J Q A : ℕ} {P U : Type}

variable (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
  (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)
  (mode : Fin J → LiveDescriptorMode) (w : LiveDescriptorWidths)

def liveDescriptorBankGenerated (R : Fin (liveDescriptorT N J) → List (Fin (A + 4))) :
    List (LiveDescriptorJob N J) → Fin (liveDescriptorT N J) → List (Fin (A + 4))
  | [] => R
  | job :: jobs => liveDescriptorBankGenerated (Function.update R (liveDescriptorCore (J := J) job.dst)
      (repairDescriptorWord p X hG hK active s (mode job.index).key ++ R (liveDescriptorCore (J := J) job.dst))) jobs

def liveDescriptorBatch : List (LiveDescriptorJob N J) → Pr P (liveDescriptorT N J) Q A U
  | [] => .act .done
  | job :: jobs => .seq (liveDescriptorProgram (mode job.index) job.index job.dst) (liveDescriptorBatch jobs)

def liveDescriptorBatchCost : List (LiveDescriptorJob N J) → ℕ
  | [] => 1
  | job :: jobs => liveDescriptorCost p X hG hK active s w (mode job.index) + liveDescriptorBatchCost jobs

theorem liveDescriptorBatch_exec (body : P → Pr P (liveDescriptorT N J) Q A U)
    (hGK : p.G < p.K) (jobs : List (LiveDescriptorJob N J))
    (v : HS (liveDescriptorT N J) Q A U) (S : Stacks (liveDescriptorT N J) A)
    (h : LiveDescriptorReady p X hG hK active s mode w S.R) :
    ∃ (v' : HS (liveDescriptorT N J) Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ liveDescriptorBatchCost p X hG hK active s mode w jobs ∧
      Exec body (liveDescriptorBatch mode jobs) (mk v S) steps
        (mk v' { S with R := liveDescriptorBankGenerated p X hG hK active s mode S.R jobs }) := by
  induction jobs generalizing v S with
  | nil => exact ⟨v, 1, rfl, le_rfl, Exec.act (body := body) .done (mk v S)⟩
  | cons job jobs ih =>
    obtain ⟨v₁, n₁, hu₁, ht₁, he₁⟩ := liveDescriptor_exec body p X hG hK hGK active s mode w job.index job.dst v S h
    let S₁ : Stacks (liveDescriptorT N J) A := { S with R := Function.update S.R (liveDescriptorCore (J := J) job.dst) (repairDescriptorWord p X hG hK active s (mode job.index).key ++ S.R (liveDescriptorCore (J := J) job.dst)) }
    have hr : LiveDescriptorReady p X hG hK active s mode w S₁.R := h.update_core job.dst _
    obtain ⟨v₂, n₂, hu₂, ht₂, he₂⟩ := ih v₁ S₁ hr
    exact ⟨v₂, n₁ + n₂, hu₂.trans hu₁, Nat.add_le_add ht₁ ht₂, Exec.seq he₁ he₂⟩

theorem liveDescriptorBankGenerated_keep (R : Fin (liveDescriptorT N J) → List (Fin (A + 4)))
    (jobs : List (LiveDescriptorJob N J)) (k : Fin (liveDescriptorT N J))
    (hk : ∀ job ∈ jobs, k ≠ liveDescriptorCore (J := J) job.dst) :
    liveDescriptorBankGenerated p X hG hK active s mode R jobs k = R k := by
  induction jobs generalizing R with
  | nil => rfl
  | cons job jobs ih =>
    rw [liveDescriptorBankGenerated, ih _ (fun other ho => hk other (by simp [ho]))]
    exact Function.update_of_ne (hk job (by simp)) _ _

theorem liveDescriptorBankGenerated_aux (R : Fin (liveDescriptorT N J) → List (Fin (A + 4)))
    (jobs : List (LiveDescriptorJob N J)) (r : LiveDescriptorRole J) :
    liveDescriptorBankGenerated p X hG hK active s mode R jobs (liveDescriptorAux r) = R (liveDescriptorAux r) := by
  apply liveDescriptorBankGenerated_keep
  intro job _
  exact (liveDescriptorCore_aux job.dst r).symm

theorem liveDescriptorBankGenerated_at (R : Fin (liveDescriptorT N J) → List (Fin (A + 4)))
    (jobs : List (LiveDescriptorJob N J)) (hn : (jobs.map LiveDescriptorJob.dst).Nodup)
    (job : LiveDescriptorJob N J) (hj : job ∈ jobs) :
    liveDescriptorBankGenerated p X hG hK active s mode R jobs (liveDescriptorCore (J := J) job.dst) =
      repairDescriptorWord p X hG hK active s (mode job.index).key ++ R (liveDescriptorCore (J := J) job.dst) := by
  induction jobs generalizing R with
  | nil => simp at hj
  | cons head jobs ih =>
    have hnd := List.nodup_cons.mp hn
    rcases List.mem_cons.mp hj with rfl | hj
    · rw [liveDescriptorBankGenerated, liveDescriptorBankGenerated_keep]
      · simp
      · intro other ho he
        apply hnd.1
        exact List.mem_map.mpr ⟨other, ho, (liveDescriptorCore_injective he).symm⟩
    · rw [liveDescriptorBankGenerated, ih _ hnd.2 hj]
      have hne : liveDescriptorCore (J := J) job.dst ≠ liveDescriptorCore (J := J) head.dst := by
        intro he
        exact hnd.1 (List.mem_map.mpr ⟨job, hj, liveDescriptorCore_injective he⟩)
      rw [Function.update_of_ne hne]

end
end IntegerMultBounds.MathlibTM2.Routing
