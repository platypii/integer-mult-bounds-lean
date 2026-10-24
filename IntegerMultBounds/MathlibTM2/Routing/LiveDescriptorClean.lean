module

public import IntegerMultBounds.MathlibTM2.Routing.LiveDescriptorBatch

/-! Erase live-generated descriptor tables after an arbitrary disjoint stream
change. All original blank destinations and the complete auxiliary bank return. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget IntegerMultBounds.MathlibTM2.Layer.CompactDigits

noncomputable section

variable {N J Q A : ℕ} {P U : Type}

variable (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
  (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)
  (mode : Fin J → LiveDescriptorMode)

def LiveDescriptorJob.target (job : LiveDescriptorJob N J) : Fin (liveDescriptorT N J) := liveDescriptorCore job.dst


def liveDescriptorEraseCost : List (LiveDescriptorJob N J) → ℕ
  | [] => 1
  | job :: jobs => liveDescriptorEraseCost jobs +
      (2 * (repairCompactRows p (mode job.index).key * (repairCompactSourceWidth p X (mode job.index).key + 1)) + 2)

/-- Erasing a finite descriptor family has a uniform quadratic address-size bound. -/
theorem liveDescriptorEraseCost_le (n : ℕ) (hfields : fieldsLen (selectiveLen p X) = n)
    (jobs : List (LiveDescriptorJob N J)) :
    liveDescriptorEraseCost p X mode jobs ≤ jobs.length * (2 * (n * (n + 1)) + 2) + 1 := by
  induction jobs with
  | nil => simp [liveDescriptorEraseCost]
  | cons job jobs ih =>
    have hr := repairCompactRows_le_fields p X (mode job.index).key
    have hs := repairCompactSourceWidth_le_fields p X (mode job.index).key
    rw [hfields] at hr hs
    have hm := Nat.mul_le_mul hr (Nat.add_le_add_right hs 1)
    simp only [liveDescriptorEraseCost, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem liveDescriptorEraseCost_eq (R : Fin (liveDescriptorT N J) → List (Fin (A + 4)))
    (jobs : List (LiveDescriptorJob N J))
    (hlen : ∀ job ∈ jobs, (R job.target).length =
      repairCompactRows p (mode job.index).key * (repairCompactSourceWidth p X (mode job.index).key + 1)) :
    metadataCleanCost R (jobs.map LiveDescriptorJob.target) = liveDescriptorEraseCost p X mode jobs := by
  induction jobs with
  | nil => rfl
  | cons job jobs ih =>
    simp only [List.map_cons, metadataCleanCost, liveDescriptorEraseCost]
    rw [ih (fun j hj => hlen j (by simp [hj])), hlen job (by simp)]

theorem liveDescriptorClean_restore (R : Fin (liveDescriptorT N J) → List (Fin (A + 4)))
    (jobs : List (LiveDescriptorJob N J)) (hblank : ∀ job ∈ jobs, R job.target = [])
    (str : Fin (liveDescriptorT N J)) (out : List (Fin (A + 4)))
    (hstr : ∀ job ∈ jobs, job.target ≠ str) :
    metadataCleared (Function.update (liveDescriptorBankGenerated p X hG hK active s mode R jobs) str out)
      (jobs.map LiveDescriptorJob.target) = Function.update R str out := by
  funext r
  by_cases hr : r ∈ jobs.map LiveDescriptorJob.target
  · rw [metadataCleared_at _ _ r hr]
    obtain ⟨job, hj, rfl⟩ := List.mem_map.mp hr
    rw [Function.update_of_ne (hstr job hj), hblank job hj]
  · rw [metadataCleared_keep _ _ r hr]
    by_cases hs : r = str
    · subst r; simp
    · rw [Function.update_of_ne hs, Function.update_of_ne hs]
      apply liveDescriptorBankGenerated_keep
      intro job hj he
      exact hr (List.mem_map.mpr ⟨job, hj, he.symm⟩)

theorem liveDescriptorClean_exec (body : P → Pr P (liveDescriptorT N J) Q A U)
    (jobs : List (LiveDescriptorJob N J)) (hn : (jobs.map LiveDescriptorJob.dst).Nodup)
    (str : Fin (liveDescriptorT N J)) (hstr : ∀ job ∈ jobs, job.target ≠ str)
    (v : HS (liveDescriptorT N J) Q A U) (S : Stacks (liveDescriptorT N J) A)
    (out : List (Fin (A + 4))) (hblank : ∀ job ∈ jobs, S.R job.target = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (metadataClean (jobs.map LiveDescriptorJob.target))
        (mk v { S with R := Function.update (liveDescriptorBankGenerated p X hG hK active s mode S.R jobs) str out })
        (liveDescriptorEraseCost p X mode jobs) (mk v' { S with R := Function.update S.R str out }) := by
  have hnt : (jobs.map LiveDescriptorJob.target).Nodup := by
    have heq : jobs.map LiveDescriptorJob.target =
        (jobs.map LiveDescriptorJob.dst).map (liveDescriptorCore (J := J)) := by
      rw [List.map_map]
      rfl
    rw [heq]
    exact hn.map liveDescriptorCore_injective
  let S₁ : Stacks (liveDescriptorT N J) A := { S with R := Function.update (liveDescriptorBankGenerated p X hG hK active s mode S.R jobs) str out }
  obtain ⟨v', hu, he⟩ := metadataClean_exec body _ hnt v S₁
  have hc : metadataCleanCost S₁.R (jobs.map LiveDescriptorJob.target) = liveDescriptorEraseCost p X mode jobs := by
    apply liveDescriptorEraseCost_eq
    intro job hj
    change (Function.update (liveDescriptorBankGenerated p X hG hK active s mode S.R jobs) str out job.target).length = _
    rw [Function.update_of_ne (hstr job hj)]
    change (liveDescriptorBankGenerated p X hG hK active s mode S.R jobs (liveDescriptorCore job.dst)).length = _
    have hb : S.R (liveDescriptorCore (J := J) job.dst) = [] := hblank job hj
    rw [liveDescriptorBankGenerated_at p X hG hK active s mode S.R jobs hn job hj, hb, List.append_nil]
    exact repairLiveDescriptorWord_length p X hG hK active s _
  have hf := liveDescriptorClean_restore p X hG hK active s mode S.R jobs hblank str out hstr
  rw [hc, hf] at he
  exact ⟨v', hu, he⟩

end
end IntegerMultBounds.MathlibTM2.Routing
