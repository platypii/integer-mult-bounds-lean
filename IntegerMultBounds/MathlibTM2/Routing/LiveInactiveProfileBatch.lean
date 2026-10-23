module

public import IntegerMultBounds.MathlibTM2.Routing.LiveInactiveProfile

/-! Generate any distinct list of inactive live inputs with one count operand
and workspace. Readiness of later jobs follows from the initial bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

variable {N J Q A : ℕ} {P U : Type}
variable (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
  (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)
  (mode : Fin J → LiveDescriptorMode) (w : LiveDescriptorWidths)

def liveInactiveProfileBatchBank (R : Fin (liveInactiveProfileT N J) → List (Fin (A + 4))) :
    List (Fin J) → Fin (liveInactiveProfileT N J) → List (Fin (A + 4))
  | [] => R
  | j :: jobs => liveInactiveProfileBatchBank (liveInactiveProfileBank p X hG hK active s mode w R j) jobs

def liveInactiveProfileBatch : List (Fin J) → Pr P (liveInactiveProfileT N J) Q A U
  | [] => .act .done
  | j :: jobs => .seq (binaryInactiveProfileProgram (liveInactiveProfileReg j)) (liveInactiveProfileBatch jobs)

theorem liveInactiveProfileBatch_keep
    (R : Fin (liveInactiveProfileT N J) → List (Fin (A + 4))) (jobs : List (Fin J))
    (i : Fin (liveInactiveProfileT N J))
    (hi : ∀ j ∈ jobs, i ≠ liveInactiveProfileCore (liveDescriptorAux (.input j))) :
    liveInactiveProfileBatchBank p X hG hK active s mode w R jobs i = R i := by
  induction jobs generalizing R with
  | nil => rfl
  | cons j jobs ih =>
    rw [liveInactiveProfileBatchBank, ih _ (fun k hk => hi k (by simp [hk]))]
    exact Function.update_of_ne (hi j (by simp)) _ _

theorem liveInactiveProfileBatch_at
    (R : Fin (liveInactiveProfileT N J) → List (Fin (A + 4))) (jobs : List (Fin J))
    (hnd : jobs.Nodup) (j : Fin J) (hj : j ∈ jobs) :
    liveInactiveProfileBatchBank p X hG hK active s mode w R jobs
      (liveInactiveProfileCore (liveDescriptorAux (.input j))) =
      (mode j).profileFrames p X hG hK active s w.selectorBits := by
  induction jobs generalizing R with
  | nil => simp at hj
  | cons k jobs ih =>
    rcases List.mem_cons.mp hj with rfl | hj
    · rw [liveInactiveProfileBatchBank, liveInactiveProfileBatch_keep]
      · simp [liveInactiveProfileBank]
      · intro i hi
        exact liveInactiveProfileCore_injective.ne (liveDescriptorAux_injective.ne
          (by intro h; cases h; exact (List.nodup_cons.mp hnd).1 hi))
    · exact ih _ hnd.of_cons hj

theorem liveInactiveProfileBatch_ready
    (R : Fin (liveInactiveProfileT N J) → List (Fin (A + 4))) (jobs : List (Fin J)) (hnd : jobs.Nodup)
    (hfit : ∀ j, LiveDescriptorBounds p X w (mode j))
    (hbank : ∀ r, (∀ j ∈ jobs, r ≠ .input j) → R (liveInactiveProfileCore (liveDescriptorAux r)) =
      liveDescriptorData p X hG hK active s mode w r) :
    LiveDescriptorReady p X hG hK active s mode w
      (fun i => liveInactiveProfileBatchBank p X hG hK active s mode w R jobs (liveInactiveProfileCore i)) := by
  refine ⟨hfit, ?_⟩
  intro r
  by_cases hr : ∃ j ∈ jobs, r = .input j
  · obtain ⟨j, hj, rfl⟩ := hr
    exact liveInactiveProfileBatch_at p X hG hK active s mode w R jobs hnd j hj
  · have hn : ∀ j ∈ jobs, r ≠ .input j := by simpa only [not_exists, not_and] using hr
    rw [liveInactiveProfileBatch_keep p X hG hK active s mode w R jobs _
      (fun j hj => liveInactiveProfileCore_injective.ne (liveDescriptorAux_injective.ne (hn j hj)))]
    exact hbank r hn

theorem liveInactiveProfileBatch_exec (body : P → Pr P (liveInactiveProfileT N J) Q A U)
    (jobs : List (Fin J)) (hnd : jobs.Nodup) (Lc : ℕ) (hn : p.n < 2 ^ Lc)
    (hprofiles : ∀ j ∈ jobs, (mode j).profileFrames (A := A) p X hG hK active s w.selectorBits =
      affineProfileFrames w.selectorBits (List.replicate p.n (false, 0)))
    (hselector : w.selectorBits < 2 ^ w.widthBits)
    (v : HS (liveInactiveProfileT N J) Q A U) (S : Stacks (liveInactiveProfileT N J) A)
    (hwidth : S.R (liveInactiveProfileCore (liveDescriptorAux .selectorBits)) = binSyms w.widthBits w.selectorBits)
    (hinput : ∀ j ∈ jobs, S.R (liveInactiveProfileCore (liveDescriptorAux (.input j))) = [])
    (hcount : S.R (liveInactiveProfileAux 0) = binSyms Lc p.n)
    (hscratch : ∀ i : Fin 7, i ≠ 0 → S.R (liveInactiveProfileAux i) = []) :
    ∃ (v' : HS (liveInactiveProfileT N J) Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ jobs.length * binaryInactiveProfileCost w.widthBits Lc w.selectorBits p.n + 1 ∧
      Exec body (liveInactiveProfileBatch jobs) (mk v S) steps
        (mk v' { S with R := liveInactiveProfileBatchBank p X hG hK active s mode w S.R jobs }) := by
  induction jobs generalizing v S with
  | nil => exact ⟨v, 1, rfl, by simp, Exec.act (body := body) .done (mk v S)⟩
  | cons j jobs ih =>
    obtain ⟨v₁, m₁, hu₁, hm₁, hx₁⟩ := liveInactiveProfileGenerate_exec p X hG hK active s mode w body
      j Lc hn (hprofiles j (by simp)) v S hselector hwidth (hinput j (by simp)) hcount hscratch
    let S₁ : Stacks (liveInactiveProfileT N J) A := { S with R := liveInactiveProfileBank p X hG hK active s mode w S.R j }
    have hkeep (i : Fin (liveInactiveProfileT N J)) (hi : i ≠ liveInactiveProfileCore (liveDescriptorAux (.input j))) : S₁.R i = S.R i :=
      Function.update_of_ne hi _ _
    obtain ⟨v₂, m₂, hu₂, hm₂, hx₂⟩ := ih hnd.of_cons (fun k hk => hprofiles k (by simp [hk])) v₁ S₁
      ((hkeep _ (liveInactiveProfileCore_injective.ne (liveDescriptorAux_injective.ne (by simp)))).trans hwidth)
      (by
        intro k hk
        rw [hkeep _ (liveInactiveProfileCore_injective.ne (liveDescriptorAux_injective.ne
          (by intro h; cases h; exact (List.nodup_cons.mp hnd).1 hk)))]
        exact hinput k (by simp [hk]))
      ((hkeep _ (liveInactiveProfileAux_core _ _)).trans hcount)
      (fun i hi => (hkeep _ (liveInactiveProfileAux_core _ _)).trans (hscratch i hi))
    exact ⟨v₂, m₁ + m₂, hu₂.trans hu₁, by simp only [List.length_cons, Nat.add_mul]; omega,
      Exec.seq hx₁ hx₂⟩

end
end IntegerMultBounds.MathlibTM2.Routing
