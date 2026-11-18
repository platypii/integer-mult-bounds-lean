module

public import IntegerMultBounds.MathlibTM2.Host.Embed
public import IntegerMultBounds.MathlibTM2.Host.Foreign

/-! Keep row metadata outside the simulated swap. Only the payload tape is shared. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
variable {N Q A : ℕ} {P U : Type}

/-- Route the simulator's unused row slots to private tapes beyond its workspace.
Its payload and its prepared headers stay in place. -/
def swapSimulationPort (i : Fin N) : Fin (N+35) :=
  if h : i.val < 35 ∧ i.val ≠ 24 then Fin.natAdd N ⟨i.val,h.1⟩ else Fin.castAdd 35 i

theorem swapSimulationPort_injective : Function.Injective (swapSimulationPort (N := N)) := by
  intro i j eq
  have e := congrArg Fin.val eq
  unfold swapSimulationPort at e
  split at e <;> split at e <;> simp only [Fin.val_natAdd,Fin.val_castAdd] at e <;> apply Fin.ext <;> omega

theorem swapSimulationPort_outside (k : Fin N) (row : k.val < 35) (other : k.val ≠ 24) :
    ∀ i, swapSimulationPort i ≠ Fin.castAdd 35 k := by
  intro i eq
  have e := congrArg Fin.val eq
  unfold swapSimulationPort at e
  split at e <;> simp only [Fin.val_natAdd,Fin.val_castAdd] at e <;> omega

/-- Placing the swap this way preserves both stacks of every other row tape exactly. -/
theorem swapPlaced_exec {prog : Pr Empty N Q A U} (body : P → Pr P (N+35) Q A U)
    (v : HS (N+35) Q A U) (S : Stacks (N+35) A) {z F n}
    (run : Exec Empty.elim prog (mk (embDn swapSimulationPort v) (embStk swapSimulationPort S)) n (mk z F)) :
    ∃ y G, Exec body (embProg swapSimulationPort Empty.elim prog) (mk v S) n (mk y G) ∧
      y.user = z.user ∧ embStk swapSimulationPort G = F ∧
      ∀ k : Fin N, k.val < 35 → k.val ≠ 24 →
        G.L (Fin.castAdd 35 k) = S.L (Fin.castAdd 35 k) ∧ G.R (Fin.castAdd 35 k) = S.R (Fin.castAdd 35 k) := by
  obtain ⟨y,G,placed,_,user,project,frame⟩ := exec_emb (body' := body) (ι := Empty.elim)
    swapSimulationPort_injective (fun e => nomatch e) run v rfl S rfl
  exact ⟨y,G,placed,user,project,fun k hk ne => frame _ (swapSimulationPort_outside k hk ne)⟩

/-- The redirected bank reads the original prepared tapes everywhere except at
the unused role slots, which represent the contents of their private stacks. -/
theorem swapSimulation_rep (w : Tapes N A) (S : Stacks (N+35) A)
    (rep : RepT w (S.L ∘ Fin.castAdd 35) (S.R ∘ Fin.castAdd 35)) :
    let shadow : Tapes N A := ⟨w.head, fun i pos =>
      if h : i.val < 35 ∧ i.val ≠ 24 then
        readAt blank (S.L (Fin.natAdd N ⟨i.val,h.1⟩)) (S.R (Fin.natAdd N ⟨i.val,h.1⟩)) (pos-w.head i)
      else w.tape i pos⟩
    RepT shadow (S.L ∘ swapSimulationPort) (S.R ∘ swapSimulationPort) := by
  intro shadow i pos
  by_cases h : i.val < 35 ∧ i.val ≠ 24
  · simp [shadow,swapSimulationPort,h]
  · simpa [shadow,swapSimulationPort,h] using rep i pos

end IntegerMultBounds.MathlibTM2.Cover.Fallback
