module

public import IntegerMultBounds.MathlibTM2.Routing.LiveInactiveProfileLayout

/-! Fill one missing inactive profile in the actual live descriptor bank.
All other live inputs, the count operand and outer scratch are preserved. -/

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

def liveInactiveProfileBank (R : Fin (liveInactiveProfileT N J) → List (Fin (A + 4)))
    (j : Fin J) := Function.update R (liveInactiveProfileCore (liveDescriptorAux (.input j)))
      ((mode j).profileFrames p X hG hK active s w.selectorBits)

theorem liveInactiveProfile_ready
    (R : Fin (liveInactiveProfileT N J) → List (Fin (A + 4))) (j : Fin J)
    (hfit : ∀ k, LiveDescriptorBounds p X w (mode k))
    (hbank : ∀ r, r ≠ .input j → R (liveInactiveProfileCore (liveDescriptorAux r)) =
      liveDescriptorData p X hG hK active s mode w r) :
    LiveDescriptorReady p X hG hK active s mode w
      (fun i => liveInactiveProfileBank p X hG hK active s mode w R j (liveInactiveProfileCore i)) := by
  refine ⟨hfit, ?_⟩
  intro r
  by_cases hr : r = .input j
  · subst r
    simp [liveInactiveProfileBank, liveDescriptorData]
  · rw [liveInactiveProfileBank, Function.update_of_ne
      (liveInactiveProfileCore_injective.ne (liveDescriptorAux_injective.ne hr))]
    exact hbank r hr

theorem liveInactiveProfileGenerate_exec (body : P → Pr P (liveInactiveProfileT N J) Q A U)
    (j : Fin J) (Lc : ℕ) (hn : p.n < 2 ^ Lc)
    (hprofile : (mode j).profileFrames (A := A) p X hG hK active s w.selectorBits =
      affineProfileFrames w.selectorBits (List.replicate p.n (false, 0)))
    (v : HS (liveInactiveProfileT N J) Q A U) (S : Stacks (liveInactiveProfileT N J) A)
    (hselector : w.selectorBits < 2 ^ w.widthBits)
    (hwidth : S.R (liveInactiveProfileCore (liveDescriptorAux .selectorBits)) = binSyms w.widthBits w.selectorBits)
    (hinput : S.R (liveInactiveProfileCore (liveDescriptorAux (.input j))) = [])
    (hcount : S.R (liveInactiveProfileAux 0) = binSyms Lc p.n)
    (hscratch : ∀ i : Fin 7, i ≠ 0 → S.R (liveInactiveProfileAux i) = []) :
    ∃ (v' : HS (liveInactiveProfileT N J) Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ binaryInactiveProfileCost w.widthBits Lc w.selectorBits p.n ∧
      Exec body (binaryInactiveProfileProgram (liveInactiveProfileReg j)) (mk v S) steps
        (mk v' { S with R := liveInactiveProfileBank p X hG hK active s mode w S.R j }) := by
  obtain ⟨v', steps, hu, ht, hx⟩ := binaryInactiveProfile_exec body (liveInactiveProfileReg j)
    (liveInactiveProfileReg_injective j) w.widthBits Lc w.selectorBits p.n hselector hn v S
    hwidth hcount (by
      intro i h0 h1 h3
      fin_cases i <;> simp_all [liveInactiveProfileReg])
  refine ⟨v', steps, hu, ht, ?_⟩
  rw [show liveInactiveProfileReg j 3 = liveInactiveProfileCore (liveDescriptorAux (.input j)) from rfl,
    hinput, List.append_nil, ← hprofile] at hx
  exact hx

theorem liveInactiveProfile_exec (body : P → Pr P (liveInactiveProfileT N J) Q A U)
    (j : Fin J) (Lc : ℕ) (hn : p.n < 2 ^ Lc)
    (hprofile : (mode j).profileFrames (A := A) p X hG hK active s w.selectorBits =
      affineProfileFrames w.selectorBits (List.replicate p.n (false, 0)))
    (v : HS (liveInactiveProfileT N J) Q A U) (S : Stacks (liveInactiveProfileT N J) A)
    (hfit : ∀ k, LiveDescriptorBounds p X w (mode k))
    (hbank : ∀ r, r ≠ .input j → S.R (liveInactiveProfileCore (liveDescriptorAux r)) =
      liveDescriptorData p X hG hK active s mode w r)
    (hinput : S.R (liveInactiveProfileCore (liveDescriptorAux (.input j))) = [])
    (hcount : S.R (liveInactiveProfileAux 0) = binSyms Lc p.n)
    (hscratch : ∀ i : Fin 7, i ≠ 0 → S.R (liveInactiveProfileAux i) = []) :
    ∃ (v' : HS (liveInactiveProfileT N J) Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ binaryInactiveProfileCost w.widthBits Lc w.selectorBits p.n ∧
      Exec body (binaryInactiveProfileProgram (liveInactiveProfileReg j)) (mk v S) steps
        (mk v' { S with R := liveInactiveProfileBank p X hG hK active s mode w S.R j }) := by
  exact liveInactiveProfileGenerate_exec p X hG hK active s mode w body j Lc hn hprofile v S
    (hfit j).selector_fits (hbank .selectorBits (by simp)) hinput hcount hscratch

end
end IntegerMultBounds.MathlibTM2.Routing
