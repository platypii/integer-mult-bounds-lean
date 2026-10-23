module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryInactiveProfile
public import IntegerMultBounds.MathlibTM2.Routing.LiveDescriptorMode

/-! Generate the three inactive second-pass Z, Y and X input profiles from
binary count/width operands, with no source-profile word supplied. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

variable {T Q A : ℕ} {P U : Type}

theorem repairInactiveProfile_frames (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)
    (off : Off) (hoff : off = .Z ∨ off = .Y ∨ off = .X) (Ls : ℕ) :
    (LiveDescriptorMode.ofKey (some (off, 1))).profileFrames (A := A) p X hG hK active s Ls =
      affineProfileFrames Ls (List.replicate p.n (false, 0)) := by
  rcases hoff with rfl | rfl | rfl <;>
    simp [LiveDescriptorMode.ofKey, LiveDescriptorMode.profileFrames, repairAffineSources,
      repairRotationSources, affineSourceProfile, List.ofFn_const, Option.elim]

theorem repairInactiveProfileGenerate_exec (body : P → Pr P T Q A U)
    (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)
    (off : Off) (hoff : off = .Z ∨ off = .Y ∨ off = .X)
    (rg : Fin 9 → Fin T) (hrg : Function.Injective rg)
    (Lw Lc Ls : ℕ) (hLs : Ls < 2 ^ Lw) (hn : p.n < 2 ^ Lc)
    (v : HS T Q A U) (S : Stacks T A)
    (hwidth : S.R (rg 0) = binSyms Lw Ls) (hcount : S.R (rg 1) = binSyms Lc p.n)
    (hblank : ∀ i : Fin 9, i ≠ 0 → i ≠ 1 → i ≠ 3 → S.R (rg i) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ binaryInactiveProfileCost Lw Lc Ls p.n ∧
      Exec body (binaryInactiveProfileProgram rg) (mk v S) steps
        (mk v' { S with R := Function.update S.R (rg 3) ((LiveDescriptorMode.ofKey (some (off, 1))).profileFrames p X hG hK active s Ls ++ S.R (rg 3)) }) := by
  rw [repairInactiveProfile_frames p X hG hK active s off hoff]
  exact binaryInactiveProfile_exec body rg hrg Lw Lc Ls p.n hLs hn v S hwidth hcount hblank

end
end IntegerMultBounds.MathlibTM2.Routing
