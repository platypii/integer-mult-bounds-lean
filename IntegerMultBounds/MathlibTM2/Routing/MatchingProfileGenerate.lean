module

public import IntegerMultBounds.MathlibTM2.Routing.MatchingCoordinateGenerate

/-! Produce exactly the profile input consumed by generated repair, deriving
physical sources and activity from an oriented matching's endpoint table. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
noncomputable section
variable {T Q A : ℕ} {P U : Type}

def matchingProfileEntries (p : Par) (hK : 0 < p.K) (mate : Fin p.wy → Fin p.wy) : List (ℕ × ℕ) :=
  List.ofFn fun c : Fin p.n => ((profileTarget p hK c).val, (mate (profileTarget p hK c)).val)

theorem matchingProfileOutput_eq (p : Par) (hK : 0 < p.K) (mate : Fin p.wy → Fin p.wy)
    (hinv : Function.Involutive mate) (reverse : Bool) (Li Lk : ℕ) :
    matchingCoordinateOutput (A := A) reverse Li Lk (matchingProfileEntries p hK mate) =
      sourceCoordinateInputWords Li Lk (profileCoordinateInputs p hK (matchingDirectionTargets mate reverse) mate) := by
  rw [profileCoordinateInputs_matching p hK mate hinv reverse]
  simp only [matchingCoordinateOutput, matchingProfileEntries, List.map_ofFn, Function.comp_def]

/-- No prepared source coordinate or activity input is required: both are
computed from each live matching entry, with the entire endpoint table restored. -/
theorem matchingProfileGenerate_exec (body : P → Pr P T Q A U)
    (rg : Fin 11 → Fin T) (hrg : Function.Injective rg)
    (out : Fin T) (hout : ∀ j, out ≠ rg j)
    (p : Par) (hK : 0 < p.K) (mate : Fin p.wy → Fin p.wy)
    (hinv : Function.Involutive mate) (reverse : Bool) (Li Lk : ℕ)
    (hwidth : p.wy < 2 ^ (Li + Lk))
    (v : HS T Q A U) (S : Stacks T A)
    (hinput : S.R (rg 7) = matchingEntryWords (Li + Lk) (matchingProfileEntries p hK mate))
    (hblank : ∀ j : Fin 11, j.val < 7 → j ≠ 5 → S.R (rg j) = [])
    (htmp : S.R (rg 9) = []) (hsaved : S.R (rg 8) = []) (haccum : S.R (rg 10) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ p.n * (28 * (Li + Lk) + 44) +
        2 * (p.n * (2 * (Li + Lk) + 2)) + 2 * (p.n * (Li + Lk + 3)) + 6 ∧
      Exec body (matchingCoordinateGenerateProgram rg reverse out) (mk v S) steps
        (mk v' { S with R := Function.update S.R out (sourceCoordinateInputWords Li Lk (profileCoordinateInputs p hK (matchingDirectionTargets mate reverse) mate) ++ S.R out) }) := by
  have hfit : ∀ x ∈ matchingProfileEntries p hK mate, x.1 < 2 ^ (Li + Lk) ∧ x.2 < 2 ^ (Li + Lk) := by
    intro x hx
    obtain ⟨c, rfl⟩ := List.mem_ofFn.mp hx
    exact ⟨(profileTarget p hK c).isLt.trans hwidth, (mate (profileTarget p hK c)).isLt.trans hwidth⟩
  obtain ⟨v', steps, hu, hm, he⟩ := matchingCoordinateGenerate_exec body rg hrg reverse out hout Li Lk
    (matchingProfileEntries p hK mate) hfit v S hinput hblank htmp hsaved haccum
  rw [matchingProfileOutput_eq p hK mate hinv reverse Li Lk] at he
  exact ⟨v', steps, hu, by simpa only [matchingProfileEntries, List.length_ofFn] using hm, he⟩

end
end IntegerMultBounds.MathlibTM2.Routing
