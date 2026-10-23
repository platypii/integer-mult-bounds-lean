module

public import IntegerMultBounds.MathlibTM2.Routing.MatchingProfileGather

/-! Gather one matching residue from a common table, derive physical coordinates
and activity, then erase the gathered temporary. Only the profile input remains. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
noncomputable section
variable {T Q A : ℕ} {P U : Type}

def matchingProfileProductionProgram (gather : Fin 18 → Fin T) (generate : Fin 11 → Fin T)
    (reverse : Bool) (dst : Fin T) : Pr P T Q A U :=
  .seq (residueEntryGenerateProgram gather (generate 7))
    (.seq (matchingCoordinateGenerateProgram generate reverse dst) (bclear (generate 7)))

def matchingProfileProductionCost (p : Par) (L Lk : ℕ) : ℕ :=
  ((p.n * p.K) * (residueDispatchCost L Lk + 28 * L + 47) +
    4 * ((p.n * p.K) * (2 * L + 2)) + 6) +
  (p.n * (28 * L + 44) + 2 * (p.n * (2 * L + 2)) + 2 * (p.n * (L + 3)) + 6) +
  (2 * (p.n * (2 * L + 2)) + 2)

theorem matchingProfileProduction_exec (body : P → Pr P T Q A U)
    (gather : Fin 18 → Fin T) (hgather : Function.Injective gather)
    (generate : Fin 11 → Fin T) (hgenerate : Function.Injective generate)
    (hseparate : ∀ j, generate 7 ≠ gather j) (dst : Fin T) (hdst : ∀ j, dst ≠ generate j)
    (p : Par) (hK : 0 < p.K) (hρ : p.ρ < p.K) (mate : Fin p.wy → Fin p.wy)
    (hinv : Function.Involutive mate) (reverse : Bool) (Li Lk : ℕ)
    (hwidth : p.wy < 2 ^ (Li + Lk)) (hk : p.K < 2 ^ Lk)
    (v : HS T Q A U) (S : Stacks T A)
    (hinput : S.R (gather 14) = matchingEntryWords (Li + Lk) (matchingTableEntries (p.n * p.K) (matchingMateCoordinate mate)))
    (hblankGather : ∀ j : Fin 18, j = 0 ∨ j = 12 ∨ j = 13 ∨ (2 ≤ j.val ∧ j.val < 10) → S.R (gather j) = [])
    (hstride : S.R (gather 1) = binSyms Lk p.K) (hresidue : S.R (gather 11) = binSyms Lk p.ρ)
    (htmpGather : S.R (gather 16) = []) (hsavedGather : S.R (gather 15) = []) (haccumGather : S.R (gather 17) = [])
    (hblankGenerate : ∀ j : Fin 11, j.val < 7 → j ≠ 5 → S.R (generate j) = [])
    (htmpGenerate : S.R (generate 9) = []) (hsavedGenerate : S.R (generate 8) = [])
    (haccumGenerate : S.R (generate 10) = []) (hsourceBlank : S.R (generate 7) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ matchingProfileProductionCost p (Li + Lk) Lk ∧
      Exec body (matchingProfileProductionProgram gather generate reverse dst) (mk v S) steps
        (mk v' { S with R := Function.update S.R dst (sourceCoordinateInputWords Li Lk
          (profileCoordinateInputs p hK (matchingDirectionTargets mate reverse) mate) ++ S.R dst) }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := matchingProfileGather_exec body gather hgather (generate 7) hseparate
    p hK hρ mate (Li + Lk) Lk hwidth hk v S hinput hblankGather hstride hresidue htmpGather hsavedGather haccumGather
  rw [hsourceBlank, List.append_nil] at he₁
  let entries := matchingEntryWords (A := A) (Li + Lk) (matchingProfileEntries p hK mate)
  let G : Stacks T A := { S with R := Function.update S.R (generate 7) entries }
  have hkeep (j : Fin 11) (hj : j ≠ 7) : G.R (generate j) = S.R (generate j) :=
    Function.update_of_ne (hgenerate.ne hj) _ _
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := matchingProfileGenerate_exec body generate hgenerate dst hdst p hK mate hinv
    reverse Li Lk hwidth v₁ G (by simp [G, entries])
    (by intro j hj h5; exact (hkeep j (by intro he; subst j; simp at hj)).trans (hblankGenerate j hj h5))
    ((hkeep 9 (by decide)).trans htmpGenerate) ((hkeep 8 (by decide)).trans hsavedGenerate)
    ((hkeep 10 (by decide)).trans haccumGenerate)
  let output := sourceCoordinateInputWords (A := A) Li Lk (profileCoordinateInputs p hK (matchingDirectionTargets mate reverse) mate) ++ S.R dst
  have hdstG : G.R dst = S.R dst := Function.update_of_ne (hdst 7) _ _
  rw [hdstG] at he₂
  let H : Stacks T A := { G with R := Function.update G.R dst output }
  obtain ⟨v₃, hu₃, _, he₃⟩ := bclear_exec body (generate 7) v₂ H
  have hlength : (H.R (generate 7)).length = p.n * (2 * (Li + Lk) + 2) := by
    simp [H, G, (hdst 7).symm, entries, matchingEntryWords_length, matchingProfileEntries]
  have hf : Function.update H.R (generate 7) [] = Function.update S.R dst output := by
    funext j
    by_cases h7 : j = generate 7
    · subst j; simp [hsourceBlank, (hdst 7).symm]
    by_cases hd : j = dst
    · subst j; simp [H, G, h7]
    · simp [H, G, h7, hd]
  rw [hlength, hf] at he₃
  exact ⟨v₃, m₁ + (m₂ + (2 * (p.n * (2 * (Li + Lk) + 2)) + 2)),
    hu₃.trans (hu₂.trans hu₁), by unfold matchingProfileProductionCost; omega,
    Exec.seq he₁ (Exec.seq he₂ he₃)⟩

end
end IntegerMultBounds.MathlibTM2.Routing
