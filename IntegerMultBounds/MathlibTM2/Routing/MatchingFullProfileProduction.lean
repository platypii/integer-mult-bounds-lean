module

public import IntegerMultBounds.MathlibTM2.Routing.MatchingProfileProduction
public import IntegerMultBounds.MathlibTM2.Routing.MatchingTablePrefix

/-! Gather one matching residue from a common table, derive physical coordinates
and activity, then erase the gathered temporary. Only the profile input remains. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
noncomputable section
variable {T Q A : ℕ} {P U : Type}

def matchingFullProfileProductionProgram (extract : Fin 8 → Fin T) (gather : Fin 18 → Fin T)
    (generate : Fin 11 → Fin T) (reverse : Bool) (dst : Fin T) : Pr P T Q A U :=
  .seq (binaryPrefixExtractProgram extract)
    (.seq (matchingProfileProductionProgram gather generate reverse dst) (bclear (gather 14)))

def matchingFullProfileProductionCost (p : Par) (L Lk Lc : ℕ) : ℕ :=
  binaryPrefixExtractCost Lc ((p.n * p.K) * (2 * L + 2)) + matchingProfileProductionCost p L Lk +
    (2 * ((p.n * p.K) * (2 * L + 2)) + 2)

theorem matchingFullProfileProduction_exec (body : P → Pr P T Q A U)
    (extract : Fin 8 → Fin T) (hprefix : Function.Injective extract)
    (gather : Fin 18 → Fin T) (hgather : Function.Injective gather)
    (generate : Fin 11 → Fin T) (hgenerate : Function.Injective generate)
    (hseparate : ∀ j, generate 7 ≠ gather j) (dst : Fin T) (hdst : ∀ j, dst ≠ generate j)
    (hjoin : extract 6 = gather 14) (hgenerateSource : ∀ j, generate j ≠ gather 14)
    (hdstBulk : dst ≠ gather 14)
    (p : Par) (hK : 0 < p.K) (hρ : p.ρ < p.K) (mate : Fin p.wy → Fin p.wy)
    (hinv : Function.Involutive mate) (reverse : Bool) (Li Lk Lc : ℕ)
    (hwidth : p.wy < 2 ^ (Li + Lk)) (hk : p.K < 2 ^ Lk)
    (hcountFit : (p.n * p.K) * (2 * (Li + Lk) + 2) < 2 ^ Lc)
    (v : HS T Q A U) (S : Stacks T A)
    (hinput : S.R (extract 5) = matchingEntryWords (Li + Lk) (matchingTableEntries p.wy (matchingMateCoordinate mate)))
    (hcount : S.R (extract 0) = binSyms Lc ((p.n * p.K) * (2 * (Li + Lk) + 2)))
    (hblankPrefix : ∀ j : Fin 8, j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 7 → S.R (extract j) = [])
    (hbulkBlank : S.R (gather 14) = [])
    (hblankGather : ∀ j : Fin 18, j = 0 ∨ j = 12 ∨ j = 13 ∨ (2 ≤ j.val ∧ j.val < 10) → S.R (gather j) = [])
    (hstride : S.R (gather 1) = binSyms Lk p.K) (hresidue : S.R (gather 11) = binSyms Lk p.ρ)
    (htmpGather : S.R (gather 16) = []) (hsavedGather : S.R (gather 15) = []) (haccumGather : S.R (gather 17) = [])
    (hblankGenerate : ∀ j : Fin 11, j.val < 7 → j ≠ 5 → S.R (generate j) = [])
    (htmpGenerate : S.R (generate 9) = []) (hsavedGenerate : S.R (generate 8) = [])
    (haccumGenerate : S.R (generate 10) = []) (hsourceBlank : S.R (generate 7) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ matchingFullProfileProductionCost p (Li + Lk) Lk Lc ∧
      Exec body (matchingFullProfileProductionProgram extract gather generate reverse dst) (mk v S) steps
        (mk v' { S with R := Function.update S.R dst (sourceCoordinateInputWords Li Lk
          (profileCoordinateInputs p hK (matchingDirectionTargets mate reverse) mate) ++ S.R dst) }) := by
  have hB : p.n * p.K ≤ p.wy := by unfold Par.wy; omega
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := matchingTablePrefix_exec body extract hprefix p.wy (p.n * p.K)
    (Li + Lk) Lc hB (matchingMateCoordinate mate) hcountFit v S hcount hinput hblankPrefix
  rw [hjoin, hbulkBlank, List.append_nil] at he₁
  let bulk := matchingEntryWords (A := A) (Li + Lk) (matchingTableEntries (p.n * p.K) (matchingMateCoordinate mate))
  let G : Stacks T A := { S with R := Function.update S.R (gather 14) bulk }
  have hgkeep (j : Fin 18) (hj : j ≠ 14) : G.R (gather j) = S.R (gather j) := Function.update_of_ne (hgather.ne hj) _ _
  have hnkeep (j : Fin 11) : G.R (generate j) = S.R (generate j) := Function.update_of_ne (hgenerateSource j) _ _
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := matchingProfileProduction_exec body gather hgather generate hgenerate
    hseparate dst hdst p hK hρ mate hinv reverse Li Lk hwidth hk v₁ G (by simp [G, bulk])
    (by intro j hj; rw [hgkeep j (by intro he; subst j; simp at hj)]; exact hblankGather j hj)
    ((hgkeep 1 (by decide)).trans hstride) ((hgkeep 11 (by decide)).trans hresidue)
    ((hgkeep 16 (by decide)).trans htmpGather) ((hgkeep 15 (by decide)).trans hsavedGather)
    ((hgkeep 17 (by decide)).trans haccumGather)
    (by intro j hj h5; exact (hnkeep j).trans (hblankGenerate j hj h5))
    ((hnkeep 9).trans htmpGenerate) ((hnkeep 8).trans hsavedGenerate)
    ((hnkeep 10).trans haccumGenerate) ((hnkeep 7).trans hsourceBlank)
  let output := sourceCoordinateInputWords (A := A) Li Lk (profileCoordinateInputs p hK (matchingDirectionTargets mate reverse) mate) ++ S.R dst
  have hdstG : G.R dst = S.R dst := Function.update_of_ne hdstBulk _ _
  rw [hdstG] at he₂
  let H : Stacks T A := { G with R := Function.update G.R dst output }
  obtain ⟨v₃, hu₃, _, he₃⟩ := bclear_exec body (gather 14) v₂ H
  have hlength : (H.R (gather 14)).length = (p.n * p.K) * (2 * (Li + Lk) + 2) := by
    simp [H, G, hdstBulk.symm, bulk, matchingEntryWords_length, matchingTableEntries]
  have hf : Function.update H.R (gather 14) [] = Function.update S.R dst output := by
    funext j
    by_cases hb : j = gather 14
    · subst j; simp [hbulkBlank, hdstBulk.symm]
    by_cases hd : j = dst
    · subst j; simp [H, G, hb]
    · simp [H, G, hb, hd]
  rw [hlength, hf] at he₃
  exact ⟨v₃, m₁ + (m₂ + (2 * ((p.n * p.K) * (2 * (Li + Lk) + 2)) + 2)),
    hu₃.trans (hu₂.trans hu₁), by unfold matchingFullProfileProductionCost; omega,
    Exec.seq he₁ (Exec.seq he₂ he₃)⟩

end
end IntegerMultBounds.MathlibTM2.Routing
