module

public import IntegerMultBounds.MathlibTM2.Routing.SourceCoordinateBranches

/-! A fixed interpreter converts a live Y source coordinate into its canonical
raw record. Region tests, division, width conversion, writing and cleanup are
all executed and charged; only the record destination changes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def sourceCoordinateRecordProgram (rg : Fin 21 → Fin T) : Pr P T Q A U :=
  sourceRegionDispatchProgram (sourceCoordinateRegion rg) (sourceCoordinateBranchProgram rg)

def sourceCoordinateRecordCost (Li Lk : ℕ) :=
  (Li + Lk) * (12 * Lk + 35) + 20 * Lk + 48 * (Li + Lk) + 18 * Li + 158

theorem sourceCoordinateRecord_exec (body : P → Pr P T Q A U)
    (rg : Fin 21 → Fin T) (hrg : Function.Injective rg)
    (Li Lk q low high k : ℕ) (enabled : Bool)
    (hq : q < 2 ^ (Li + Lk)) (hlow : low < 2 ^ (Li + Lk)) (hhigh : high < 2 ^ (Li + Lk))
    (hk : k < 2 ^ Lk) (hk0 : 0 < k)
    (v : HS T Q A U) (S : Stacks T A) (data : SourceCoordinateData rg Li Lk q low high k enabled S) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧ steps ≤ sourceCoordinateRecordCost Li Lk ∧
      Exec body (sourceCoordinateRecordProgram rg) (mk v S) steps
        (mk v' { S with R := Function.update S.R (rg 19) ((sourceCoordinateChoice q low high k enabled).word Li Lk ++ S.R (rg 19)) }) := by
  let C := (Li + Lk) * (12 * Lk + 35) + 20 * Lk + 32 * (Li + Lk) + 18 * Li + 140
  let S' : Stacks T A := { S with R := Function.update S.R (rg 19) ((sourceCoordinateChoice q low high k enabled).word Li Lk ++ S.R (rg 19)) }
  have hbranch (u : HS T Q A U) : ∃ (u' : HS T Q A U) (steps : ℕ), u'.user = u.user ∧ steps ≤ C ∧
      Exec body (sourceCoordinateBranchProgram rg (sourceRegionIndex q low high)) (mk u S) steps (mk u' S') := by
    by_cases hlo : q < low
    · obtain ⟨u', hu, hx⟩ := sourceCoordinateOuter_exec body rg hrg Li Lk q low high k enabled false hq (by simp) u S data
      refine ⟨u', 16 * (Li + Lk) + 12 * Li + 76, hu, by dsimp [C]; omega, ?_⟩
      simpa [S', sourceCoordinateBranchProgram, sourceRegionIndex, sourceCoordinateChoice,
        GatedSelectedSourceChoice.word, hlo] using hx
    · by_cases hhi : q < high
      · obtain ⟨u', steps, hu, ht, hx⟩ := sourceCoordinateSegment_exec body rg hrg Li Lk q low high k enabled
          hq (by omega) hk hk0 u S data
        refine ⟨u', steps, hu, ht, ?_⟩
        simpa [S', sourceRegionIndex, sourceCoordinateChoice, GatedSelectedSourceChoice.word, hlo, hhi] using hx
      · obtain ⟨u', hu, hx⟩ := sourceCoordinateOuter_exec body rg hrg Li Lk q low high k enabled true hq (by simpa using Nat.le_of_not_gt hhi) u S data
        refine ⟨u', 16 * (Li + Lk) + 12 * Li + 76, hu, by dsimp [C]; omega, ?_⟩
        simpa [S', sourceCoordinateBranchProgram, sourceRegionIndex, sourceCoordinateChoice,
          GatedSelectedSourceChoice.word, hlo, hhi] using hx
  obtain ⟨v', steps, hu, ht, hx⟩ := sourceRegionDispatch_exec body (sourceCoordinateRegion rg)
    (sourceCoordinateRegion_injective rg hrg) (sourceCoordinateBranchProgram rg)
    (Li + Lk) q low high C hq hlow hhigh v S S'
    (by simpa [sourceCoordinateRegion] using data.coordinate)
    (by simpa [sourceCoordinateRegion] using data.low)
    (by simpa [sourceCoordinateRegion] using data.high)
    (by
      intro j hj
      rcases hj with rfl | rfl | rfl
      · simpa [sourceCoordinateRegion] using data.blank 13 (by decide)
      · simpa [sourceCoordinateRegion] using data.blank 14 (by decide)
      · simpa [sourceCoordinateRegion] using data.blank 15 (by decide)) hbranch
  exact ⟨v', steps, hu, by dsimp [C] at ht; unfold sourceCoordinateRecordCost; omega, hx⟩

open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

theorem sourceYCoordinateRecord_exec (body : P → Pr P T Q A U)
    (rg : Fin 21 → Fin T) (hrg : Function.Injective rg)
    (p : Par) (hK : 0 < p.K) (X Li Lk : ℕ) (q : Fin p.wy) (enabled : Bool)
    (hw : p.wy < 2 ^ (Li + Lk)) (hk : p.K < 2 ^ Lk)
    (v : HS T Q A U) (S : Stacks T A)
    (data : SourceCoordinateData rg Li Lk q.val p.ρ (p.ρ + p.n * p.K) p.K enabled S) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧ steps ≤ sourceCoordinateRecordCost Li Lk ∧
      Exec body (sourceCoordinateRecordProgram rg) (mk v S) steps
        (mk v' { S with R := Function.update S.R (rg 19) (((sourceOfY p hK q : SlotSource p X).gatedChoice enabled).word Li Lk ++ S.R (rg 19)) }) := by
  have hy : p.wy = p.ρ + p.n * p.K + p.m := rfl
  obtain ⟨v', steps, hu, ht, hx⟩ := sourceCoordinateRecord_exec body rg hrg Li Lk q.val p.ρ
    (p.ρ + p.n * p.K) p.K enabled (q.isLt.trans hw) (by omega) (by omega) hk hK v S data
  rw [sourceCoordinateChoice_sourceOfY p hK X q enabled] at hx
  exact ⟨v', steps, hu, ht, hx⟩

end IntegerMultBounds.MathlibTM2.Routing
