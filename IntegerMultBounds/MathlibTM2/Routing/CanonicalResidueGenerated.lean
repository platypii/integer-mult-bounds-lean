module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalResidueProgram
public import IntegerMultBounds.MathlibTM2.Routing.CanonicalResidueCount

/-! Generate the count from dimension, execute all actual residue profiles, and
restore count/index/archive and generation scratch. Only profile output changes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
noncomputable section
variable {Q A : ℕ} {P U : Type}

def canonicalResidueCountSlot : Fin 10 → Fin 163 := ![57,126,127,128,129,130,131,132,70,133]
theorem canonicalResidueCountSlot_injective : Function.Injective canonicalResidueCountSlot := by decide +kernel

def canonicalResidueGeneratedProgram (second : Bool) (k : Fin 3) (reverse : Bool) : Pr P 163 Q A U :=
  canonicalResidueCountScope canonicalResidueCountSlot 107 (canonicalResidueProgram second k reverse)

theorem canonicalResidueGenerated_exec (body : P → Pr P 163 Q A U)
    (L n : ℕ) (hn : n < 2 ^ L) (hlarge : canonicalRouterStride n ≤ n)
    (second : Bool) (k : Fin 3) (reverse : Bool) (f : Equiv.Perm (Fin n))
    (core : Fin 126 → List (Fin (A + 4))) (hdimension : core 57 = binSyms L n)
    (htable : core 85 = matchingEntryWords L (matchingTableEntries n (matchingMateCoordinate f)))
    (hblank : ∀ j : Fin 126, j.val < 98 → j ≠ 57 → j ≠ 70 → j ≠ 84 → j ≠ 85 → core j = [])
    (hgeometry : ∀ j : Fin 28, j ≠ 0 → j ≠ 9 → j ≠ 18 → core (canonicalPermutationGeometrySlot j) = [])
    (hdivisor : canonicalRouterStride n + 3 * canonicalRouterGap n < 2 ^ L)
    (price : ℕ) (hprice : ∀ i < canonicalRouterStride n, canonicalResidueRoundCost L n i ≤ price)
    (v : HS 163 Q A U) (S : Stacks 163 A)
    (hR : (embStk canonicalResidueCoreSlot S).R = matchingProductionBank core [] [] [] [])
    (hcount : S.R 107 = []) (hsaved : S.R 162 = []) (hindex : S.R 116 = []) :
    let profile := canonicalResidueWords n hlarge second k reverse f
    ∃ (v' : HS 163 Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ canonicalRouterStride n * (price + 12) + 4 * L * L + 129 * L + 192 ∧
      Exec body (canonicalResidueGeneratedProgram second k reverse) (mk v S) m
        (mk v' { S with R := (Function.update S.R 98
          (indexedCountOutput profile (canonicalRouterStride n) ++ S.R 98)) }) := by
  dsimp only
  let ticks := List.replicate (canonicalRouterStride n) (IntegerMultBounds.MathlibTM2.Node.tick : Fin (A + 4))
  let output := indexedCountOutput (canonicalResidueWords n hlarge second k reverse f) (canonicalRouterStride n) ++ S.R 98
  let loopPrice := canonicalRouterStride n * (price + 4) + 6 * L + 10
  have hd : S.R 57 = binSyms L n := by
    change (embStk canonicalResidueCoreSlot S).R (matchingCoreEmbed 126 57) = _
    rw [hR, matchingProductionBank_core]
    exact hdimension
  have work (j : Fin 36) : S.R ⟨126 + j.val, by have := j.isLt; omega⟩ = [] := by
    change (embStk canonicalResidueCoreSlot S).R ⟨126 + j.val, by have := j.isLt; omega⟩ = _
    rw [hR, matchingProductionBank_work core [] [] [] [] j.val j.isLt]
    simp [matchingWorkspaceWords]
  have generatorBlank : ∀ j : Fin 10, j ≠ 0 → j ≠ 8 → S.R (canonicalResidueCountSlot j) = [] := by
    intro j h0 h8
    fin_cases j
    · exact (h0 rfl).elim
    · exact work 0
    · exact work 1
    · exact work 2
    · exact work 3
    · exact work 4
    · exact work 5
    · exact work 6
    · exact (h8 rfl).elim
    · exact work 7
  have hcall (u : HS 163 Q A U) :
      let C : Stacks 163 A := { S with R := Function.update S.R 107 ticks }
      ∃ (u' : HS 163 Q A U) (m : ℕ), u'.user = u.user ∧ m ≤ loopPrice ∧
        Exec body (canonicalResidueProgram second k reverse) (mk u C) m
          (mk u' { C with R := Function.update C.R 98 output }) := by
    dsimp only
    let C : Stacks 163 A := { S with R := Function.update S.R 107 ticks }
    let R := Function.update core 107 ticks
    have hC : (embStk canonicalResidueCoreSlot C).R = matchingProductionBank R [] [] [] [] := by
      funext j
      change Function.update S.R 107 ticks (canonicalResidueCoreSlot j) = _
      rw [matchingProductionBank_updateCore]
      by_cases hj : j = matchingCoreEmbed 126 107
      · subst j
        change Function.update S.R 107 ticks (107 : Fin 163) = ticks
        simp
      · have hne : canonicalResidueCoreSlot j ≠ 107 := fun h => hj (canonicalResidueCoreSlot_injective h)
        rw [Function.update_of_ne hne, Function.update_of_ne hj]
        exact congrFun hR j
    have hb : ∀ j : Fin 126, j.val < 98 → j ≠ 57 → j ≠ 70 → j ≠ 84 → j ≠ 85 → R j = [] := by
      intro j hj h57 h70 h84 h85
      have h107 : j ≠ 107 := by intro h; subst j; simp at hj
      simpa [R, h107] using hblank j hj h57 h70 h84 h85
    have hg : ∀ j : Fin 28, j ≠ 0 → j ≠ 9 → j ≠ 18 → R (canonicalPermutationGeometrySlot j) = [] := by
      intro j h0 h9 h18
      have hj0 : j.val ≠ 0 := fun h => h0 (Fin.ext h)
      have hj9 : j.val ≠ 9 := fun h => h9 (Fin.ext h)
      have h107 : canonicalPermutationGeometrySlot j ≠ 107 := by
        simp [canonicalPermutationGeometrySlot, hj0, hj9, Fin.ext_iff]
        omega
      simpa [R, h107] using hgeometry j h0 h9 h18
    obtain ⟨u', m, hu, hm, hex⟩ := canonicalResidueProgram_exec body L n hn hlarge second k reverse f R
      (by simpa [R] using hdimension) (by simpa [R] using htable) hb hg hdivisor ticks (by simp [ticks])
      price hprice u C hC (by simp [C]) (by simpa [C] using hsaved) (by simpa [C] using hindex)
    have keep : C.R 98 = S.R 98 := by simp [C]
    rw [keep] at hex
    exact ⟨u', m, hu, hm, hex⟩
  obtain ⟨v', m, hu, hm, hex⟩ := canonicalResidueCountScope_exec body canonicalResidueCountSlot
    canonicalResidueCountSlot_injective 107 (by decide +kernel) L n hn hlarge v S hd generatorBlank hcount
    98 (by decide) output (canonicalResidueProgram second k reverse) loopPrice hcall
  exact ⟨v', m, hu, by dsimp only [loopPrice] at hm; nlinarith only [hm], hex⟩

end
end IntegerMultBounds.MathlibTM2.Routing
