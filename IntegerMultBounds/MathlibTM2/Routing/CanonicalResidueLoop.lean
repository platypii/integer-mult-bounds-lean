module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalResidueBank
public import IntegerMultBounds.MathlibTM2.Routing.CanonicalResidueWords

/-! Execute all canonical residues with a fixed count-tape loop. Each round is
actual permutation/profile compilation; count/index/output banks are explicit. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
noncomputable section
variable {Q A : ℕ} {P U : Type}

def canonicalResidueLoopProgram (second : Bool) (k : Fin 3) (reverse : Bool) : Pr P 163 Q A U :=
  indexedCountLoopProgram 107 (canonicalResidueStepProgram second k reverse)

theorem canonicalResidueLoop_exec (body : P → Pr P 163 Q A U)
    (L n : ℕ) (hn : n < 2 ^ L) (hlarge : canonicalRouterStride n ≤ n)
    (second : Bool) (k : Fin 3) (reverse : Bool) (f : Equiv.Perm (Fin n))
    (core : Fin 126 → List (Fin (A + 4))) (hdimension : core 57 = binSyms L n)
    (htable : core 85 = matchingEntryWords L (matchingTableEntries n (matchingMateCoordinate f)))
    (hblank : ∀ j : Fin 126, j.val < 98 → j ≠ 57 → j ≠ 70 → j ≠ 84 → j ≠ 85 → core j = [])
    (hgeometry : ∀ j : Fin 28, j ≠ 0 → j ≠ 9 → j ≠ 18 → core (canonicalPermutationGeometrySlot j) = [])
    (hdivisor : canonicalRouterStride n + 3 * canonicalRouterGap n < 2 ^ L)
    (cs : List (Fin (A + 4))) (hlen : cs.length = canonicalRouterStride n)
    (price : ℕ) (hprice : ∀ i < canonicalRouterStride n, canonicalResidueRoundCost L n i ≤ price)
    (v : HS 163 Q A U) (S : Stacks 163 A)
    (hR : (embStk canonicalResidueCoreSlot S).R = matchingProductionBank core [] [] [] []) :
    let profile := canonicalResidueWords n hlarge second k reverse f
    let bank := fun i => ({ S with R := indexedCountBank S.R 107 162 116 98 L cs profile i } : Stacks 163 A)
    ∃ (v' : HS 163 Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ canonicalRouterStride n * (price + 2) + 2 ∧
      Exec body (canonicalResidueLoopProgram second k reverse) (mk v (bank 0)) m
        (mk v' (bank (canonicalRouterStride n))) := by
  dsimp only
  let profile := canonicalResidueWords (A := A) n hlarge second k reverse f
  let bank := fun i => ({ S with R := indexedCountBank S.R 107 162 116 98 L cs profile i } : Stacks 163 A)
  apply indexedCountLoop_exec body 107 (canonicalResidueStepProgram second k reverse) bank
    (canonicalRouterStride n) price
  · intro i
    simpa only [bank, hlen] using indexedCountBank_count_flag S.R 107 162 116 98 (by decide) L cs profile i
  · intro i hi u
    have hne : cs.drop i ≠ [] := by
      intro h
      have hh := congrArg List.length h
      simp only [List.length_drop, List.length_nil, hlen] at hh
      omega
    obtain ⟨c, rest, hc⟩ := List.exists_cons_of_ne_nil hne
    let R := canonicalResidueCoreBank core L i (cs.drop i) (indexedCountOutput profile i ++ S.R 98)
    have hbank : (embStk canonicalResidueCoreSlot (bank i)).R = matchingProductionBank R [] [] [] [] :=
      canonicalResidueBank_projection S.R core hR L i cs profile
    have hr : R 116 = binSyms L i := by simp [R, canonicalResidueCoreBank]
    have hc' : (bank i).R 107 = c :: rest := by
      simp [bank, indexedCountBank, hc]
    obtain ⟨u', m, hu, hm, hex⟩ := canonicalResidueStep_exec body L n hn hlarge ⟨i,hi⟩ _ rfl
      second k reverse f R
      (by simpa [R, canonicalResidueCoreBank] using hdimension) hr
      (by simpa [R, canonicalResidueCoreBank] using htable)
      (canonicalResidueCoreBank_blank core hblank L i _ _)
      (canonicalResidueCoreBank_geometry core hgeometry L i _ _)
      hdivisor c rest u (bank i) hc' hbank
    change Exec body (canonicalResidueStepProgram second k reverse) (mk u (bank i)) m
      (mk u' { bank i with R := (indexedCountStepBank (bank i).R 107 162 116 98 L i c rest
        (canonicalResidueWord n hlarge second k reverse f ⟨i,hi⟩ ++ (bank i).R 98)) }) at hex
    have hw : profile i = canonicalResidueWord n hlarge second k reverse f ⟨i,hi⟩ := by
      simp only [profile, canonicalResidueWords, dite_eq_left hi]
    rw [← hw] at hex
    have hf := indexedCountBank_step S.R 107 162 116 98 (by decide) L cs profile i c rest hc
    change indexedCountStepBank (bank i).R 107 162 116 98 L i c rest
      (profile i ++ (bank i).R 98) = (bank (i + 1)).R at hf
    rw [hf] at hex
    exact ⟨u', m, hu, hm.trans (hprice i hi), hex⟩

end
end IntegerMultBounds.MathlibTM2.Routing
