module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalResidueLoop
public import IntegerMultBounds.MathlibTM2.Routing.IndexedCountClean

/-! Initialize the residue, execute every profile round, restore the supplied
count tape and erase the final residue. Only compiled output remains changed. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
noncomputable section
variable {Q A : ℕ} {P U : Type}

def canonicalResidueProgram (second : Bool) (k : Fin 3) (reverse : Bool) : Pr P 163 Q A U :=
  .seq (bzero 57 116 126) (.seq (canonicalResidueLoopProgram second k reverse)
    (.seq (moveR 162 107 id) (bclear 116)))

theorem canonicalResidueProgram_exec (body : P → Pr P 163 Q A U)
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
    (hR : (embStk canonicalResidueCoreSlot S).R = matchingProductionBank core [] [] [] [])
    (hcount : S.R 107 = cs) (hsaved : S.R 162 = []) (hindex : S.R 116 = []) :
    let profile := canonicalResidueWords n hlarge second k reverse f
    ∃ (v' : HS 163 Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ canonicalRouterStride n * (price + 4) + 6 * L + 10 ∧
      Exec body (canonicalResidueProgram second k reverse) (mk v S) m
        (mk v' { S with R := (Function.update S.R 98
          (indexedCountOutput profile (canonicalRouterStride n) ++ S.R 98)) }) := by
  dsimp only
  let profile := canonicalResidueWords (A := A) n hlarge second k reverse f
  have hdim : S.R 57 = binSyms L n := by
    change (embStk canonicalResidueCoreSlot S).R (matchingCoreEmbed 126 57) = _
    rw [hR, matchingProductionBank_core]
    exact hdimension
  have htmp : S.R 126 = [] := by
    change (embStk canonicalResidueCoreSlot S).R (matchingExtractSlot 126 0) = _
    rw [hR]
    simp [matchingProductionBank_extract, matchingWorkspaceWords]
  obtain ⟨v₁, hu₁, hex₁⟩ := bzero_exec (body := body) (wR := (57 : Fin 163)) (c := 116) (t := 126)
    (by decide) v S htmp
  rw [hdim, length_binSyms, hindex, List.append_nil] at hex₁
  have hinit := indexedCountBank_zero S.R 107 162 116 98 (by decide) L cs profile hcount
  obtain ⟨v₂, m₂, hu₂, hm₂, hex₂⟩ := canonicalResidueLoop_exec body L n hn hlarge second k reverse f
    core hdimension htable hblank hgeometry hdivisor cs hlen price hprice v₁ S hR
  change Exec body _ (mk v₁ { S with R := indexedCountBank S.R 107 162 116 98 L cs profile 0 }) m₂
    (mk v₂ { S with R := indexedCountBank S.R 107 162 116 98 L cs profile (canonicalRouterStride n) }) at hex₂
  rw [hinit] at hex₂
  let G : Stacks 163 A := { S with R := indexedCountBank S.R 107 162 116 98 L cs profile (canonicalRouterStride n) }
  obtain ⟨v₃, hu₃, hex₃⟩ := moveR_exec body (162 : Fin 163) 107 (by decide) id v₂ G
  let H : Stacks 163 A := { G with R := movedR G.R 162 107 id (G.R 162) }
  obtain ⟨v₄, hu₄, _, hex₄⟩ := bclear_exec body (116 : Fin 163) v₃ H
  have hs : (G.R 162).length = canonicalRouterStride n := by
    simp [G, indexedCountBank, hsaved, ← hlen]
  have hi : (H.R 116).length = L := by
    simp [H, G, movedR, indexedCountBank, length_binSyms]
  have hf := indexedCountBank_clean S.R 107 162 116 98 (by decide) L cs profile hcount hsaved hindex
  rw [hlen] at hf
  change Function.update H.R 116 [] = Function.update S.R 98
    (indexedCountOutput profile (canonicalRouterStride n) ++ S.R 98) at hf
  rw [hs] at hex₃
  rw [hi, hf] at hex₄
  refine ⟨v₄, (4 * L + 4) + (m₂ + ((2 * canonicalRouterStride n + 2) + (2 * L + 2))),
    hu₄.trans (hu₃.trans (hu₂.trans hu₁)), ?_, Exec.seq hex₁ (Exec.seq hex₂ (Exec.seq hex₃ hex₄))⟩
  nlinarith only [hm₂]

end
end IntegerMultBounds.MathlibTM2.Routing
