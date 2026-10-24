module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalPermutationScope
public import IntegerMultBounds.MathlibTM2.Routing.CanonicalPreparedProfile

/-! Produce the local matching table from the original permutation, compile its
canonical profile, and erase both intermediate table encodings on one bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
noncomputable section
variable {Q A : ℕ} {P U : Type}

def canonicalPermutationCompileProgram (second : Bool) (k : Fin 3) (reverse : Bool)
    (dst : Fin 126) : Pr P 162 Q A U :=
  canonicalPermutationScope second k
    (matchingResizedProfileProgram (canonicalProfileResizeInput canonicalPermutationGeometrySlot 34)
      (canonicalPermutationGeometrySlot ∘ canonicalProfileControlInput)
      (canonicalPermutationGeometrySlot ∘ canonicalProfileCountInput) reverse dst)

theorem canonicalPermutationCompile_exec (body : P → Pr P 162 Q A U)
    (L n : ℕ) (hn : n < 2 ^ L) (hlarge : canonicalRouterStride n ≤ n)
    (r : Fin (canonicalRouterStride n)) (p : Par)
    (hp : p = routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val)
    (second : Bool) (k : Fin 3) (reverse : Bool) (f : Equiv.Perm (Fin n))
    (R : Fin 126 → List (Fin (A + 4))) (hdimension : R 57 = binSyms L n)
    (hresidue : R 116 = binSyms L r.val)
    (htable : R 85 = matchingEntryWords L (matchingTableEntries n (matchingMateCoordinate f)))
    (hblank : ∀ j : Fin 126, j.val < 98 → j ≠ 57 → j ≠ 70 → j ≠ 84 → j ≠ 85 → R j = [])
    (dst : Fin 126) (hdst : dst ≠ 34) (v : HS 162 Q A U) (S : Stacks 162 A)
    (hR : S.R = matchingProductionBank (canonicalProfileSetupBank R canonicalPermutationGeometrySlot L n r.val) [] [] [] []) :
    let H := routingReservoirWidth n (canonicalRouterGap n)
    let hfit := routingReservoir_fit n (canonicalRouterGap n) hlarge
    let w := routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n)
    let hw := routerBorrowed_le_reservoir n (canonicalRouterGap n) (canonicalRouterGap_pos n)
    let hsize : p.wy = n - 3 * w := by subst p; exact routerProfileParameters_width n _ _ hlarge r
    let mate := permutationReservoirSource n H hfit w hw k second f p hsize
    let widths := canonicalStageWidths p
    ∃ (v' : HS 162 Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ permutationMatchingTableBinaryCost n L + reservoirClassLocalTableCost n w L +
        682 * L + 765 + 2 * (n * (2 * L + 2)) + 2 + canonicalPreparedProfileCost L p +
        2 * ((n - 3 * w) * (2 * L + 2)) + 2 ∧
      Exec body (canonicalPermutationCompileProgram second k reverse dst) (mk v S) m
        (mk v' { S with R := (Function.update S.R (matchingCoreEmbed 126 dst)
          (sourceCoordinateInputWords widths.indexBits widths.strideBits
            (profileCoordinateInputs p (by subst p; exact (canonicalProfileFits L n hn hlarge r).1)
              (matchingDirectionTargets mate reverse) mate) ++ S.R (matchingCoreEmbed 126 dst))) }) := by
  dsimp only
  let H := routingReservoirWidth n (canonicalRouterGap n)
  let w := routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n)
  let hfit := routingReservoir_fit n (canonicalRouterGap n) hlarge
  let hw := routerBorrowed_le_reservoir n (canonicalRouterGap n) (canonicalRouterGap_pos n)
  have hsize : p.wy = n - 3 * w := by subst p; exact routerProfileParameters_width n _ _ hlarge r
  let mate := permutationReservoirSource n H hfit w hw k second f p hsize
  let word := permutationReservoirLocalWord (A := A) n H hfit w hw k second f L
  have hoff : (34 : Fin 126) ∉ canonicalProfileTargets canonicalPermutationGeometrySlot := by decide +kernel
  apply canonicalPermutationScope_exec body L n r.val hn hlarge second k f R hdimension htable hblank v S hR
    (matchingCoreEmbed 126 dst) ((matchingCoreEmbed_injective 126).ne hdst) _ _ (canonicalPreparedProfileCost L p) _
  intro u
  let C : Stacks 162 A := { S with R := Function.update S.R (matchingCoreEmbed 126 34) word }
  let R' := Function.update R 34 word
  have hC : C.R = matchingProductionBank (canonicalProfileSetupBank R' canonicalPermutationGeometrySlot L n r.val) [] [] [] [] := by
    dsimp only [C, R']
    rw [hR, ← matchingProductionBank_updateCore,
      canonicalProfileSetupBank_update R canonicalPermutationGeometrySlot L n r.val 34 word hoff]
  have hr' : R' (canonicalPermutationGeometrySlot 18) = binSyms L r.val := by
    simpa [R', canonicalPermutationGeometrySlot] using hresidue
  have ht' : R' 34 = matchingEntryWords L (matchingTableEntries p.wy (matchingMateCoordinate mate)) := by
    simp only [R', Function.update_self]
    exact permutationReservoirLocalWord_eq n H hfit w hw k second f p hsize L
  obtain ⟨u', m, hu, hm, hex⟩ := canonicalPreparedProfile_exec body L n hn hlarge r p hp mate
    (permutationReservoirSource_involutive n H hfit w hw k second f p hsize) reverse
    canonicalPermutationGeometrySlot canonicalPermutationGeometrySlot_injective R' hr' 34 hoff ht' dst u C hC
  have keep : C.R (matchingCoreEmbed 126 dst) = S.R (matchingCoreEmbed 126 dst) :=
    Function.update_of_ne ((matchingCoreEmbed_injective 126).ne hdst) _ _
  rw [keep] at hex
  exact ⟨u', m, hu, hm, hex⟩

end
end IntegerMultBounds.MathlibTM2.Routing
