module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalPermutationProduce
public import IntegerMultBounds.MathlibTM2.Routing.MatchingProductionBank
public import IntegerMultBounds.MathlibTM2.Routing.PermutationReservoirProfile

/-! Borrow the generated local matching table on the full compiler bank. The
producer and table erasure execute; only the framed call output changes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {Q A : ℕ} {P U : Type}

def canonicalPermutationScope (second : Bool) (k : Fin 3) (call : Pr P 162 Q A U) : Pr P 162 Q A U :=
  .seq (embProg (matchingCoreEmbed 126) Empty.elim (canonicalPermutationProduceProgram (P := Empty) second k))
    (.seq call (bclear (matchingCoreEmbed 126 34)))

theorem canonicalPermutationScope_exec (body : P → Pr P 162 Q A U)
    (L n r : ℕ) (hn : n < 2 ^ L) (hlarge : canonicalRouterStride n ≤ n)
    (second : Bool) (k : Fin 3) (f : Equiv.Perm (Fin n))
    (R : Fin 126 → List (Fin (A + 4))) (hdimension : R 57 = binSyms L n)
    (htable : R 85 = matchingEntryWords L (matchingTableEntries n (matchingMateCoordinate f)))
    (hblank : ∀ j : Fin 126, j.val < 98 → j ≠ 57 → j ≠ 70 → j ≠ 84 → j ≠ 85 → R j = [])
    (v : HS 162 Q A U) (S : Stacks 162 A)
    (hR : S.R = matchingProductionBank (canonicalProfileSetupBank R canonicalPermutationGeometrySlot L n r) [] [] [] [])
    (dst : Fin 162) (hdst : dst ≠ matchingCoreEmbed 126 34) (output : List (Fin (A + 4)))
    (call : Pr P 162 Q A U) (price : ℕ)
    (hcall : ∀ u : HS 162 Q A U,
      let H := routingReservoirWidth n (canonicalRouterGap n)
      let hfit := routingReservoir_fit n (canonicalRouterGap n) hlarge
      let w := routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n)
      let hw := routerBorrowed_le_reservoir n (canonicalRouterGap n) (canonicalRouterGap_pos n)
      let word := permutationReservoirLocalWord n H hfit w hw k second f L
      let C : Stacks 162 A := { S with R := Function.update S.R (matchingCoreEmbed 126 34) word }
      ∃ (u' : HS 162 Q A U) (m : ℕ), u'.user = u.user ∧ m ≤ price ∧
        Exec body call (mk u C) m (mk u' { C with R := Function.update C.R dst output })) :
    ∃ (v' : HS 162 Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ permutationMatchingTableBinaryCost n L +
        reservoirClassLocalTableCost n (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n)) L +
        682 * L + 765 + 2 * (n * (2 * L + 2)) + 2 + price +
        2 * ((n - 3 * routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n)) * (2 * L + 2)) + 2 ∧
      Exec body (canonicalPermutationScope second k call) (mk v S) m
        (mk v' { S with R := Function.update S.R dst output }) := by
  let H := routingReservoirWidth n (canonicalRouterGap n)
  let w := routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n)
  let hfit := routingReservoir_fit n (canonicalRouterGap n) hlarge
  let hw := routerBorrowed_le_reservoir n (canonicalRouterGap n) (canonicalRouterGap_pos n)
  let word := permutationReservoirLocalWord (A := A) n H hfit w hw k second f L
  let smallBody : Empty → Pr Empty 126 Q A U := Empty.elim
  have hcore : (embStk (matchingCoreEmbed 126) S).R = canonicalProfileSetupBank R canonicalPermutationGeometrySlot L n r := by
    funext j
    change S.R (matchingCoreEmbed 126 j) = _
    rw [hR, matchingProductionBank_core]
  obtain ⟨u, m₁, hu, hm₁, hex⟩ := canonicalPermutationProduce_exec smallBody L n r hn hlarge second k f
    R hdimension htable hblank (embDn (matchingCoreEmbed 126) v) (embStk (matchingCoreEmbed 126) S) hcore
  obtain ⟨v₁, hu₁, hex₁⟩ := exec_emb_stream (matchingCoreEmbed 126) (matchingCoreEmbed_injective 126)
    Empty.elim smallBody body (by intro q; exact q.elim) (canonicalPermutationProduceProgram second k)
    v S u m₁ 34 word hex
  let C : Stacks 162 A := { S with R := Function.update S.R (matchingCoreEmbed 126 34) word }
  obtain ⟨v₂, m₂, hu₂, hm₂, hex₂⟩ := hcall v₁
  let D : Stacks 162 A := { C with R := Function.update C.R dst output }
  obtain ⟨v₃, hu₃, _, hex₃⟩ := bclear_exec body (matchingCoreEmbed 126 34) v₂ D
  have hlen : (D.R (matchingCoreEmbed 126 34)).length = (n - 3 * w) * (2 * L + 2) := by
    simp [D, C, hdst.symm, word, permutationReservoirLocalWord, matchingEntryWords_length, matchingTableEntries]
  have htableBlank : S.R (matchingCoreEmbed 126 34) = [] := by
    rw [hR, matchingProductionBank_core]
    exact canonicalPermutationProducer_blank R L n r hblank 34
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hf : ({ D with R := Function.update D.R (matchingCoreEmbed 126 34) [] } : Stacks 162 A) =
      { S with R := Function.update S.R dst output } := by
    congr 1
    funext j
    by_cases ht : j = matchingCoreEmbed 126 34
    · subst j; simp [hdst.symm, htableBlank]
    · by_cases hd : j = dst <;> simp [D, C, ht, hd, hdst]
  rw [hlen, hf] at hex₃
  exact ⟨v₃, m₁ + (m₂ + (2 * ((n - 3 * w) * (2 * L + 2)) + 2)),
    hu₃.trans (hu₂.trans (hu₁.trans hu)), by dsimp only [w]; omega, Exec.seq hex₁ (Exec.seq hex₂ hex₃)⟩

end IntegerMultBounds.MathlibTM2.Routing
