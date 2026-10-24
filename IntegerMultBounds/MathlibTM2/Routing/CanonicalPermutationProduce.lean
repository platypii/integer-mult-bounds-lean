module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalPermutationLayout

/-! Execute the concrete permutation/reservoir producer directly on generated
canonical geometry. All producer inputs and scratch readiness are derived. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {Q A : ℕ} {P U : Type}

def canonicalPermutationProduceProgram (second : Bool) (k : Fin 3) : Pr P 126 Q A U :=
  embProg canonicalPermutationProducerSlot Empty.elim (permutationReservoirFixedProgram (P := Empty) second k)

theorem canonicalPermutationProduce_exec (body : P → Pr P 126 Q A U)
    (L n r : ℕ) (hn : n < 2 ^ L) (hlarge : canonicalRouterStride n ≤ n)
    (second : Bool) (k : Fin 3) (f : Equiv.Perm (Fin n))
    (R : Fin 126 → List (Fin (A + 4)))
    (hdimension : R 57 = binSyms L n)
    (htable : R 85 = matchingEntryWords L (matchingTableEntries n (matchingMateCoordinate f)))
    (hblank : ∀ j : Fin 126, j.val < 98 → j ≠ 57 → j ≠ 70 → j ≠ 84 → j ≠ 85 → R j = [])
    (v : HS 126 Q A U) (S : Stacks 126 A)
    (hR : S.R = canonicalProfileSetupBank R canonicalPermutationGeometrySlot L n r) :
    let H := routingReservoirWidth n (canonicalRouterGap n)
    let hfit := routingReservoir_fit n (canonicalRouterGap n) hlarge
    let w := routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n)
    let hw := routerBorrowed_le_reservoir n (canonicalRouterGap n) (canonicalRouterGap_pos n)
    let mate := reservoirClassLocalMatching n H hfit w hw k (permutationMatchingCoordinate second f)
      (permutationMatchingCoordinate_involutive second f)
    ∃ (v' : HS 126 Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ permutationMatchingTableBinaryCost n L + reservoirClassLocalTableCost n w L +
        682 * L + 765 + 2 * (n * (2 * L + 2)) + 2 ∧
      Exec body (canonicalPermutationProduceProgram second k) (mk v S) m
        (mk v' { S with R := (Function.update S.R 34
          (matchingEntryWords L (matchingTableEntries (n - 3 * w) (matchingMateCoordinate mate)))) }) := by
  dsimp only
  let H := routingReservoirWidth n (canonicalRouterGap n)
  let w := routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n)
  have hfit := routingReservoir_fit n (canonicalRouterGap n) hlarge
  have hw := routerBorrowed_le_reservoir n (canonicalRouterGap n) (canonicalRouterGap_pos n)
  obtain ⟨hH, hwWord⟩ := canonicalPermutationProducer_scalars R L n r
  have keep (j : Fin 98) (h58 : j ≠ 58) (h59 : j ≠ 59) :
      S.R (canonicalPermutationProducerSlot j) = R (canonicalPermutationProducerSlot j) := by
    rw [hR]
    exact canonicalPermutationProducer_keep R L n r j h58 h59
  let smallBody : Empty → Pr Empty 98 Q A U := Empty.elim
  obtain ⟨u, m, hu, hm, hex⟩ := permutationReservoirFixed_exec smallBody n H hfit w hw k second L hn f
    (embDn canonicalPermutationProducerSlot v) (embStk canonicalPermutationProducerSlot S)
    ((keep 57 (by decide) (by decide)).trans hdimension)
    (by change S.R (canonicalPermutationProducerSlot 58) = _; rw [hR]; exact hH)
    (by change S.R (canonicalPermutationProducerSlot 59) = _; rw [hR]; exact hwWord)
    ((keep 85 (by decide) (by decide)).trans htable)
    (by intro j h57 h58 h59 h70 h85 h84
        change S.R (canonicalPermutationProducerSlot j) = _
        rw [hR]
        exact canonicalPermutationProducer_blank R L n r hblank j h57 h58 h59 h70 h85 h84)
  obtain ⟨v', hu', hex'⟩ := exec_emb_stream canonicalPermutationProducerSlot
    canonicalPermutationProducerSlot_injective Empty.elim smallBody body (by intro q; exact q.elim)
    (permutationReservoirFixedProgram second k) v S u m 34 _ hex
  exact ⟨v', m, hu'.trans hu, hm, hex'⟩

end IntegerMultBounds.MathlibTM2.Routing
