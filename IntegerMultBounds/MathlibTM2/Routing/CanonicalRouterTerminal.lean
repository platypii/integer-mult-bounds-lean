module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalRouterBits
public import IntegerMultBounds.MathlibTM2.Routing.ElementaryCompileLoopData
public import IntegerMultBounds.MathlibTM2.Routing.ElementaryInstructionSemantics

/-! Physical terminal coordinates for the canonical router, consumed by the
existing elementary table compiler and routing program. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Node
noncomputable section
variable (n : ℕ) (hn : canonicalRouterStride n ≤ n) (mate : Fin n → Fin n)
    (hinv : Function.Involutive mate) (k : Fin 3) (reverse : Bool)

def canonicalRouterTerminalTargets : Finset (Fin n) :=
  (routerTerminalTargets n (canonicalRouterStride n) (canonicalRouterGap n)
    (matchingDirectionTargets (canonicalRouterLocalMatching n hn k mate hinv) reverse)).image
      (canonicalRouterMiddleEmbedding n hn k)

theorem canonicalRouterTerminal_source :
    ∀ i ∈ canonicalRouterTerminalTargets n hn mate hinv k reverse,
      matchingClass (routingReservoir n (routingReservoirWidth n (canonicalRouterGap n))
        (routingReservoir_fit n (canonicalRouterGap n) hn)) mate k i ∉
        canonicalRouterTerminalTargets n hn mate hinv k reverse := by
  apply canonicalRouterMiddleTargets_source n hn mate hinv k reverse
  intro q hq
  exact (Finset.mem_filter.mp hq).1

def canonicalRouterTerminalCoordinates : List (ElementaryCoordinate n) :=
  (canonicalRouterTerminalTargets n hn mate hinv k reverse).toList.attach.map fun t =>
    ⟨t.val, matchingClass (routingReservoir n (routingReservoirWidth n (canonicalRouterGap n))
      (routingReservoir_fit n (canonicalRouterGap n) hn)) mate k t.val, by
      intro he
      exact canonicalRouterTerminal_source n hn mate hinv k reverse t.val
        (Finset.mem_toList.mp t.property) (by rw [he]; exact Finset.mem_toList.mp t.property)⟩

theorem canonicalRouterTerminalCoordinates_targets :
    (canonicalRouterTerminalCoordinates n hn mate hinv k reverse).map ElementaryCoordinate.target =
      (canonicalRouterTerminalTargets n hn mate hinv k reverse).toList := by
  simp only [canonicalRouterTerminalCoordinates, List.map_map, Function.comp_def]
  simp

theorem canonicalRouterTerminalCoordinates_count :
    (canonicalRouterTerminalCoordinates n hn mate hinv k reverse).length < 131 * canonicalRouterGap n := by
  rw [canonicalRouterTerminalCoordinates, List.length_map, List.length_attach, Finset.length_toList]
  unfold canonicalRouterTerminalTargets
  rw [Finset.card_image_of_injective _ (canonicalRouterMiddleEmbedding_injective n hn k)]
  exact routerTerminalTargets_spacing n (canonicalRouterGap n) _ (canonicalRouterGap_pos n) hn


theorem canonicalRouterTerminalCoordinates_source
    (c : ElementaryCoordinate n) (hc : c ∈ canonicalRouterTerminalCoordinates n hn mate hinv k reverse) :
    c.source = matchingClass (routingReservoir n (routingReservoirWidth n (canonicalRouterGap n))
      (routingReservoir_fit n (canonicalRouterGap n) hn)) mate k c.target := by
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hc
  rfl

/-- The existing compiler's coordinate contract suffices to identify the
compiled physical terminal instructions, without any supplied shear premise. -/
theorem canonicalRouterTerminalInstructions_bits (R : ℕ) (ds : List (ElementaryInstruction n))
    (hkeys : ds.map (fun d => (d.target, d.source)) =
      (canonicalRouterTerminalCoordinates n hn mate hinv k reverse).reverse.map ElementaryCoordinate.key)
    (i : Fin (R * 2 ^ n)) :
    (fun q : Fin n => (elementaryInstructionsRank R ds i).val.testBit q.val) =
      shear (canonicalRouterTerminalTargets n hn mate hinv k reverse)
        (matchingClass (routingReservoir n (routingReservoirWidth n (canonicalRouterGap n))
          (routingReservoir_fit n (canonicalRouterGap n) hn)) mate k)
        (fun q => i.val.testBit q.val) := by
  apply elementaryInstructionsRank_shear R _ _ (canonicalRouterTerminal_source n hn mate hinv k reverse) ds
  · intro d hd
    have hmem : (d.target, d.source) ∈ ds.map (fun d => (d.target, d.source)) := List.mem_map.mpr ⟨d, hd, rfl⟩
    rw [hkeys] at hmem
    obtain ⟨c, hc, he⟩ := List.mem_map.mp hmem
    have htarget := congrArg Prod.fst he
    have hsource := congrArg Prod.snd he
    change c.target = d.target at htarget
    change c.source = d.source at hsource
    rw [← hsource, canonicalRouterTerminalCoordinates_source n hn mate hinv k reverse c (List.mem_reverse.mp hc), htarget]
  · have h := congrArg (fun xs => (xs.map Prod.fst).reverse) hkeys
    simpa only [List.map_map, List.map_reverse, List.reverse_reverse, Function.comp_def,
      ElementaryCoordinate.key, canonicalRouterTerminalCoordinates_targets] using h

end
end IntegerMultBounds.MathlibTM2.Routing
