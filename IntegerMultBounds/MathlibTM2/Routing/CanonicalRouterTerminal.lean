module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalRouterBits
public import IntegerMultBounds.MathlibTM2.Routing.ElementaryCompileLoopData
public import IntegerMultBounds.MathlibTM2.Routing.CompiledElementarySemantics

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
  exact compiledElementary_shear R _ _ (canonicalRouterTerminal_source n hn mate hinv k reverse)
    _ (canonicalRouterTerminalCoordinates_source n hn mate hinv k reverse)
    (canonicalRouterTerminalCoordinates_targets n hn mate hinv k reverse) ds hkeys i


/-- The executed bulk and terminal target sets cover the full directional class
without overlap, so their physical shear actions compose without lost bits. -/
theorem canonicalRouter_bulk_terminal_shear (x : Fin n → Bool) :
    shear ((routerBulkTargets n (canonicalRouterStride n) (canonicalRouterGap n)
      (matchingDirectionTargets (canonicalRouterLocalMatching n hn k mate hinv) reverse)).image
        (canonicalRouterMiddleEmbedding n hn k))
      (matchingClass (routingReservoir n (routingReservoirWidth n (canonicalRouterGap n))
        (routingReservoir_fit n (canonicalRouterGap n) hn)) mate k)
      (shear (canonicalRouterTerminalTargets n hn mate hinv k reverse)
        (matchingClass (routingReservoir n (routingReservoirWidth n (canonicalRouterGap n))
          (routingReservoir_fit n (canonicalRouterGap n) hn)) mate k) x) =
    shear ((matchingDirectionTargets (canonicalRouterLocalMatching n hn k mate hinv) reverse).image
      (canonicalRouterMiddleEmbedding n hn k))
      (matchingClass (routingReservoir n (routingReservoirWidth n (canonicalRouterGap n))
        (routingReservoir_fit n (canonicalRouterGap n) hn)) mate k) x := by
  let targets := matchingDirectionTargets (canonicalRouterLocalMatching n hn k mate hinv) reverse
  let f := canonicalRouterMiddleEmbedding n hn k
  let bulk := routerBulkTargets n (canonicalRouterStride n) (canonicalRouterGap n) targets
  let terminal := routerTerminalTargets n (canonicalRouterStride n) (canonicalRouterGap n) targets
  have hunion : bulk.image f ∪ terminal.image f = targets.image f := by
    rw [← Finset.image_union]
    congr 1
    ext q
    simp only [bulk, terminal, routerBulkTargets, routerTerminalTargets, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hq, _⟩ | ⟨hq, _⟩) <;> exact hq
    · intro hq
      by_cases hb : q.val < routerDigits n (canonicalRouterStride n) (canonicalRouterGap n) * canonicalRouterStride n
      · exact Or.inl ⟨hq, hb⟩
      · exact Or.inr ⟨hq, Nat.le_of_not_gt hb⟩
  have hdisjoint : Disjoint (bulk.image f) (terminal.image f) := by
    apply Finset.disjoint_left.mpr
    intro q hb ht
    obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hb
    obtain ⟨b, hb, he'⟩ := Finset.mem_image.mp ht
    have hab : a = b := canonicalRouterMiddleEmbedding_injective n hn k (he.trans he'.symm)
    subst b
    have ha' := (Finset.mem_filter.mp ha).2
    have hb' := (Finset.mem_filter.mp hb).2
    omega
  have hsource := canonicalRouterMiddleTargets_source n hn mate hinv k reverse targets (fun _ h => h)
  have hs : ∀ i ∈ bulk.image f ∪ terminal.image f,
      matchingClass (routingReservoir n (routingReservoirWidth n (canonicalRouterGap n))
        (routingReservoir_fit n (canonicalRouterGap n) hn)) mate k i ∉ bulk.image f ∪ terminal.image f := by
    rw [hunion]
    exact hsource
  exact (shear_union (bulk.image f) (terminal.image f) _ hdisjoint hs x).trans
    (congrArg (fun ts => shear ts _ x) hunion)


/-- Terminal coordinate-table frames leave room for the common delimiter. -/
theorem elementaryCoordinateFrames_small {A N : ℕ} (L : ℕ) (cs : List (ElementaryCoordinate N)) :
    ∀ x ∈ (elementaryCoordinateFrames L cs : List (Fin (A + 4))), x.val < 8 := by
  induction cs with
  | nil => simp [elementaryCoordinateFrames]
  | cons c cs ih =>
    intro x hx
    simp only [elementaryCoordinateFrames, elementaryPairWords, configurationWords, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (hx | rfl | hx | rfl) | hx
    · exact canonicalScalarWord_small _ _ x hx
    · change 3 < 8
      omega
    · exact canonicalScalarWord_small _ _ x hx
    · change 3 < 8
      omega
    · exact ih x hx


def canonicalRouterTerminalPerm (rows : ℕ) : Equiv.Perm (Fin (rows * 2 ^ n)) :=
  elementaryRankSchedule rows
    (matchingClass (routingReservoir n (routingReservoirWidth n (canonicalRouterGap n))
      (routingReservoir_fit n (canonicalRouterGap n) hn)) mate k)
    (canonicalRouterTerminalTargets n hn mate hinv k reverse).toList

/-- Compiler headers do not affect the terminal output permutation. -/
theorem canonicalRouterTerminalInstructions_perm (rows : ℕ) (ds : List (ElementaryInstruction n))
    (hkeys : ds.map (fun d => (d.target, d.source)) =
      (canonicalRouterTerminalCoordinates n hn mate hinv k reverse).reverse.map ElementaryCoordinate.key) :
    elementaryInstructionsRank rows ds = canonicalRouterTerminalPerm n hn mate hinv k reverse rows := by
  apply Equiv.ext
  intro i
  apply Fin.ext
  have hbits := canonicalRouterTerminalInstructions_bits n hn mate hinv k reverse rows ds hkeys i
  have hideal := elementaryRankSchedule_shear rows _ _
    (canonicalRouterTerminal_source n hn mate hinv k reverse) i
  have hlow := hbits.trans hideal.symm
  have hrow := (compiledElementary_row rows ds i).trans
    (elementaryRankSchedule_row rows
      (matchingClass (routingReservoir n (routingReservoirWidth n (canonicalRouterGap n))
        (routingReservoir_fit n (canonicalRouterGap n) hn)) mate k)
      (canonicalRouterTerminalTargets n hn mate hinv k reverse).toList i).symm
  apply Nat.eq_of_testBit_eq
  intro q
  by_cases hq : q < n
  · exact congrFun hlow ⟨q, hq⟩
  · have h := congrArg (fun j : ℕ => j.testBit (q - n)) hrow
    simpa only [canonicalRouterTerminalPerm, Nat.testBit_div_two_pow, Nat.sub_add_cancel (Nat.le_of_not_gt hq)] using h

end
end IntegerMultBounds.MathlibTM2.Routing
