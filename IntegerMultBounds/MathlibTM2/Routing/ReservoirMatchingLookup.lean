module

public import IntegerMultBounds.MathlibTM2.Routing.ReservoirCoordinateExec
public import IntegerMultBounds.MathlibTM2.Routing.MatchingTableLookup
public import IntegerMultBounds.MathlibTM2.Routing.ReservoirMiddleMatching

/-! Executed lookup in placed coordinates, using the physical matching table.
Forward and backward schedules share the coordinate register; their metadata
may occupy separate tapes. Only that coordinate changes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def reservoirMatchingLookupProgram (forward backward : Fin 14 → Fin T)
    (lookup : Fin 10 → Fin T) (out : Fin T) : Pr P T Q A U :=
  .seq (binaryCoordinateScheduleProgram forward)
    (.seq (matchingTableLookupInPlaceProgram lookup out)
      (binaryCoordinateScheduleProgram backward))

theorem reservoirMatchingLookup_exec (body : P → Pr P T Q A U)
    (n H : ℕ) (hfit : 9 * H ≤ n) (w : ℕ) (hw : w ≤ H) (k : Fin 3)
    (forward backward : Fin 14 → Fin T) (lookup : Fin 10 → Fin T) (out : Fin T)
    (hf : Function.Injective forward) (hb : Function.Injective backward)
    (hl : Function.Injective lookup) (hout : ∀ j, out ≠ lookup j)
    (hback : backward 0 = forward 0) (hquery : lookup 2 = forward 0)
    (L : ℕ) (hn : n < 2 ^ L) (mate : Fin n → Fin n) (q : Fin n)
    (v : HS T Q A U) (S : Stacks T A)
    (hcoordinate : S.R (forward 0) = binSyms L q.val)
    (hblank : ∀ (rg : Fin 14 → Fin T), rg = forward ∨ rg = backward →
      ∀ j : Fin 14, (1 ≤ j.val ∧ j.val < 10) ∨ j = 13 → S.R (rg j) = [])
    (hmetadata : ∀ inverse : Bool,
      let rg := if inverse then backward else forward
      S.R (rg 11) = delimitedScheduleInput
        (fun j => delimitedBankFrames separator
          (coordinateExchangeJobs (A := A) rg L (reservoirExchangeSpecs n H hfit w hw k j)))
        (reservoirCoordinateOrder inverse))
    (hsaved : S.R (forward 12) = [] ∧ S.R (backward 12) = [])
    (hlookupBlank : ∀ j : Fin 10,
      j = 0 ∨ j = 1 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 9 → S.R (lookup j) = [])
    (htable : S.R (lookup 7) = matchingEntryWords L (matchingTableEntries n (matchingMateCoordinate mate)))
    (hlookupSaved : S.R (lookup 8) = []) (houtput : S.R out = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ n * (30 * L + 39) + 562 * L + 670 ∧
      Exec body (reservoirMatchingLookupProgram forward backward lookup out) (mk v S) steps
        (mk v' { S with R := Function.update S.R (forward 0) (binSyms L (placedSource (reservoirPlacement n H hfit w hw k) mate q).val) }) := by
  let e := reservoirPlacement n H hfit w hw k
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := reservoirCoordinate_exec n H hfit w hw k body
    forward hf L hn false q v S hcoordinate (hblank forward (Or.inl rfl))
    (hmetadata false) hsaved.1
  let G : Stacks T A := { S with R := Function.update S.R (forward 0) (binSyms L (e q).val) }
  have hkeep (j : Fin 10) (hj : j ≠ 2) : G.R (lookup j) = S.R (lookup j) := by
    have hne : lookup j ≠ forward 0 := by rw [← hquery]; exact hl.ne hj
    simp [G, hne]
  have ready : MatchingLookupReady lookup L (e q) G := by
    constructor
    · simp [G, hquery]
    · intro j hj
      rw [hkeep j (by rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
      exact hlookupBlank j hj
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := matchingTableLookupInPlace_exec body lookup hl out hout
    L (Nat.le_of_lt hn) mate (e q) v₁ G ready
    ((hkeep 7 (by decide)).trans htable) ((hkeep 8 (by decide)).trans hlookupSaved)
    (by have hne : out ≠ forward 0 := by rw [← hquery]; exact hout 2
        simpa [G, hne] using houtput)
  let J : Stacks T A := { S with R := Function.update S.R (forward 0) (binSyms L (mate (e q)).val) }
  have hcollapse : { G with R := Function.update G.R (lookup 2) (binSyms L (mate (e q)).val) } = J := by
    simp [J, G, hquery]
  rw [hcollapse] at he₂
  have hbackKeep (j : Fin 14) (hj : j ≠ 0) : J.R (backward j) = S.R (backward j) := by
    have hne : backward j ≠ forward 0 := by rw [← hback]; exact hb.ne hj
    simp [J, hne]
  obtain ⟨v₃, m₃, hu₃, hm₃, he₃⟩ := reservoirCoordinate_exec n H hfit w hw k body
    backward hb L hn true (mate (e q)) v₂ J
    (by simp [J, hback])
    (by intro j hj
        have hj0 : j ≠ 0 := by
          rcases hj with hj | rfl
          · intro h; subst j; norm_num at hj
          · decide
        rw [hbackKeep j hj0]
        exact hblank backward (Or.inr rfl) j hj)
    ((hbackKeep 11 (by decide)).trans (hmetadata true))
    ((hbackKeep 12 (by decide)).trans hsaved.2)
  have hfinal : { J with R := Function.update J.R (backward 0) (binSyms L (e.symm (mate (e q))).val) } =
      { S with R := Function.update S.R (forward 0) (binSyms L (placedSource e mate q).val) } := by
    simp [J, hback, placedSource]
  change Exec body (binaryCoordinateScheduleProgram backward) (mk v₂ J) m₃
    (mk v₃ { J with R := Function.update J.R (backward 0) (binSyms L (e.symm (mate (e q))).val) }) at he₃
  rw [hfinal] at he₃
  exact ⟨v₃, m₁ + (m₂ + m₃), hu₃.trans (hu₂.trans hu₁), by omega,
    Exec.seq he₁ (Exec.seq he₂ he₃)⟩

end IntegerMultBounds.MathlibTM2.Routing
