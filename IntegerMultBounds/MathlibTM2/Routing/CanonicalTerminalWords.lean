module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalTerminalLayout
public import IntegerMultBounds.MathlibTM2.Routing.CanonicalRouterTerminal

/-! Every terminal input word uses symbols below the common framing delimiter. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host
noncomputable section

private theorem bitWords_small {A : ℕ} (bits : List Bool) :
    ∀ x ∈ (bits.map bitSymbol : List (Fin (A + 4))), x.val < 8 := by
  intro x hx
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
  simp only [bitSymbol]
  split <;> omega

theorem elementaryCompilerInputWords_small {A : ℕ} (n L Lb B : ℕ) (rowBits : List Bool)
    (c : ElementaryCompilerReg) :
    ∀ x ∈ (elementaryCompilerInputWords n L Lb B rowBits c : List (Fin (A + 4))), x.val < 8 := by
  cases c with
  | coordinate r =>
    cases r <;> simp only [elementaryCompilerInputWords]
    all_goals first | exact canonicalScalarWord_small _ _ | simp
  | rows => exact bitWords_small rowBits
  | block => exact canonicalScalarWord_small _ _
  | header i => simp [elementaryCompilerInputWords]
  | mask => simp [elementaryCompilerInputWords]
  | output => simp [elementaryCompilerInputWords]

theorem sharedInputInitialWords_small {A : ℕ} (L n Lb B : ℕ) (rowBits : List Bool)
    (r : SharedInputReg) :
    ∀ x ∈ (sharedInputInitialWords L n Lb B rowBits r : List (Fin (A + 4))), x.val < 8 := by
  cases r <;> simp only [sharedInputInitialWords]
  all_goals first | exact canonicalScalarWord_small _ _ | exact bitWords_small rowBits | simp

/-- Structural register cases suffice; no concrete tape-bank enumeration is used. -/
theorem canonicalTerminalRoutingBank_small {A : ℕ} (stream : List (Fin (A + 4)))
    (hstream : ∀ x ∈ stream, x.val < 8) (n L Lb B : ℕ) (rowBits : List Bool)
    (cs : List (ElementaryCoordinate n)) :
    ∀ j, ∀ x ∈ canonicalTerminalRoutingBank canonicalTerminalRouter canonicalTerminalCompiler canonicalTerminalInput
      (canonicalTerminalAux 0) stream (elementaryCoordinateFrames L cs) n L Lb B rowBits j, x.val < 8 := by
  intro j
  obtain ⟨r, rfl⟩ := (Fintype.equivFin CanonicalTerminalReg).surjective j
  cases r with
  | router r =>
    change ∀ x ∈ canonicalTerminalRoutingBank _ _ _ _ _ _ _ _ _ _ _ (canonicalTerminalRouter r), x.val < 8
    rw [canonicalTerminalBank_fixed_router]
    split
    · exact hstream
    · simp
  | compiler c =>
    change ∀ x ∈ canonicalTerminalRoutingBank _ _ _ _ _ _ _ _ _ _ _ (canonicalTerminalCompiler c), x.val < 8
    rw [canonicalTerminalBank_fixed_compiler]
    exact elementaryCompilerInputWords_small _ _ _ _ _ c
  | input r =>
    change ∀ x ∈ canonicalTerminalRoutingBank _ _ _ _ _ _ _ _ _ _ _ (canonicalTerminalInput r), x.val < 8
    rw [canonicalTerminalBank_fixed_input]
    exact sharedInputInitialWords_small _ _ _ _ _ r
  | aux i =>
    change ∀ x ∈ canonicalTerminalRoutingBank _ _ _ _ _ _ _ _ _ _ _ (canonicalTerminalAux i), x.val < 8
    rw [canonicalTerminalBank_fixed_aux]
    split
    · exact elementaryCoordinateFrames_small L cs
    · simp

/-- Every nonstream terminal word is a scalar operand or the coordinate table. -/
theorem canonicalTerminalRoutingBank_length_le {A : ℕ}
    (stream coordinates : List (Fin (A + 4))) (n L Lb B : ℕ) (rowBits : List Bool)
    (j : Fin canonicalTerminalT) (hj : j ≠ canonicalTerminalRouter .str) :
    (canonicalTerminalRoutingBank canonicalTerminalRouter canonicalTerminalCompiler canonicalTerminalInput
      (canonicalTerminalAux 0) stream coordinates n L Lb B rowBits j).length ≤
      L + Lb + rowBits.length + coordinates.length := by
  obtain ⟨r, rfl⟩ := (Fintype.equivFin CanonicalTerminalReg).surjective j
  cases r with
  | router r =>
    change (canonicalTerminalRoutingBank _ _ _ _ _ _ _ _ _ _ _ (canonicalTerminalRouter r)).length ≤ _
    change canonicalTerminalRouter r ≠ canonicalTerminalRouter .str at hj
    rw [canonicalTerminalBank_fixed_router, ite_eq_right hj]
    exact Nat.zero_le _
  | compiler c =>
    change (canonicalTerminalRoutingBank _ _ _ _ _ _ _ _ _ _ _ (canonicalTerminalCompiler c)).length ≤ _
    rw [canonicalTerminalBank_fixed_compiler]
    cases c with
    | coordinate r => cases r <;> simp only [elementaryCompilerInputWords, length_binSyms, List.length_nil] <;> omega
    | rows => simp [elementaryCompilerInputWords]; omega
    | block => simp [elementaryCompilerInputWords]; omega
    | header i => simp [elementaryCompilerInputWords]
    | mask => simp [elementaryCompilerInputWords]
    | output => simp [elementaryCompilerInputWords]
  | input r =>
    change (canonicalTerminalRoutingBank _ _ _ _ _ _ _ _ _ _ _ (canonicalTerminalInput r)).length ≤ _
    rw [canonicalTerminalBank_fixed_input]
    cases r <;> simp [sharedInputInitialWords] <;> omega
  | aux i =>
    change (canonicalTerminalRoutingBank _ _ _ _ _ _ _ _ _ _ _ (canonicalTerminalAux i)).length ≤ _
    rw [canonicalTerminalBank_fixed_aux]
    split <;> simp_all


/-- Framing supplies the current record stream without changing terminal metadata. -/
theorem canonicalTerminalRoutingBank_updateStream {A : ℕ}
    (stream replacement coordinates : List (Fin (A + 4))) (n L Lb B : ℕ) (rowBits : List Bool) :
    Function.update
      (canonicalTerminalRoutingBank canonicalTerminalRouter canonicalTerminalCompiler canonicalTerminalInput
        (canonicalTerminalAux 0) stream coordinates n L Lb B rowBits)
      (canonicalTerminalRouter .str) replacement =
      canonicalTerminalRoutingBank canonicalTerminalRouter canonicalTerminalCompiler canonicalTerminalInput
        (canonicalTerminalAux 0) replacement coordinates n L Lb B rowBits := by
  funext j
  obtain ⟨r, rfl⟩ := (Fintype.equivFin CanonicalTerminalReg).surjective j
  cases r with
  | router r =>
    change Function.update (canonicalTerminalRoutingBank canonicalTerminalRouter canonicalTerminalCompiler canonicalTerminalInput
      (canonicalTerminalAux 0) stream coordinates n L Lb B rowBits) (canonicalTerminalRouter .str) replacement (canonicalTerminalRouter r) = canonicalTerminalRoutingBank canonicalTerminalRouter canonicalTerminalCompiler canonicalTerminalInput (canonicalTerminalAux 0) replacement coordinates n L Lb B rowBits (canonicalTerminalRouter r)
    by_cases hr : r = .str
    · subst r
      rw [Function.update_self]
      simp only [canonicalTerminalBank_fixed_router, ite_true]
    · rw [Function.update_of_ne (canonicalTerminalRouter_injective.ne hr)]
      simp only [canonicalTerminalBank_fixed_router, ite_eq_right (canonicalTerminalRouter_injective.ne hr)]
  | compiler c =>
    change Function.update (canonicalTerminalRoutingBank canonicalTerminalRouter canonicalTerminalCompiler canonicalTerminalInput
      (canonicalTerminalAux 0) stream coordinates n L Lb B rowBits) (canonicalTerminalRouter .str) replacement (canonicalTerminalCompiler c) = canonicalTerminalRoutingBank canonicalTerminalRouter canonicalTerminalCompiler canonicalTerminalInput (canonicalTerminalAux 0) replacement coordinates n L Lb B rowBits (canonicalTerminalCompiler c)
    rw [Function.update_of_ne (by simp [canonicalTerminalCompiler, canonicalTerminalRouter])]
    simp only [canonicalTerminalBank_fixed_compiler]
  | input r =>
    change Function.update (canonicalTerminalRoutingBank canonicalTerminalRouter canonicalTerminalCompiler canonicalTerminalInput
      (canonicalTerminalAux 0) stream coordinates n L Lb B rowBits) (canonicalTerminalRouter .str) replacement (canonicalTerminalInput r) = canonicalTerminalRoutingBank canonicalTerminalRouter canonicalTerminalCompiler canonicalTerminalInput (canonicalTerminalAux 0) replacement coordinates n L Lb B rowBits (canonicalTerminalInput r)
    rw [Function.update_of_ne (by simp [canonicalTerminalInput, canonicalTerminalRouter])]
    simp only [canonicalTerminalBank_fixed_input]
  | aux i =>
    change Function.update (canonicalTerminalRoutingBank canonicalTerminalRouter canonicalTerminalCompiler canonicalTerminalInput
      (canonicalTerminalAux 0) stream coordinates n L Lb B rowBits) (canonicalTerminalRouter .str) replacement (canonicalTerminalAux i) = canonicalTerminalRoutingBank canonicalTerminalRouter canonicalTerminalCompiler canonicalTerminalInput (canonicalTerminalAux 0) replacement coordinates n L Lb B rowBits (canonicalTerminalAux i)
    rw [Function.update_of_ne (by simp [canonicalTerminalAux, canonicalTerminalRouter])]
    simp only [canonicalTerminalBank_fixed_aux]

end
end IntegerMultBounds.MathlibTM2.Routing
