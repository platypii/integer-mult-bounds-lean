import IntegerMultBounds.Machine.BinaryRadixEqualShared

/-! Physical interchange of equally sized dirty address fields. The prefix,
intervening coordinates and complete suffix records are retained. Both calls
of the roundtrip run the fixed binary interchange machine, including header
copies, padding and cleanup; no payload permutation is a free tape reindexing.
The conjugation lemma is the data interface for a later swap/load/swap gadget.
-/
namespace IntegerMultBounds.Machine.BinaryPackedFieldSwap
noncomputable section
open Networks.Shared50ModularControl (prime)
open SharedPlacementAlphabet (setTape)
open BinaryAdjacentWidthHeadersShared (Sources)
open RadixRangePadding (volume index coordinates transpose)
variable {t P N G B : ℕ} {α : Type*}

/-- Address permutation underlying the actual physical interchange. -/
def address : Equiv.Perm (Fin (volume P N G B)) where
  toFun z := let c := coordinates z; index c.1 c.2.2.2.1 c.2.2.1 c.2.1 c.2.2.2.2
  invFun z := let c := coordinates z; index c.1 c.2.2.2.1 c.2.2.1 c.2.1 c.2.2.2.2
  left_inv z := by simp only [RadixRangePadding.coordinates_index]; exact RadixRangePadding.index_coordinates z
  right_inv z := by simp only [RadixRangePadding.coordinates_index]; exact RadixRangePadding.index_coordinates z

theorem address_index (p : Fin P) (front back : Fin N) (g : Fin G) (j : Fin B) :
    address (index p front g back j) = index p back g front j := by
  simp [address]

theorem transpose_involutive (x : Fin (volume P N G B) → α) :
    transpose (transpose x) = x := by
  funext z
  change x (address (address z)) = x z
  exact congrArg x (address.left_inv z)

/-- Readback action on the back field, allowing an arbitrary prefix and
intervening-coordinate dependent action. No suffix symbol is changed. -/
def backAction (f : Fin P → Fin G → Fin N → Fin N)
    (x : Fin (volume P N G B) → α) : Fin (volume P N G B) → α := fun z =>
  let c := coordinates z
  x (index c.1 c.2.1 c.2.2.1 (f c.1 c.2.2.1 c.2.2.2.1) c.2.2.2.2)

def frontAction (f : Fin P → Fin G → Fin N → Fin N)
    (x : Fin (volume P N G B) → α) : Fin (volume P N G B) → α := fun z =>
  let c := coordinates z
  x (index c.1 (f c.1 c.2.2.1 c.2.1) c.2.2.1 c.2.2.2.1 c.2.2.2.2)

/-- Swapping a dirty front field to the back, acting there, and swapping back
retains the original back coordinate and every arbitrary suffix symbol. -/
theorem swap_back_swap (f : Fin P → Fin G → Fin N → Fin N)
    (x : Fin (volume P N G B) → α) :
    transpose (backAction f (transpose x)) = frontAction f x := by
  funext z
  simp [transpose,backAction,frontAction]

theorem swap_back_swap_entry (f : Fin P → Fin G → Fin N → Fin N)
    (x : Fin (volume P N G B) → α)
    (p : Fin P) (front back : Fin N) (g : Fin G) (j : Fin B) :
    transpose (backAction f (transpose x)) (index p front g back j) =
      x (index p (f p g front) g back j) := by
  rw [swap_back_swap]
  simp [frontAction]

def store (caller : Tapes t prime) (payload : Fin t)
    (x : Fin (volume P N G B) → Bool) : Tapes t prime :=
  setTape caller payload (BinaryRadixRangePrepareAlphabet.word (fun i => bitSymbol (x i))) 0

theorem store_store (caller : Tapes t prime) (payload : Fin t)
    (x y : Fin (volume P N G B) → Bool) :
    store (store caller payload x) payload y = store caller payload y :=
  SharedPlacementAlphabet.setTape_setTape _ _ _ _ _ _

theorem store_sources (caller : Tapes t prime) (focus : Fin 4 → Fin t)
    (payload : Fin t) (hs : Fin 4 → List Bool)
    (hne : ∀ i, focus i ≠ payload) (hsrc : Sources caller focus hs)
    (x : Fin (volume P N G B) → Bool) : Sources (store caller payload x) focus hs := by
  constructor
  · intro i
    simpa only [store,setTape,Function.update_of_ne (hne i)] using hsrc.tape i
  · intro i
    simpa only [store,setTape,Function.update_of_ne (hne i)] using hsrc.head i

/-- Program wiring is independent of all four runtime dimensions. -/
def program (focus : Fin 4 → Fin t) (payload : Fin t) := BinaryRadixEqualShared.program focus payload
def roundtrip (focus : Fin 4 → Fin t) (payload : Fin t) := seq (program focus payload) (program focus payload)

/-- Complete physical execution on a common caller-owned payload tape. -/
theorem swaps (caller : Tapes t prime) (focus : Fin 4 → Fin t) (payload : Fin t)
    (P G B u : ℕ) (hs : Fin 4 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = BinaryRadixRangePrepare.values P G B u i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (hne : ∀ i, focus i ≠ payload) (hsrc : Sources caller focus hs)
    (x : Fin (volume P (2^u) G B) → Bool) :
    HoareTime (program focus payload)
      (fun v => v = BinaryRadixEqualShared.input (store caller payload x))
      (fun v => v = BinaryRadixEqualShared.input (store caller payload (transpose x)))
      (BinaryRadixEqualShared.cost P G B u hs) := by
  have hh := BinaryRadixEqualShared.runs (store caller payload x) focus payload P G B u hs
    hv hc hP hG hB (store_sources caller focus payload hs hne hsrc x) x
    (by simp [store,setTape]) (by simp [store,setTape])
  have he : transpose (fun i => (bitSymbol (x i) : Fin (prime+4))) =
      (fun i => bitSymbol (transpose x i)) := rfl
  rw [he] at hh
  simpa only [program,store,SharedPlacementAlphabet.setTape_setTape] using hh

/-- Two real interchanges restore the entire caller bank, including arbitrary
dirty address fields and all payload bits. Generated private tapes are blank
between calls and on return; the join transition is explicitly charged. -/
theorem roundtrip_hoare (caller : Tapes t prime) (focus : Fin 4 → Fin t) (payload : Fin t)
    (P G B u : ℕ) (hs : Fin 4 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = BinaryRadixRangePrepare.values P G B u i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (hne : ∀ i, focus i ≠ payload) (hsrc : Sources caller focus hs)
    (x : Fin (volume P (2^u) G B) → Bool) :
    HoareTime (roundtrip focus payload)
      (fun v => v = BinaryRadixEqualShared.input (store caller payload x))
      (fun v => v = BinaryRadixEqualShared.input (store caller payload x))
      (2*BinaryRadixEqualShared.cost P G B u hs+1) := by
  have h₁ := swaps caller focus payload P G B u hs hv hc hP hG hB hne hsrc x
  have h₂ := swaps caller focus payload P G B u hs hv hc hP hG hB hne hsrc (transpose x)
  rw [transpose_involutive] at h₂
  apply (h₁.seq h₂).consequence (fun _ h => h) (fun _ h => h)
  omega

/-- Reusable interchange and restoration retain the uniform sublinear-width
overhead of the binary interchange theorem. -/
theorem roundtrip_uniform_bound : ∃ C : ℝ, 0 < C ∧ ∀ (P G B u : ℕ) (hs : Fin 4 → List Bool),
    0 < P → 0 < G → 0 < B →
    (∀ i, Counter.value (hs i) = BinaryRadixRangePrepare.values P G B u i) →
    (∀ i, GrowingCounterData.Canonical (hs i)) →
    ((2*BinaryRadixEqualShared.cost P G B u hs+1 : ℕ) : ℝ) ≤
      C*(volume P (2^u) G B : ℝ)*((max 1 u : ℕ) : ℝ)^Parameters.tau := by
  obtain ⟨C,hC,hbound⟩ := BinaryRadixEqualShared.uniform_bound
  refine ⟨2*C+1,by linarith,?_⟩
  intro P G B u hs hP hG hB hv hc
  have hb := hbound P G B u hs hP hG hB hv hc
  have hV : 1 ≤ (volume P (2^u) G B : ℝ) := by
    have hn : 0 < volume P (2^u) G B := by unfold volume; positivity
    exact_mod_cast hn
  have hp : 1 ≤ ((max 1 u : ℕ) : ℝ)^Parameters.tau := Real.one_le_rpow
    (by exact_mod_cast le_max_left 1 u) Shared50RecursiveBudgetBound.exponent_range.1.le
  have hvp : 1 ≤ (volume P (2^u) G B : ℝ)*((max 1 u : ℕ) : ℝ)^Parameters.tau :=
    calc 1 = 1*1 := by ring
         _ ≤ _ := mul_le_mul hV hp (by norm_num) (by linarith)
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
  nlinarith only [hb,hvp]

end
end IntegerMultBounds.Machine.BinaryPackedFieldSwap
