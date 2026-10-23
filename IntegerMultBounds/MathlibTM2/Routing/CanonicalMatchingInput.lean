module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalMatchingExec

/-! The intermediate records for the executed matching schedule are pure
constructions from the original records, rather than supplied witnesses. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine
open IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {Q K : ℕ} (n : ℕ) (hn : canonicalRouterStride n ≤ n)
    (R B : ℕ) (hR : 0 < R) (hB : 1 ≤ B) (mate : Fin n → Fin n) (hinv : Function.Involutive mate)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q) (hA : 4 ≤ prime + K)
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ n)
    (hlen : ∀ row ∈ l, row.length = B ∧ ∀ x ∈ row, x.val < 8)

def canonicalClassInputOf (k : Fin 3) : CanonicalClassInput n hn R B hR hB mate hinv k hQ hA := by
  let π₀ := canonicalRouterDirectionalPerm n hn R B hR hB mate hinv k false hQ hA l hl hlen
    (List.finRange (canonicalRouterStride n))
  let l₁ := moveRecs π₀ l
  have hl₁ : l₁.length = R * 2 ^ n := length_moveRecs _ _
  have hlen₁ : ∀ row ∈ l₁, row.length = B ∧ ∀ x ∈ row, x.val < 8 :=
    fun row hr => hlen row (mem_moveRecs π₀ hl hr)
  let π₁ := canonicalRouterDirectionalPerm n hn R B hR hB mate hinv k true hQ hA l₁ hl₁ hlen₁
    (List.finRange (canonicalRouterStride n))
  let l₂ := moveRecs π₁ l₁
  have hl₂ : l₂.length = R * 2 ^ n := length_moveRecs _ _
  have hlen₂ : ∀ row ∈ l₂, row.length = B ∧ ∀ x ∈ row, x.val < 8 :=
    fun row hr => hlen₁ row (mem_moveRecs π₁ hl₁ hr)
  refine { records := fun d => if d = 0 then l else if d = 1 then l₁ else l₂
           count := ?_, shape := ?_, next₁ := ?_, next₂ := ?_ }
  · intro d
    split
    · exact hl
    · split
      · exact hl₁
      · exact hl₂
  · intro d
    split
    · exact hlen
    · split
      · exact hlen₁
      · exact hlen₂
  · rfl
  · rfl

theorem canonicalClassInputOf_records_zero (k : Fin 3) :
    (canonicalClassInputOf n hn R B hR hB mate hinv hQ hA l hl hlen k).records 0 = l := rfl

def canonicalMatchingInput : (k : Fin 3) → CanonicalClassInput n hn R B hR hB mate hinv k hQ hA := by
  let input₂ := canonicalClassInputOf n hn R B hR hB mate hinv hQ hA l hl hlen 2
  let l₁ := moveRecs input₂.perm l
  have hl₁ : l₁.length = R * 2 ^ n := length_moveRecs _ _
  have hlen₁ : ∀ row ∈ l₁, row.length = B ∧ ∀ x ∈ row, x.val < 8 :=
    fun row hr => hlen row (mem_moveRecs input₂.perm hl hr)
  let input₁ := canonicalClassInputOf n hn R B hR hB mate hinv hQ hA l₁ hl₁ hlen₁ 1
  let l₀ := moveRecs input₁.perm l₁
  have hl₀ : l₀.length = R * 2 ^ n := length_moveRecs _ _
  have hlen₀ : ∀ row ∈ l₀, row.length = B ∧ ∀ x ∈ row, x.val < 8 :=
    fun row hr => hlen₁ row (mem_moveRecs input₁.perm hl₁ hr)
  let input₀ := canonicalClassInputOf n hn R B hR hB mate hinv hQ hA l₀ hl₀ hlen₀ 0
  intro k
  refine Fin.cases input₀ (fun j => ?_) k
  refine Fin.cases input₁ (fun j => ?_) j
  have hj : j = 0 := Fin.eq_zero j
  subst j
  exact input₂

local notation "inputs" => canonicalMatchingInput n hn R B hR hB mate hinv hQ hA l hl hlen

theorem canonicalMatchingInput_records_two : (inputs 2).records 0 = l := rfl

theorem canonicalMatchingInput_next_one :
    (inputs 1).records 0 = moveRecs (inputs 2).perm ((inputs 2).records 0) := rfl

theorem canonicalMatchingInput_next_zero :
    (inputs 0).records 0 = moveRecs (inputs 1).perm ((inputs 1).records 0) := rfl

variable (L Lb : ℕ) (rowBits : List Bool)

def canonicalMatchingFrame : List (Fin (prime + K + 4)) :=
  (inputs 2).frame L Lb rowBits ++ ((inputs 1).frame L Lb rowBits ++ (inputs 0).frame L Lb rowBits)

theorem canonicalMatchingFrame_length_le :
    (canonicalMatchingFrame n hn R B hR hB mate hinv hQ hA l hl hlen L Lb rowBits).length ≤
      9 * canonicalDirectionalFrameBudget n R B hR hB L Lb rowBits
        (List.finRange (canonicalRouterStride n)) := by
  have h₂ := (inputs 2).frame_length_le L Lb rowBits
  have h₁ := (inputs 1).frame_length_le L Lb rowBits
  have h₀ := (inputs 0).frame_length_le L Lb rowBits
  simp only [canonicalMatchingFrame, List.length_append]
  omega

def canonicalMatchingProgram : Pr Empty ((canonicalRouterCommonT + 3) + 3) Q (prime + K) Unit :=
  .seq (.seq ((inputs 2).program Lb rowBits) ((inputs 1).program Lb rowBits)) ((inputs 0).program Lb rowBits)

def canonicalMatchingPrice : ℝ :=
  ((inputs 2).price L Lb rowBits + (inputs 1).price L Lb rowBits) + (inputs 0).price L Lb rowBits

theorem canonicalMatchingInput_exec
    (hn0 : 0 < n) (hnfit : n < 2 ^ L) (hBfit : B < 2 ^ Lb) (hnB : n ≤ B)
    (hrow : GrowingCounterData.Canonical rowBits) (hrowNe : rowBits ≠ [])
    (hrowValue : Counter.value rowBits = R)
    (rest : List (Fin (prime + K + 4)))
    (v : HS ((canonicalRouterCommonT + 3) + 3) Q (prime + K) Unit)
    (S : Stacks ((canonicalRouterCommonT + 3) + 3) (prime + K))
    (ready : FramedCoreReady canonicalDirectionalStream (R * 2 ^ n) B S)
    (hstream : S.R (framedCoreEmbed (canonicalRouterCommonT + 3) canonicalDirectionalStream) = l.flatten)
    (hinput : S.R (framedCoreAux (canonicalRouterCommonT + 3) 0) =
      canonicalMatchingFrame n hn R B hR hB mate hinv hQ hA l hl hlen L Lb rowBits ++ rest) :
    let E : Stacks ((canonicalRouterCommonT + 3) + 3) (prime + K) :=
      { S with R := delimitedCallAdvanced S.R (framedCoreAux (canonicalRouterCommonT + 3) 0) (framedCoreAux (canonicalRouterCommonT + 3) 2) (framedCoreEmbed (canonicalRouterCommonT + 3) canonicalDirectionalStream) (canonicalMatchingFrame n hn R B hR hB mate hinv hQ hA l hl hlen L Lb rowBits) rest (moveRecs (canonicalRouterMatchingPerm n hn mate hinv R B hR hB hQ hA l hl hlen) l).flatten }
    ∃ (v' : HS ((canonicalRouterCommonT + 3) + 3) Q (prime + K) Unit) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ canonicalMatchingPrice n hn R B hR hB mate hinv hQ hA l hl hlen L Lb rowBits ∧
      FramedCoreReady canonicalDirectionalStream (R * 2 ^ n) B E ∧
      Exec Empty.elim (canonicalMatchingProgram n hn R B hR hB mate hinv hQ hA l hl hlen Lb rowBits)
        (mk v S) steps (mk v' E) := by
  apply canonicalMatching_exec n hn R B hR hB mate hinv hQ hA inputs L Lb rowBits
    hn0 hnfit hBfit hnB hrow hrowNe hrowValue
    (canonicalMatchingInput_next_one n hn R B hR hB mate hinv hQ hA l hl hlen)
    (canonicalMatchingInput_next_zero n hn R B hR hB mate hinv hQ hA l hl hlen)
    rest v S ready hstream
  simpa only [canonicalMatchingFrame, List.append_assoc] using hinput

end
end IntegerMultBounds.MathlibTM2.Routing
