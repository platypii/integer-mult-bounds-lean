module

public import IntegerMultBounds.MathlibTM2.Routing.ReservoirMatchingLookup
public import IntegerMultBounds.MathlibTM2.Host.EmbedStream

/-! A fixed 33-tape scalar lookup on the actual middle field. Offset arithmetic,
physical-table lookup and both placement directions execute; metadata restores. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {Q A : ℕ} {P U : Type}

def middleLookupForward (j : Fin 14) : Fin 33 := j.castAdd 19

def middleLookupBackward (j : Fin 14) : Fin 33 :=
  if j = 11 then 14 else j.castAdd 19

def middleLookupTable : Fin 10 → Fin 33 := ![15, 16, 0, 17, 18, 19, 20, 21, 22, 23]

def middleLookupTranslate (inverse : Bool) : Fin 9 → Fin 33 :=
  if inverse then ![0, 26, 25, 27, 28, 29, 30, 31, 32]
  else ![0, 25, 26, 27, 28, 29, 30, 31, 32]

theorem middleLookupForward_injective : Function.Injective middleLookupForward := by decide +kernel

theorem middleLookupBackward_injective : Function.Injective middleLookupBackward := by decide +kernel

theorem middleLookupTable_injective : Function.Injective middleLookupTable := by decide +kernel

theorem middleLookupTranslate_injective (inverse : Bool) :
    Function.Injective (middleLookupTranslate inverse) := by cases inverse <;> decide +kernel

def reservoirMiddleLookupProgram : Pr P 33 Q A U :=
  .seq (binaryCoordinateTranslateInPlaceProgram (middleLookupTranslate false))
    (.seq (reservoirMatchingLookupProgram middleLookupForward middleLookupBackward middleLookupTable 24)
      (binaryCoordinateTranslateInPlaceProgram (middleLookupTranslate true)))

variable (n H : ℕ) (hfit : 9 * H ≤ n) (w : ℕ) (hw : w ≤ H) (k : Fin 3) (L : ℕ)

def middleLookupMetadata (inverse : Bool) : List (Fin (A + 4)) :=
  let rg := if inverse then middleLookupBackward else middleLookupForward
  delimitedScheduleInput
    (fun j => delimitedBankFrames separator
      (coordinateExchangeJobs rg L (reservoirExchangeSpecs n H hfit w hw k j)))
    (reservoirCoordinateOrder inverse)

def reservoirMiddleLookupBank (mate : Fin n → Fin n) (q : ℕ) (j : Fin 33) : List (Fin (A + 4)) :=
  if j = 0 then binSyms L q
  else if j = 11 then middleLookupMetadata n H hfit w hw k L false
  else if j = 14 then middleLookupMetadata n H hfit w hw k L true
  else if j = 21 then matchingEntryWords L (matchingTableEntries n (matchingMateCoordinate mate))
  else if j = 25 then binSyms L 0
  else if j = 26 then binSyms L w
  else []

/-- The fixed-bank local lookup has no execution premises and no supplied
local matching table: its only matching input is the physical table. -/
theorem reservoirMiddleLookup_exec (body : P → Pr P 33 Q A U)
    (hn : n < 2 ^ L) (mate : Fin n → Fin n) (hinv : Function.Involutive mate)
    (hfix : ∀ q ∈ routingReservoir n H hfit k, mate q = q) (q : Fin (n - 3 * w))
    (v : HS 33 Q A U) (S : Stacks 33 A)
    (hbank : S.R = reservoirMiddleLookupBank n H hfit w hw k L mate q.val) :
    ∃ (v' : HS 33 Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ n * (30 * L + 39) + 618 * L + 726 ∧
      Exec body reservoirMiddleLookupProgram (mk v S) steps
        (mk v' { S with R := Function.update S.R 0 (binSyms L (reservoirMiddleMatching n H hfit w hw k mate hinv hfix q).val) }) := by
  have hq : q.val < 2 ^ L := by have := q.isLt; omega
  let physical := middleCoordinate w (n - 3 * w) (reservoirMiddle_fit n H hfit w hw) q
  have hphysical : q.val - 0 + w = physical.val := by simp [physical, middleCoordinate, Nat.add_comm]
  obtain ⟨v₁, hu₁, he₁⟩ := binaryCoordinateTranslateInPlace_exec body
    (middleLookupTranslate false) (middleLookupTranslate_injective false)
    L q.val 0 w hq (Nat.zero_le _) (by rw [hphysical]; exact physical.isLt.trans hn) v S
    (by simp [middleLookupTranslate, hbank, reservoirMiddleLookupBank])
    (by simp [middleLookupTranslate, hbank, reservoirMiddleLookupBank])
    (by simp [middleLookupTranslate, hbank, reservoirMiddleLookupBank])
    (by intro j hj; rcases hj with rfl | rfl | rfl | rfl | rfl <;>
        simp [middleLookupTranslate, hbank, reservoirMiddleLookupBank])
  rw [hphysical] at he₁
  let G : Stacks 33 A := { S with R := Function.update S.R 0 (binSyms L physical.val) }
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := reservoirMatchingLookup_exec body n H hfit w hw k
    middleLookupForward middleLookupBackward middleLookupTable 24
    middleLookupForward_injective middleLookupBackward_injective middleLookupTable_injective
    (by intro j; fin_cases j <;> decide) rfl rfl L hn mate physical v₁ G
    (by simp [G, middleLookupForward])
    (by intro rg hr j hj
        rcases hr with rfl | rfl <;> fin_cases j <;>
          simp_all [G, reservoirMiddleLookupBank, middleLookupForward, middleLookupBackward])
    (by intro inverse; cases inverse <;>
        simp [G, hbank, reservoirMiddleLookupBank, middleLookupForward, middleLookupBackward, middleLookupMetadata])
    (by simp [G, hbank, reservoirMiddleLookupBank, middleLookupForward, middleLookupBackward])
    (by intro j hj; rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [G, hbank, reservoirMiddleLookupBank, middleLookupTable])
    (by simp [G, hbank, reservoirMiddleLookupBank, middleLookupTable])
    (by simp [G, hbank, reservoirMiddleLookupBank, middleLookupTable])
    (by simp [G, hbank, reservoirMiddleLookupBank])
  let r := placedSource (reservoirPlacement n H hfit w hw k) mate physical
  let J : Stacks 33 A := { S with R := Function.update S.R 0 (binSyms L r.val) }
  have hcollapse : { G with R := Function.update G.R (middleLookupForward 0) (binSyms L r.val) } = J := by
    simp [J, G, middleLookupForward]
  change Exec body (reservoirMatchingLookupProgram middleLookupForward middleLookupBackward middleLookupTable 24)
    (mk v₁ G) m₂ (mk v₂ { G with R := Function.update G.R (middleLookupForward 0) (binSyms L r.val) }) at he₂
  rw [hcollapse] at he₂
  have hr : w ≤ r.val := (reservoirMiddleMatching_lookup_bounds n H hfit w hw k mate hinv hfix q).1
  have hresult : r.val - w + 0 = (reservoirMiddleMatching n H hfit w hw k mate hinv hfix q).val := by
    simpa [r, placedSource, physical] using (reservoirMiddleMatching_value n H hfit w hw k mate hinv hfix q).symm
  obtain ⟨v₃, hu₃, he₃⟩ := binaryCoordinateTranslateInPlace_exec body
    (middleLookupTranslate true) (middleLookupTranslate_injective true)
    L r.val w 0 (r.isLt.trans hn) hr (by have := r.isLt; omega) v₂ J
    (by simp [J, middleLookupTranslate])
    (by simp [J, middleLookupTranslate, hbank, reservoirMiddleLookupBank])
    (by simp [J, middleLookupTranslate, hbank, reservoirMiddleLookupBank])
    (by intro j hj; rcases hj with rfl | rfl | rfl | rfl | rfl <;>
        simp [J, middleLookupTranslate, hbank, reservoirMiddleLookupBank])
  rw [hresult] at he₃
  have hfinal : { J with R := Function.update J.R (middleLookupTranslate true 0) (binSyms L (reservoirMiddleMatching n H hfit w hw k mate hinv hfix q).val) } =
      { S with R := Function.update S.R 0 (binSyms L (reservoirMiddleMatching n H hfit w hw k mate hinv hfix q).val) } := by
    simp [J, middleLookupTranslate]
  rw [hfinal] at he₃
  exact ⟨v₃, (28 * L + 28) + (m₂ + (28 * L + 28)), hu₃.trans (hu₂.trans hu₁),
    by omega, Exec.seq he₁ (Exec.seq he₂ he₃)⟩

/-- Place the closed scalar program in any larger bank. Off-bank tapes may
hold a growing generated table or the enumerator's live counter. -/
theorem reservoirMiddleLookup_embedded_exec {T : ℕ} (body : P → Pr P T Q A U)
    (rg : Fin 33 → Fin T) (hrg : Function.Injective rg)
    (hn : n < 2 ^ L) (mate : Fin n → Fin n) (hinv : Function.Involutive mate)
    (hfix : ∀ q ∈ routingReservoir n H hfit k, mate q = q) (q : Fin (n - 3 * w))
    (v : HS T Q A U) (S : Stacks T A)
    (hbank : ∀ j, S.R (rg j) = reservoirMiddleLookupBank n H hfit w hw k L mate q.val j) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ n * (30 * L + 39) + 618 * L + 726 ∧
      Exec body (embProg rg Empty.elim (reservoirMiddleLookupProgram (P := Empty))) (mk v S) steps
        (mk v' { S with R := Function.update S.R (rg 0) (binSyms L (reservoirMiddleMatching n H hfit w hw k mate hinv hfix q).val) }) := by
  let smallBody : Empty → Pr Empty 33 Q A U := Empty.elim
  obtain ⟨v₁, steps, hu₁, hm, he⟩ := reservoirMiddleLookup_exec n H hfit w hw k L
    smallBody hn mate hinv hfix q (embDn rg v) (embStk rg S) (by funext j; exact hbank j)
  obtain ⟨v₂, hu₂, he₂⟩ := exec_emb_stream rg hrg Empty.elim smallBody body
    (by intro f; exact f.elim) reservoirMiddleLookupProgram v S v₁ steps 0
    (binSyms L (reservoirMiddleMatching n H hfit w hw k mate hinv hfix q).val) he
  exact ⟨v₂, steps, hu₂.trans hu₁, hm, he₂⟩

end IntegerMultBounds.MathlibTM2.Routing
