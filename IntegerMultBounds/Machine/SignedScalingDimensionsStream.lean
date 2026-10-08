import IntegerMultBounds.Machine.SignedScalingDimensions
import IntegerMultBounds.Machine.SignedScalingStream

/-! One physical synthesis of all signed-scaling descriptors followed by a
literal counted stream of equal-size fibers. Only canonical Q/B/n words, the
explicit inherited fixed sentinels, and declared scratch are inputs. Both nested
placements wire the same physical tapes; no descriptor or payload transfer is
assumed between setup and the reusable stream. -/
namespace IntegerMultBounds.Machine.SignedScalingDimensionsStream

open SignedScalingPrepared (Setup prepared prepared_valid)
open SignedScalingDimensions (Scratch generated metadata)
open CountedCopyReuse (empty binary)
open ScalingPreparedExecution (SynthesisStates)

abbrev TapeCount (a d : ℕ) := SignedScalingDimensions.TapeCount a d+2
abbrev PreparationStates (a d : ℕ) := 160+(SynthesisStates a+SynthesisStates d)
abbrev States (a d : ℕ) (negative : Bool) := PreparationStates a d+SignedScalingStream.States a d negative

def innerPlacement (a d : ℕ) : Fin (SignedScalingStream.TapeCount a d+2) ≃ Fin (SignedScalingPrepared.TapeCount a d+2) :=
  FamilyPlacement.withFrame (SignedScalingPrepared.executionPlacement a d)

def outerPlacement (a d : ℕ) : Fin ((SignedScalingPrepared.TapeCount a d+2)+9) ≃ Fin (TapeCount a d) :=
  FamilyPlacement.withFrame (SignedScalingDimensions.executionPlacement a d)

private def spares : Tapes 2 0 := ScalingPreparedExecution.spare.append ScalingPreparedExecution.spare

private theorem placed_hoare {s u t q : ℕ} {M : Program s q 0} {v w : Tapes s 0} {cost : ℕ}
    (h : HoareTime M (fun x => x = v) (fun x => x = w) cost) (e : Fin (s+u) ≃ Fin t) (frame : Tapes u 0) :
    HoareTime (Placement.placed M e) (fun x => x = Placement.combine e v frame)
      (fun x => x = Placement.combine e w frame) cost := by
  apply (Placement.hoare_at h e (Placement.combine e v frame) (Placement.active_combine _ _ _)).consequence
    (fun _ h => h) _ le_rfl
  rintro x ⟨small,hsmall,rfl⟩
  subst small
  simp only [Placement.replace,Placement.extra_combine]

def input {a d : ℕ} (negative : Bool) (A : Setup a) (D : Setup d) (S : Scratch) (Q n : ℕ) (ns : List Bool)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (r : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : ℕ → ℕ → List (Fin 4)) : Tapes (TapeCount a d) 0 :=
  (SignedScalingDimensions.input negative A D S Q
    (putWord source p (SignedScalingStream.fibers Q n payload).flatten) p middle r signMiddle t dest q (fun _ => [])).append
    (CountedLoopReuse.controls empty (binary ns) 1 1)

/-- Full stream boundary with generated metadata and both synthesis spares kept. -/
def state {a d : ℕ} (ha : 0 < a) (hd : 0 < d) (negative : Bool) (A : Setup a) (D : Setup d) (S : Scratch)
    (Q B n : ℕ) (ns : List Bool) (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (r : ℤ)
    (signMiddle : ℤ → Fin 4) (t : ℤ) (dest : ℤ → Fin 4) (q : ℤ) (payload : ℕ → ℕ → List (Fin 4)) (i : ℕ) :
    Tapes (TapeCount a d) 0 :=
  Placement.combine (outerPlacement a d)
    (Placement.combine (innerPlacement a d)
      (CountedLoopReuse.bank
        (SignedScalingStream.state ha hd negative (prepared ha A Q B) (prepared hd D Q B) (generated S Q B)
          Q B n source p middle r signMiddle t dest q payload i) empty (binary ns) 1 1) spares)
    (metadata Q B A.blockBits A.countBits)

/-- Both descriptor bootstraps run once, while the outer controls are framed. -/
def prepareProgram {a d : ℕ} (ha : 0 < a) (hd : 0 < d) : Program (TapeCount a d) (PreparationStates a d) 0 :=
  extend (seq (SignedScalingDimensions.bootstrapProgram a d)
    (Placement.placed (SignedScalingPrepared.allPrepareProgram ha hd) (SignedScalingDimensions.executionPlacement a d))) 2

def program {a d : ℕ} (ha : 0 < a) (hd : 0 < d) (negative : Bool) : Program (TapeCount a d) (States a d negative) 0 :=
  seq (prepareProgram ha hd)
    (Placement.placed (Placement.placed (SignedScalingStream.program ha hd negative) (innerPlacement a d)) (outerPlacement a d))

/-- Every derived descriptor is physically produced before the first fiber. -/
theorem prepare_hoare {Q a d B : ℕ} (hQ : 0 < Q) (ha : 0 < a) (hd : 0 < d) (hB : 0 < B)
    (negative : Bool) (A : Setup a) (D : Setup d) (S : Scratch) (hA : A.Valid Q B) (hD : D.Valid Q B)
    (n : ℕ) (ns : List Bool) (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (r : ℤ)
    (signMiddle : ℤ → Fin 4) (t : ℤ) (dest : ℤ → Fin 4) (q : ℤ) (payload : ℕ → ℕ → List (Fin 4)) :
    HoareTime (prepareProgram ha hd)
      (fun v => v = input negative A D S Q n ns source p middle r signMiddle t dest q payload)
      (fun v => v = state ha hd negative A D S Q B n ns source p middle r signMiddle t dest q payload 0)
      (356*(Q*B)+225) := by
  let src := putWord source p (SignedScalingStream.fibers Q n payload).flatten
  have hb := SignedScalingDimensions.bootstrap_hoare hQ hB negative A D S hA src p middle r signMiddle t dest q (fun _ => [])
  have hp := placed_hoare (SignedScalingPrepared.allPrepare_hoare ha hd hB negative A D (generated S Q B) hA hD
    src p middle r signMiddle t dest q (fun _ => [])) (SignedScalingDimensions.executionPlacement a d)
    (metadata Q B A.blockBits A.countBits)
  have hh := FamilyPlacement.extend_hoare (hb.seq hp) (CountedLoopReuse.controls empty (binary ns) 1 1)
  apply hh.consequence (fun _ h => h) _ (by omega)
  rintro v rfl
  unfold state innerPlacement outerPlacement CountedLoopReuse.bank
  rw [FamilyPlacement.combine_withFrame,FamilyPlacement.combine_withFrame]
  rw [← SignedScalingStream.initial_state ha hd negative (prepared ha A Q B) (prepared hd D Q B) (generated S Q B)]
  rfl

/-- A single synthesis followed by n actual signed fiber executions. Setup is
charged even when n is zero; all generated metadata and scratch banks survive. -/
theorem scaling_hoare {Q a d B n : ℕ} (hQ : 0 < Q) (ha : 0 < a) (hd : 0 < d)
    (hcopA : a.Coprime Q) (hcopD : d.Coprime Q) (hB : 0 < B) (negative : Bool)
    (A : Setup a) (D : Setup d) (S : Scratch) (hA : A.Valid Q B) (hD : D.Valid Q B)
    (hS : negative = true → ∀ z, S.origin ≤ z → z < S.origin+(((Q-1)*B : ℕ) : ℤ) → S.tape z = blank)
    (ns : List Bool) (hn : Counter.value ns = n) (cn : GrowingCounterData.Canonical ns)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (r : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : ℕ → ℕ → List (Fin 4)) (hwidth : ∀ j y, (payload j y).length = B)
    (hblank : ∀ z, r ≤ z → z < r+((Q*B : ℕ) : ℤ) → middle z = blank)
    (hsblank : negative = true → ∀ z, t ≤ z → z < t+((Q*B : ℕ) : ℤ) → signMiddle z = blank) :
    HoareTime (program ha hd negative)
      (fun v => v = input negative A D S Q n ns source p middle r signMiddle t dest q payload)
      (fun v => v = state ha hd negative A D S Q B n ns source p middle r signMiddle t dest q payload n)
      ((1381+120*(a+d))*(SignedScalingStream.fibers Q n payload).flatten.length+356*(Q*B)+249) := by
  have he := placed_hoare (placed_hoare
    (SignedScalingStream.scaling_hoare_linear hQ ha hd hcopA hcopD hB negative
      (prepared ha A Q B) (prepared hd D Q B) (generated S Q B) (prepared_valid hQ ha hcopA A hA)
      (prepared_valid hQ hd hcopD D hD) (fun h => SignedScalingDimensions.generated_valid S Q B (hS h)) ns hn cn
      source p middle r signMiddle t dest q payload hwidth hblank hsblank)
    (innerPlacement a d) spares) (outerPlacement a d) (metadata Q B A.blockBits A.countBits)
  have hp := prepare_hoare hQ ha hd hB negative A D S hA hD n ns source p middle r signMiddle t dest q payload
  exact (hp.seq he).consequence (fun _ h => h) (fun _ h => h) (by omega)

/-- With at least one fiber, once-only setup is absorbed by total payload volume. -/
theorem scaling_hoare_linear {Q a d B n : ℕ} (hQ : 0 < Q) (ha : 0 < a) (hd : 0 < d)
    (hcopA : a.Coprime Q) (hcopD : d.Coprime Q) (hB : 0 < B) (hnpos : 0 < n) (negative : Bool)
    (A : Setup a) (D : Setup d) (S : Scratch) (hA : A.Valid Q B) (hD : D.Valid Q B)
    (hS : negative = true → ∀ z, S.origin ≤ z → z < S.origin+(((Q-1)*B : ℕ) : ℤ) → S.tape z = blank)
    (ns : List Bool) (hn : Counter.value ns = n) (cn : GrowingCounterData.Canonical ns)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (r : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : ℕ → ℕ → List (Fin 4)) (hwidth : ∀ j y, (payload j y).length = B)
    (hblank : ∀ z, r ≤ z → z < r+((Q*B : ℕ) : ℤ) → middle z = blank)
    (hsblank : negative = true → ∀ z, t ≤ z → z < t+((Q*B : ℕ) : ℤ) → signMiddle z = blank) :
    HoareTime (program ha hd negative)
      (fun v => v = input negative A D S Q n ns source p middle r signMiddle t dest q payload)
      (fun v => v = state ha hd negative A D S Q B n ns source p middle r signMiddle t dest q payload n)
      ((1737+120*(a+d))*(SignedScalingStream.fibers Q n payload).flatten.length+249) := by
  apply (scaling_hoare hQ ha hd hcopA hcopD hB negative A D S hA hD hS ns hn cn
    source p middle r signMiddle t dest q payload hwidth hblank hsblank).consequence (fun _ h => h) (fun _ h => h)
  rw [ScalingStream.source_length Q B n payload hwidth]
  have hv : Q*B ≤ n*(Q*B) := by
    calc Q*B = 1*(Q*B) := by omega
         _ ≤ n*(Q*B) := Nat.mul_le_mul_right _ (by omega : 1 ≤ n)
  nlinarith

def destinationSlot (a d : ℕ) (negative : Bool) : Fin (TapeCount a d) :=
  outerPlacement a d (Fin.castAdd 9 (innerPlacement a d
    (Fin.castAdd 2 (Fin.castAdd 2 (SignedScalingSign.destinationSlot a d negative)))))

/-- Final destination is the concatenation of exact signed affine fiber images,
and its head has advanced by the complete physically processed volume. -/
theorem state_destination {a d : ℕ} (ha : 0 < a) (hd : 0 < d) (negative : Bool)
    (A : Setup a) (D : Setup d) (S : Scratch) (Q B n : ℕ) (ns : List Bool)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (r : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : ℕ → ℕ → List (Fin 4)) (i : ℕ) :
    let v := state ha hd negative A D S Q B n ns source p middle r signMiddle t dest q payload i
    v.tape (destinationSlot a d negative) = putWord dest q (SignedScalingStream.outputPrefix ha Q d negative i payload) ∧
      v.head (destinationSlot a d negative) = q+((i*(Q*B) : ℕ) : ℤ) := by
  dsimp only
  simp only [state,destinationSlot,Placement.combine_tape_active,Placement.combine_head_active,
    CountedLoopReuse.bank,Tapes.append,Fin.addCases_left]
  exact SignedScalingStream.state_destination ha hd negative (prepared ha A Q B) (prepared hd D Q B) (generated S Q B)
    Q B n source p middle r signMiddle t dest q payload i

/-- Generated helper lengths and the bootstrap's fixed one remain explicit. -/
theorem state_metadata {a d : ℕ} (ha : 0 < a) (hd : 0 < d) (negative : Bool)
    (A : Setup a) (D : Setup d) (S : Scratch) (Q B n : ℕ) (ns : List Bool)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (r : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : ℕ → ℕ → List (Fin 4)) (i : ℕ) :
    Placement.extra (outerPlacement a d)
      (state ha hd negative A D S Q B n ns source p middle r signMiddle t dest q payload i) =
      metadata Q B A.blockBits A.countBits := Placement.extra_combine _ _ _

/-- Both coefficient-synthesis spare tapes are physically retained. -/
theorem state_spares {a d : ℕ} (ha : 0 < a) (hd : 0 < d) (negative : Bool)
    (A : Setup a) (D : Setup d) (S : Scratch) (Q B n : ℕ) (ns : List Bool)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (r : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : ℕ → ℕ → List (Fin 4)) (i : ℕ) :
    Placement.extra (innerPlacement a d) (Placement.active (outerPlacement a d)
      (state ha hd negative A D S Q B n ns source p middle r signMiddle t dest q payload i)) =
      ScalingPreparedExecution.spare.append ScalingPreparedExecution.spare := by
  simp only [state,Placement.active_combine,Placement.extra_combine,spares]

theorem tapeCount_eq (a d : ℕ) : TapeCount a d = 51+4*(a+d) := by
  dsimp only [TapeCount]
  rw [SignedScalingDimensions.tapeCount_eq]
  omega

theorem stateCount_eq (a d : ℕ) (negative : Bool) :
    States a d negative = 117*(a+d)+(if negative then 803 else 471) := by
  dsimp only [States,PreparationStates]
  rw [SignedScalingStream.stateCount_eq]
  dsimp only [SynthesisStates]
  cases negative <;> simp <;> omega

end IntegerMultBounds.Machine.SignedScalingDimensionsStream
