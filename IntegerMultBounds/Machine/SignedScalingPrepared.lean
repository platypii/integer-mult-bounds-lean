import IntegerMultBounds.Machine.SignedScalingSign
import IntegerMultBounds.Machine.ScalingPreparedExecution
import IntegerMultBounds.Machine.FamilyPlacement

/-! Synthesize both coefficient-piece descriptor families before signed scaling.
Generated descriptors are shared through static tape-bank wiring. Only canonical
Q/B and, for the negative branch, sign-tail descriptors remain supplied. -/
namespace IntegerMultBounds.Machine.SignedScalingPrepared

open CountedCopyReuse (empty binary)
open SignedScalingExecution (Controls setTape)
open SignedScalingSign (SignControls)
open ScalingPreparedExecution (SynthesisTapes FrameTapes SynthesisStates)

/-- Per-coefficient state without any supplied piece-length descriptors. -/
structure Setup (c : ℕ) where
  background : Fin c → ℤ → Fin 4
  origins : Fin c → ℤ
  blockBits : List Bool
  countBits : List Bool
  modulus : Tapes c 0
  current : Tapes c 0

structure Setup.Valid {c : ℕ} (C : Setup c) (Q B : ℕ) : Prop where
  block_value : Counter.value C.blockBits = B
  count_value : Counter.value C.countBits = Q
  block_canonical : GrowingCounterData.Canonical C.blockBits
  count_canonical : GrowingCounterData.Canonical C.countBits
  scratch_blank : ∀ j z, C.origins j ≤ z → z < C.origins j+
    ((ScalingSplit.offset Q c B (j.val+1)-ScalingSplit.offset Q c B j.val : ℕ) : ℤ) → C.background j z = blank

/-- The canonical descriptors and residue cells physically produced by synthesis. -/
def prepared {c : ℕ} (hc : 0 < c) (C : Setup c) (Q B : ℕ) : Controls c where
  background := C.background
  origins := C.origins
  descriptors := ScalingDescriptorData.descriptors hc Q B Q
  blockBits := C.blockBits
  countBits := C.countBits
  modulus := OneHot.bank C.modulus (OneHot.residue hc Q)
  current := OneHot.bank C.current (OneHot.residue hc Q)

theorem prepared_valid {Q c B : ℕ} (hQ : 0 < Q) (hc : 0 < c) (hcop : c.Coprime Q)
    (C : Setup c) (hC : C.Valid Q B) : (prepared hc C Q B).Valid Q B := by
  refine ⟨hC.block_value,hC.count_value,hC.block_canonical,hC.count_canonical,?_,
    ScalingDescriptorData.descriptors_canonical hc Q B Q,hC.scratch_blank⟩
  intro j
  change Counter.value (ScalingDescriptorData.descriptors hc Q B Q j) = _
  rw [ScalingDescriptorData.complete_value hQ hc hcop]
  simp only [ScalingSplit.offset,Nat.sub_mul]

private def descriptorBank {c : ℕ} (ds : Fin c → List Bool) : Tapes c 0 :=
  ⟨fun _ => 1,fun j => binary (ds j)⟩

private def localReady {c : ℕ} (hc : 0 < c) (Q B : ℕ) (C : Setup c)
    (a : Tapes 4 0) (left : Tapes 2 0) : Tapes (ScalingExecution.TapeCount c) 0 :=
  ScalingExecution.join a ⟨C.origins,C.background⟩
    (descriptorBank (ScalingDescriptorData.descriptors hc Q B Q))
    (left.append (CountedLoopReuse.controls empty (binary C.blockBits) 1 1))
    (OneHot.bank C.modulus (OneHot.residue hc Q)) (OneHot.bank C.current (OneHot.residue hc Q))
    (CountedLoopReuse.controls empty (binary C.countBits) 1 1)

private def localInput {c : ℕ} (C : Setup c) (a : Tapes 4 0) (left : Tapes 2 0) :
    Tapes (ScalingPreparedExecution.TapeCount c) 0 :=
  (ScalingDescriptors.initial C.blockBits C.countBits C.modulus C.current).append
    ((a.append (⟨C.origins,C.background⟩ : Tapes c 0)).append left)

private def prepareProgram {c : ℕ} (hc : 0 < c) :
    Program (ScalingPreparedExecution.TapeCount c) (SynthesisStates c) 0 :=
  extend (ScalingDescriptors.program hc) (FrameTapes c)

private theorem prepare_hoare {Q c B : ℕ} (hc : 0 < c) (hB : 0 < B) (C : Setup c) (hC : C.Valid Q B)
    (a : Tapes 4 0) (left : Tapes 2 0) :
    HoareTime (prepareProgram hc) (fun v => v = localInput C a left)
      (fun v => v = Placement.combine (ScalingPreparedExecution.executionPlacement c)
        (localReady hc Q B C a left) ScalingPreparedExecution.spare) (70*(Q*B)+51) := by
  have h := (ScalingDescriptors.synthesize_hoare_linear hc Q B hB C.blockBits C.countBits
    hC.block_value hC.count_value hC.block_canonical hC.count_canonical C.modulus C.current).extend
    ((a.append (⟨C.origins,C.background⟩ : Tapes c 0)).append left)
  apply h.consequence _ _ le_rfl
  · rintro v rfl; exact ⟨_,rfl,rfl⟩
  · rintro v ⟨w,rfl,rfl⟩
    exact ScalingPreparedExecution.regroup a ⟨C.origins,C.background⟩
      (descriptorBank (ScalingDescriptorData.descriptors hc Q B Q)) left
      (CountedLoopReuse.controls empty (binary C.blockBits) 1 1)
      (OneHot.bank C.modulus (OneHot.residue hc Q)) (OneHot.bank C.current (OneHot.residue hc Q))
      (CountedLoopReuse.controls empty (binary C.countBits) 1 1) ScalingPreparedExecution.spare

private def dataControl (f : ℤ → Fin 4) (p : ℤ) : Tapes 4 0 :=
  CountedCopyReuse.bank f (fun _ => blank) empty (fun _ => blank) p 0 1 0

private theorem copy_controls (source dest : ℤ → Fin 4) (p q : ℤ) (bs : List Bool) :
    (CountedLoopReuse.controls source dest p q).append (CountedLoopReuse.controls empty (binary bs) 1 1) =
      CountedCopyReuse.bank source dest empty (binary bs) p q 1 1 := by
  unfold CountedLoopReuse.controls CountedCopyReuse.bank Tapes.append
  congr 1 <;> funext i <;> fin_cases i <;> rfl

private theorem forward_aux {c : ℕ} (f : ℤ → Fin 4) (p : ℤ) (bs ns : List Bool) (m k : Tapes c 0) :
    ScalingExecutionReuse.auxiliary f p bs ns m k =
      (((CountedCopyReuse.bank empty f empty (binary bs) 0 p 1 1).append m).append k).append
        (CountedLoopReuse.controls empty (binary ns) 1 1) := rfl

private theorem inverse_aux {c : ℕ} (f : ℤ → Fin 4) (p : ℤ) (bs ns : List Bool) (m k : Tapes c 0) :
    ScalingInverseExecution.auxiliary f p bs ns m k =
      (((CountedCopyReuse.bank f empty empty (binary bs) p 0 1 1).append m).append k).append
        (CountedLoopReuse.controls empty (binary ns) 1 1) := rfl

private theorem ready_forward {a : ℕ} (ha : 0 < a) (Q B : ℕ) (A : Setup a)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (r : ℤ) (payload : ℕ → List (Fin 4)) :
    localReady ha Q B A (dataControl (putWord source p (ScalingExecution.inputWord Q payload)) p)
      (CountedLoopReuse.controls empty middle 0 r) =
      SignedScalingExecution.forwardInput (prepared ha A Q B) Q source p middle r payload := by
  unfold localReady
  rw [copy_controls]
  unfold SignedScalingExecution.forwardInput ScalingExecutionReuse.input
  rw [forward_aux]
  rfl

private theorem setTape_append_right {l r : ℕ} (v : Tapes l 0) (w : Tapes r 0) (i : Fin r)
    (f : ℤ → Fin 4) (p : ℤ) :
    setTape (v.append w) (Fin.natAdd l i) f p = v.append (setTape w i f p) := by
  unfold setTape Tapes.append
  congr 1 <;> funext j <;> induction j using Fin.addCases <;> simp [Function.update_apply,Fin.ext_iff]
  all_goals rename_i k; intro h; have hk := k.isLt; omega

private theorem copy_source_set (source dest newSource : ℤ → Fin 4) (p q newHead : ℤ) (bs : List Bool) :
    setTape (CountedCopyReuse.bank source dest empty (binary bs) p q 1 1) 0 newSource newHead =
      CountedCopyReuse.bank newSource dest empty (binary bs) newHead q 1 1 := by
  unfold setTape CountedCopyReuse.bank
  congr 1 <;> funext i <;> fin_cases i <;> rfl

private theorem ready_inverse {d : ℕ} (hd : 0 < d) (Q B : ℕ) (D : Setup d)
    (middle : ℤ → Fin 4) (r : ℤ) (dest : ℤ → Fin 4) (q : ℤ) (payload : ℕ → List (Fin 4)) :
    localReady hd Q B D (dataControl dest q) (CountedLoopReuse.controls empty empty 0 0) =
      SignedScalingExecution.stripSource
        (SignedScalingExecution.inverseInput (prepared hd D Q B) Q middle r dest q payload) := by
  unfold localReady
  rw [copy_controls]
  unfold SignedScalingExecution.stripSource SignedScalingExecution.inverseInput ScalingInverseExecution.input
    SignedScalingExecution.inverseSourceSlot
  rw [setTape_append_right,inverse_aux]
  simp only [SignedScalingExecution.setTape_append_left,copy_source_set]
  rfl


abbrev TapeCount (a d : ℕ) := ((ScalingPreparedExecution.TapeCount a+ScalingPreparedExecution.TapeCount d+5)+8)+5

/-- Both descriptor families are statically shared with the existing consumer;
the only extra frame consists of the two synthesis spare tapes. -/
def executionPlacement (a d : ℕ) : Fin (SignedScalingSign.TapeCount a d+2) ≃ Fin (TapeCount a d) :=
  FamilyPlacement.withFrame (FamilyPlacement.withFrame (FamilyPlacement.withFrame
    (FamilyPlacement.pair (ScalingPreparedExecution.executionPlacement a)
      (ScalingPreparedExecution.executionPlacement d))))

private def firstControl (Q : ℕ) (source : ℤ → Fin 4) (p : ℤ) (payload : ℕ → List (Fin 4)) : Tapes 4 0 :=
  dataControl (putWord source p (ScalingExecution.inputWord Q payload)) p

private def lastControl (negative : Bool) (signMiddle : ℤ → Fin 4) (t : ℤ) (dest : ℤ → Fin 4) (q : ℤ) : Tapes 4 0 :=
  if negative then dataControl signMiddle t else dataControl dest q

private def signSide (negative : Bool) (S : SignControls) (bs : List Bool) (dest : ℤ → Fin 4) (q : ℤ) : Tapes 8 0 :=
  if negative then SignedScalingSign.signBank S bs dest q else SignedScalingSign.signBank S bs empty 0

/-- No generated piece descriptor occurs in this initial physical bank. The
fixed split-clock sentinel is explicit; synthesis starts its counters blank. -/
def input {a d : ℕ} (negative : Bool) (A : Setup a) (D : Setup d) (S : SignControls) (Q : ℕ)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (r : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : ℕ → List (Fin 4)) : Tapes (TapeCount a d) 0 :=
  ((((localInput A (firstControl Q source p payload) (CountedLoopReuse.controls empty middle 0 r)).append
    (localInput D (lastControl negative signMiddle t dest q) (CountedLoopReuse.controls empty empty 0 0))).append
    (CountedSpanSeek.bank empty 0 A.blockBits A.countBits)).append
    (signSide negative S A.blockBits dest q)).append (CountedSpanSeek.bank empty 0 A.blockBits A.countBits)

private theorem handoff {a d : ℕ} (ha : 0 < a) (hd : 0 < d) (negative : Bool)
    (A : Setup a) (D : Setup d) (S : SignControls) (Q B : ℕ)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (r : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : ℕ → List (Fin 4)) :
    ((((Placement.combine (ScalingPreparedExecution.executionPlacement a)
      (localReady ha Q B A (firstControl Q source p payload) (CountedLoopReuse.controls empty middle 0 r))
      ScalingPreparedExecution.spare).append
      (Placement.combine (ScalingPreparedExecution.executionPlacement d)
        (localReady hd Q B D (lastControl negative signMiddle t dest q) (CountedLoopReuse.controls empty empty 0 0))
        ScalingPreparedExecution.spare)).append (CountedSpanSeek.bank empty 0 A.blockBits A.countBits)).append
      (signSide negative S A.blockBits dest q)).append (CountedSpanSeek.bank empty 0 A.blockBits A.countBits) =
    Placement.combine (executionPlacement a d)
      (SignedScalingSign.input ha negative (prepared ha A Q B) (prepared hd D Q B) S Q
        source p middle r signMiddle t dest q payload)
      (ScalingPreparedExecution.spare.append ScalingPreparedExecution.spare) := by
  unfold executionPlacement
  cases negative
  · simp only [SignedScalingSign.input,Bool.false_eq_true,ite_false,SignedScalingSign.positiveInput,
      SignedScalingExecution.unsignedInput,prepared,signSide,lastControl]
    rw [FamilyPlacement.combine_withFrame,FamilyPlacement.combine_withFrame,FamilyPlacement.combine_withFrame,
      FamilyPlacement.combine_pair]
    rw [show firstControl Q source p payload = dataControl (putWord source p (ScalingExecution.inputWord Q payload)) p from rfl,
      ready_forward,ready_inverse hd Q B D middle r dest q (SignedScalingExecution.numeratorPayload ha Q payload)]
    rfl
  · simp only [SignedScalingSign.input,ite_true,SignedScalingSign.negativeInput,
      SignedScalingExecution.unsignedInput,prepared,signSide,lastControl]
    rw [FamilyPlacement.combine_withFrame,FamilyPlacement.combine_withFrame,FamilyPlacement.combine_withFrame,
      FamilyPlacement.combine_pair]
    rw [show firstControl Q source p payload = dataControl (putWord source p (ScalingExecution.inputWord Q payload)) p from rfl,
      ready_forward,ready_inverse hd Q B D middle r signMiddle t (SignedScalingExecution.numeratorPayload ha Q payload)]
    rfl

private def allPrepareProgram {a d : ℕ} (ha : 0 < a) (hd : 0 < d) :
    Program (TapeCount a d) (SynthesisStates a+SynthesisStates d) 0 :=
  extend (extend (extend (FamilyPlacement.sequence (prepareProgram ha) (prepareProgram hd)) 5) 8) 5

private theorem allPrepare_hoare {Q a d B : ℕ} (ha : 0 < a) (hd : 0 < d) (hB : 0 < B)
    (negative : Bool) (A : Setup a) (D : Setup d) (S : SignControls) (hA : A.Valid Q B) (hD : D.Valid Q B)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (r : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : ℕ → List (Fin 4)) :
    HoareTime (allPrepareProgram ha hd)
      (fun v => v = input negative A D S Q source p middle r signMiddle t dest q payload)
      (fun v => v = Placement.combine (executionPlacement a d)
        (SignedScalingSign.input ha negative (prepared ha A Q B) (prepared hd D Q B) S Q
          source p middle r signMiddle t dest q payload)
        (ScalingPreparedExecution.spare.append ScalingPreparedExecution.spare)) (140*(Q*B)+103) := by
  have hp := FamilyPlacement.sequence_hoare
    (prepare_hoare ha hB A hA (firstControl Q source p payload) (CountedLoopReuse.controls empty middle 0 r))
    (prepare_hoare hd hB D hD (lastControl negative signMiddle t dest q) (CountedLoopReuse.controls empty empty 0 0))
  have h := FamilyPlacement.extend_hoare (FamilyPlacement.extend_hoare (FamilyPlacement.extend_hoare hp
    (CountedSpanSeek.bank empty 0 A.blockBits A.countBits)) (signSide negative S A.blockBits dest q))
    (CountedSpanSeek.bank empty 0 A.blockBits A.countBits)
  rw [handoff] at h
  exact h.consequence (fun _ h => h) (fun _ h => h) (by omega)

/-- Generated descriptor banks are retained for subsequent fibers. -/
def output {a d : ℕ} (ha : 0 < a) (hd : 0 < d) (negative : Bool) (A : Setup a) (D : Setup d)
    (S : SignControls) (Q B : ℕ) (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (r : ℤ)
    (signMiddle : ℤ → Fin 4) (t : ℤ) (dest : ℤ → Fin 4) (q : ℤ) (payload : ℕ → List (Fin 4)) : Tapes (TapeCount a d) 0 :=
  Placement.combine (executionPlacement a d)
    (SignedScalingSign.output ha hd negative (prepared ha A Q B) (prepared hd D Q B) S Q B
      source p middle r signMiddle t dest q payload)
    (ScalingPreparedExecution.spare.append ScalingPreparedExecution.spare)

def program {a d : ℕ} (ha : 0 < a) (hd : 0 < d) (negative : Bool) :
    Program (TapeCount a d) (SynthesisStates a+SynthesisStates d+SignedScalingSign.states a d negative) 0 :=
  seq (allPrepareProgram ha hd) (Placement.placed (SignedScalingSign.program ha hd negative) (executionPlacement a d))

/-- Both piece descriptor families are physically synthesized before the full
signed rational payload transform. Only Q/B and negative-tail descriptors are
supplied; no piece count or canonicality hypothesis is left to the caller. -/
theorem scaling_hoare {Q a d B : ℕ} (hQ : 0 < Q) (ha : 0 < a) (hd : 0 < d)
    (hcopA : a.Coprime Q) (hcopD : d.Coprime Q) (hB : 0 < B) (negative : Bool)
    (A : Setup a) (D : Setup d) (S : SignControls) (hA : A.Valid Q B) (hD : D.Valid Q B)
    (hS : negative = true → S.Valid Q B)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (r : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : ℕ → List (Fin 4)) (hwidth : ∀ y, (payload y).length = B)
    (hblank : ∀ z, r ≤ z → z < r+((Q*B : ℕ) : ℤ) → middle z = blank)
    (hsblank : negative = true → ∀ z, t ≤ z → z < t+((Q*B : ℕ) : ℤ) → signMiddle z = blank) :
    HoareTime (program ha hd negative)
      (fun v => v = input negative A D S Q source p middle r signMiddle t dest q payload)
      (fun v => v = output ha hd negative A D S Q B source p middle r signMiddle t dest q payload)
      (SignedScalingSign.bound Q B a d negative+140*(Q*B)+104) := by
  let before := SignedScalingSign.input ha negative (prepared ha A Q B) (prepared hd D Q B) S Q
    source p middle r signMiddle t dest q payload
  let spares := ScalingPreparedExecution.spare.append ScalingPreparedExecution.spare
  have he := Placement.hoare_at
    (SignedScalingSign.scaling_hoare hQ ha hd hcopA hcopD hB negative
      (prepared ha A Q B) (prepared hd D Q B) S (prepared_valid hQ ha hcopA A hA) (prepared_valid hQ hd hcopD D hD) hS
      source p middle r signMiddle t dest q payload hwidth hblank hsblank)
    (executionPlacement a d) (Placement.combine (executionPlacement a d) before spares) (Placement.active_combine _ _ _)
  have he' : HoareTime (Placement.placed (SignedScalingSign.program ha hd negative) (executionPlacement a d))
      (fun v => v = Placement.combine (executionPlacement a d) before spares)
      (fun v => v = output ha hd negative A D S Q B source p middle r signMiddle t dest q payload)
      (SignedScalingSign.bound Q B a d negative) := by
    apply he.consequence (fun _ h => h) _ le_rfl
    rintro v ⟨w,rfl,rfl⟩
    simp only [Placement.replace,Placement.extra_combine]
    rfl
  have h := (allPrepare_hoare ha hd hB negative A D S hA hD source p middle r signMiddle t dest q payload).seq he'
  exact h.consequence (fun _ h => h) (fun _ h => h) (by omega)


/-- Canonical dimensions absorb every fixed coefficient/setup term into the
payload-volume coefficient. -/
theorem linear_bound (Q B a d : ℕ) (negative : Bool) (hQ : 0 < Q) (hB : 0 < B) :
    SignedScalingSign.bound Q B a d negative+140*(Q*B)+104 ≤ (1612+120*(a+d))*(Q*B) := by
  have hv : 1 ≤ Q*B := by nlinarith
  have hm := Nat.mul_le_mul_left (120*(a+d)+620) hv
  unfold SignedScalingSign.bound
  split_ifs <;> nlinarith

theorem scaling_hoare_linear {Q a d B : ℕ} (hQ : 0 < Q) (ha : 0 < a) (hd : 0 < d)
    (hcopA : a.Coprime Q) (hcopD : d.Coprime Q) (hB : 0 < B) (negative : Bool)
    (A : Setup a) (D : Setup d) (S : SignControls) (hA : A.Valid Q B) (hD : D.Valid Q B)
    (hS : negative = true → S.Valid Q B)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (r : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : ℕ → List (Fin 4)) (hwidth : ∀ y, (payload y).length = B)
    (hblank : ∀ z, r ≤ z → z < r+((Q*B : ℕ) : ℤ) → middle z = blank)
    (hsblank : negative = true → ∀ z, t ≤ z → z < t+((Q*B : ℕ) : ℤ) → signMiddle z = blank) :
    HoareTime (program ha hd negative)
      (fun v => v = input negative A D S Q source p middle r signMiddle t dest q payload)
      (fun v => v = output ha hd negative A D S Q B source p middle r signMiddle t dest q payload)
      ((1612+120*(a+d))*(Q*B)) :=
  (scaling_hoare hQ ha hd hcopA hcopD hB negative A D S hA hD hS source p middle r signMiddle t dest q
    payload hwidth hblank hsblank).consequence (fun _ h => h) (fun _ h => h) (linear_bound Q B a d negative hQ hB)

def destinationSlot (a d : ℕ) (negative : Bool) : Fin (TapeCount a d) :=
  executionPlacement a d (Fin.castAdd 2 (SignedScalingSign.destinationSlot a d negative))

/-- Physical output retains the complete exact signed affine recipe after
both descriptor families have been synthesized and used by the executor. -/
theorem output_tape {Q a d B : ℕ} (hQ : 0 < Q) (ha : 0 < a) (hd : 0 < d)
    (hcop : a.Coprime Q) (negative : Bool) (A : Setup a) (D : Setup d) (S : SignControls)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (r : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : ℕ → List (Fin 4)) :
    (output ha hd negative A D S Q B source p middle r signMiddle t dest q payload).tape
      (destinationSlot a d negative) =
      putWord dest q (ScalingAffineBridge.signedBlocks ha Q d negative payload).flatten := by
  rw [output,destinationSlot,Placement.combine_tape_active]
  exact SignedScalingSign.output_tape hQ ha hd hcop negative (prepared ha A Q B) (prepared hd D Q B) S
    source p middle r signMiddle t dest q payload

/-- Synthesis spare tapes survive literally; generated descriptor banks remain
part of the active consumer state for subsequent fibers. -/
theorem output_spares {a d : ℕ} (ha : 0 < a) (hd : 0 < d) (negative : Bool) (A : Setup a) (D : Setup d)
    (S : SignControls) (Q B : ℕ) (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (r : ℤ)
    (signMiddle : ℤ → Fin 4) (t : ℤ) (dest : ℤ → Fin 4) (q : ℤ) (payload : ℕ → List (Fin 4)) :
    Placement.extra (executionPlacement a d)
      (output ha hd negative A D S Q B source p middle r signMiddle t dest q payload) =
      ScalingPreparedExecution.spare.append ScalingPreparedExecution.spare :=
  Placement.extra_combine _ _ _

theorem tapeCount_eq (a d : ℕ) : TapeCount a d = 40+4*(a+d) := by
  dsimp only [TapeCount]
  rw [ScalingPreparedExecution.tapeCount_eq,ScalingPreparedExecution.tapeCount_eq]
  omega

theorem stateCount_eq (a d : ℕ) (negative : Bool) :
    SynthesisStates a+SynthesisStates d+SignedScalingSign.states a d negative =
      117*(a+d)+(if negative then 627 else 295) := by
  rw [SignedScalingSign.stateCount_eq]
  dsimp only [SynthesisStates]
  cases negative <;> simp <;> omega

end IntegerMultBounds.Machine.SignedScalingPrepared
