import IntegerMultBounds.Machine.SignedScalingSign
import IntegerMultBounds.Machine.ScalingStream

/-! Repeated signed rational scaling on consecutive equal-size fibers. The
prepared immutable dimension/piece/tail descriptors are shared across the actual
counted loop. The boundary invariant restores all payload scratch and advances
both external payload heads by the literal fiber volume. -/
namespace IntegerMultBounds.Machine.SignedScalingStream

open SignedScalingExecution (Controls setTape setTape_append_left)
open SignedScalingSign (SignControls)
open CountedCopyReuse (empty binary)

/-- Residue cells retain their physically produced values after the first fiber. -/
def controlsAt {c : ℕ} (hc : 0 < c) (Q i : ℕ) (C : Controls c) : Controls c :=
  { C with modulus := ScalingStream.residueState hc Q i C.modulus
           current := ScalingStream.residueState hc Q i C.current }

theorem controlsAt_valid {c Q B : ℕ} (hc : 0 < c) (C : Controls c) (hC : C.Valid Q B) (i : ℕ) :
    (controlsAt hc Q i C).Valid Q B :=
  ⟨hC.block_value,hC.count_value,hC.block_canonical,hC.count_canonical,hC.piece_value,hC.piece_canonical,hC.scratch_blank⟩

def advanced {c : ℕ} (hc : 0 < c) (Q : ℕ) (C : Controls c) : Controls c :=
  { C with modulus := OneHot.bank C.modulus (ScalingControl.residue hc Q)
           current := OneHot.bank C.current (ScalingControl.residue hc Q) }

private theorem advanced_controlsAt {c : ℕ} (hc : 0 < c) (Q i : ℕ) (C : Controls c) :
    advanced hc Q (controlsAt hc Q i C) = controlsAt hc Q (i+1) C := by
  simp only [advanced,controlsAt,ScalingStream.residueState_step]

private theorem setTape_append_right {l r : ℕ} (v : Tapes l 0) (w : Tapes r 0) (i : Fin r)
    (f : ℤ → Fin 4) (p : ℤ) :
    setTape (v.append w) (Fin.natAdd l i) f p = v.append (setTape w i f p) := by
  unfold setTape Tapes.append
  congr 1 <;> funext j <;> induction j using Fin.addCases <;> simp [Function.update_apply,Fin.ext_iff]
  all_goals rename_i k; intro h; have hk := k.isLt; omega

private theorem copy_set_source (f g clock desc newSource : ℤ → Fin 4) (p q a b newHead : ℤ) :
    setTape (CountedCopyReuse.bank f g clock desc p q a b) 0 newSource newHead =
      CountedCopyReuse.bank newSource g clock desc newHead q a b := by
  unfold setTape CountedCopyReuse.bank
  congr 1 <;> funext i <;> fin_cases i <;> rfl

private theorem copy_set_dest (f g clock desc newDest : ℤ → Fin 4) (p q a b newHead : ℤ) :
    setTape (CountedCopyReuse.bank f g clock desc p q a b) 1 newDest newHead =
      CountedCopyReuse.bank f newDest clock desc p newHead a b := by
  unfold setTape CountedCopyReuse.bank
  congr 1 <;> funext i <;> fin_cases i <;> rfl

private def forwardBank {a : ℕ} (A : Controls a) (source : ℤ → Fin 4) (p : ℤ)
    (middle : ℤ → Fin 4) (r : ℤ) : Tapes (ScalingExecution.TapeCount a) 0 :=
  (ScalingSplit.bank source A.background A.descriptors p A.origins).append
    (ScalingExecutionReuse.auxiliary middle r A.blockBits A.countBits A.modulus A.current)

private def inverseBank {d : ℕ} (D : Controls d) (dest : ℤ → Fin 4) (q : ℤ) :
    Tapes (ScalingExecution.TapeCount d) 0 :=
  (ScalingSplit.bank dest D.background D.descriptors q D.origins).append
    (ScalingInverseExecution.auxiliary empty 0 D.blockBits D.countBits D.modulus D.current)

private theorem inverse_strip {d : ℕ} (D : Controls d) (source dest : ℤ → Fin 4) (p q : ℤ) :
    SignedScalingExecution.stripSource
      ((ScalingSplit.bank dest D.background D.descriptors q D.origins).append
        (ScalingInverseExecution.auxiliary source p D.blockBits D.countBits D.modulus D.current)) =
      inverseBank D dest q := by
  unfold SignedScalingExecution.stripSource SignedScalingExecution.inverseSourceSlot
  rw [setTape_append_right]
  unfold ScalingInverseExecution.auxiliary
  change (ScalingSplit.bank dest D.background D.descriptors q D.origins).append
    (setTape ((((CountedCopyReuse.bank source empty empty (binary D.blockBits) p 0 1 1).append D.modulus).append D.current).append
      (CountedLoopReuse.controls empty (binary D.countBits) 1 1)) _ empty 0) = _
  simp only [setTape_append_left,copy_set_source]
  rfl

private theorem forward_reset {a : ℕ} (ha : 0 < a) (A : Controls a) (Q B : ℕ)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (r : ℤ) (payload : ℕ → List (Fin 4)) :
    setTape (SignedScalingExecution.forwardOutput A ha Q B source p middle r payload)
      (ScalingExecution.destinationSlot a) middle r =
    forwardBank (advanced ha Q A) (putWord source p (ScalingExecution.inputWord Q payload))
      (p+((Q*B : ℕ) : ℤ)) middle r := by
  unfold SignedScalingExecution.forwardOutput ScalingExecutionReuse.output ScalingExecution.destinationSlot
  rw [setTape_append_right]
  unfold ScalingExecutionReuse.finalAuxiliary ScalingExecutionReuse.auxiliary
  change (ScalingSplit.bank _ _ _ _ _).append
    (setTape ((((CountedCopyReuse.bank _ _ _ _ _ _ _ _).append _).append _).append _) _ middle r) = _
  simp only [setTape_append_left,copy_set_dest]
  simp only [forwardBank,advanced,Nat.cast_mul]
  rfl

private def coreBank {a d : ℕ} (A : Controls a) (D : Controls d)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (r : ℤ) (dest : ℤ → Fin 4) (q : ℤ) :
    Tapes (SignedScalingExecution.TapeCount a d) 0 :=
  ((forwardBank A source p middle r).append (inverseBank D dest q)).append
    (CountedSpanSeek.bank empty 0 A.blockBits A.countBits)

private theorem core_input {a d : ℕ} (ha : 0 < a) (A : Controls a) (D : Controls d) (Q : ℕ)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (r : ℤ) (dest : ℤ → Fin 4) (q : ℤ)
    (payload : ℕ → List (Fin 4)) :
    SignedScalingExecution.unsignedInput ha A D Q source p middle r dest q payload =
    coreBank A D (putWord source p (ScalingExecution.inputWord Q payload)) p middle r dest q := by
  unfold SignedScalingExecution.unsignedInput SignedScalingExecution.inverseInput ScalingInverseExecution.input
  rw [inverse_strip]
  rfl

private theorem core_output {a d : ℕ} (ha : 0 < a) (hd : 0 < d) (A : Controls a) (D : Controls d) (Q B : ℕ)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (r : ℤ) (dest : ℤ → Fin 4) (q : ℤ)
    (payload : ℕ → List (Fin 4)) :
    SignedScalingExecution.unsignedOutput ha hd A D Q B source p middle r dest q payload =
    coreBank (advanced ha Q A) (advanced hd Q D)
      (putWord source p (ScalingExecution.inputWord Q payload)) (p+((Q*B : ℕ) : ℤ)) middle r
      (putWord dest q (SignedScalingSign.unsignedBlocks ha Q d payload).flatten) (q+((Q*B : ℕ) : ℤ)) := by
  unfold SignedScalingExecution.unsignedOutput
  rw [forward_reset]
  unfold SignedScalingExecution.inverseOutput ScalingInverseExecution.output ScalingInverseExecution.finalAuxiliary
  have hs := inverse_strip (advanced hd Q D)
    (putWord middle r (ScalingScatter.inputWord Q (SignedScalingExecution.numeratorPayload ha Q payload)))
    (putWord dest q (ScalingInverseExecution.outputWord Q d (SignedScalingExecution.numeratorPayload ha Q payload)))
    (r+((Q*B : ℕ) : ℤ)) (q+((Q*B : ℕ) : ℤ))
  dsimp only [advanced] at hs
  rw [hs]
  rfl

/-- Complete payload-ready bank with no implicit repositioning. -/
def bank {a d : ℕ} (negative : Bool) (A : Controls a) (D : Controls d) (S : SignControls)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (r : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) : Tapes (SignedScalingSign.TapeCount a d) 0 :=
  ((coreBank A D source p middle r (if negative then signMiddle else dest) (if negative then t else q)).append
    (SignedScalingSign.signBank S A.blockBits (if negative then dest else empty) (if negative then q else 0))).append
    (CountedSpanSeek.bank empty 0 A.blockBits A.countBits)

theorem input_eq {a d : ℕ} (ha : 0 < a) (negative : Bool) (A : Controls a) (D : Controls d)
    (S : SignControls) (Q : ℕ) (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (r : ℤ)
    (signMiddle : ℤ → Fin 4) (t : ℤ) (dest : ℤ → Fin 4) (q : ℤ) (payload : ℕ → List (Fin 4)) :
    SignedScalingSign.input ha negative A D S Q source p middle r signMiddle t dest q payload =
    bank negative A D S (putWord source p (ScalingExecution.inputWord Q payload)) p middle r signMiddle t dest q := by
  cases negative <;> simp only [SignedScalingSign.input,SignedScalingSign.positiveInput,SignedScalingSign.negativeInput,
    Bool.false_eq_true,ite_false,ite_true,core_input,bank]

private theorem core_set_dest {a d : ℕ} (A : Controls a) (D : Controls d)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (r : ℤ) (dest newDest : ℤ → Fin 4) (q newHead : ℤ) :
    setTape (coreBank A D source p middle r dest q) (SignedScalingExecution.destinationSlot a d) newDest newHead =
    coreBank A D source p middle r newDest newHead := by
  unfold coreBank SignedScalingExecution.destinationSlot
  rw [setTape_append_left,setTape_append_right]
  unfold inverseBank ScalingInverseExecution.destinationSlot
  rw [setTape_append_left]
  unfold ScalingSplit.bank
  rw [setTape_append_left,copy_set_source]

/-- The produced bank is exactly ready for a next fiber, with original shared
scratch and the actual final residue cells. No head update is assumed. -/
theorem output_eq {Q a d : ℕ} (hQ : 0 < Q) (ha : 0 < a) (hd : 0 < d) (hcop : a.Coprime Q)
    (negative : Bool) (A : Controls a) (D : Controls d) (S : SignControls) (B : ℕ)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (r : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : ℕ → List (Fin 4)) :
    SignedScalingSign.output ha hd negative A D S Q B source p middle r signMiddle t dest q payload =
    bank negative (advanced ha Q A) (advanced hd Q D) S
      (putWord source p (ScalingExecution.inputWord Q payload)) (p+((Q*B : ℕ) : ℤ)) middle r signMiddle t
      (putWord dest q (ScalingAffineBridge.signedBlocks ha Q d negative payload).flatten) (q+((Q*B : ℕ) : ℤ)) := by
  rw [← SignedScalingSign.signed_blocks hQ ha hcop]
  cases negative <;> simp only [SignedScalingSign.output,SignedScalingSign.positiveOutput,SignedScalingSign.negativeOutput,
    Bool.false_eq_true,ite_false,ite_true,core_output,core_set_dest,bank,advanced]

abbrev fibers := ScalingStream.fibers

def outputPrefix {a : ℕ} (ha : 0 < a) (Q d : ℕ) (negative : Bool) (i : ℕ)
    (payload : ℕ → ℕ → List (Fin 4)) : List (Fin 4) :=
  ((List.range i).map (fun j => (ScalingAffineBridge.signedBlocks ha Q d negative (payload j)).flatten)).flatten

theorem block_volume {Q a B : ℕ} (hQ : 0 < Q) (ha : 0 < a) (hcop : a.Coprime Q)
    (d : ℕ) (negative : Bool) (payload : ℕ → List (Fin 4)) (hwidth : ∀ y, (payload y).length = B) :
    (ScalingAffineBridge.signedBlocks ha Q d negative payload).flatten.length = Q*B := by
  rw [← SignedScalingSign.signed_blocks hQ ha hcop]
  cases negative <;> simp only [Bool.false_eq_true,ite_false,ite_true,BlockNegationData.payload_length]
  all_goals exact SignedScalingSign.blocks_volume ha Q d B payload hwidth

theorem prefix_length {Q a B : ℕ} (hQ : 0 < Q) (ha : 0 < a) (hcop : a.Coprime Q)
    (d : ℕ) (negative : Bool) (i : ℕ) (payload : ℕ → ℕ → List (Fin 4))
    (hwidth : ∀ j y, (payload j y).length = B) :
    (outputPrefix ha Q d negative i payload).length = i*(Q*B) := by
  unfold outputPrefix
  rw [BlockRotationData.uniform_volume (Q*B)]
  · simp
  · intro word hw
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hw
    exact block_volume hQ ha hcop d negative (payload j) (hwidth j)

theorem prefix_succ {a : ℕ} (ha : 0 < a) (Q d : ℕ) (negative : Bool) (i : ℕ)
    (payload : ℕ → ℕ → List (Fin 4)) :
    outputPrefix ha Q d negative (i+1) payload = outputPrefix ha Q d negative i payload ++
      (ScalingAffineBridge.signedBlocks ha Q d negative (payload i)).flatten := by
  simp [outputPrefix,List.range_succ,List.map_append,List.flatten_append]

private theorem source_fiber (Q B n i : ℕ) (source : ℤ → Fin 4) (p : ℤ)
    (payload : ℕ → ℕ → List (Fin 4)) (hwidth : ∀ i y, (payload i y).length = B) (hi : i < n) :
    putWord (putWord source p (fibers Q n payload).flatten) (p+((i*(Q*B) : ℕ) : ℤ))
      (ScalingExecution.inputWord Q (payload i)) = putWord source p (fibers Q n payload).flatten := by
  have hu : BlockRotationData.Uniform (Q*B) (fibers Q n payload) := by
    intro word hw
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hw
    unfold ScalingExecution.inputWord
    rw [BlockRotationData.uniform_volume B]
    · simp
    · intro block hb
      obtain ⟨y,_,rfl⟩ := List.mem_map.mp hb
      exact hwidth j y
  have hi' : i < (fibers Q n payload).length := by simpa [fibers,ScalingStream.fibers] using hi
  have hh := FiberShift.source_fiber source p (fibers Q n payload) (Q*B) i hu hi'
  simpa [fibers,ScalingStream.fibers] using hh

/-- Full invariant: one shared reusable scratch interval for each temporary
bank, one immutable descriptor family, and both external heads at fiber i. -/
def state {a d : ℕ} (ha : 0 < a) (hd : 0 < d) (negative : Bool) (A : Controls a) (D : Controls d)
    (S : SignControls) (Q B n : ℕ) (source : ℤ → Fin 4) (p : ℤ)
    (middle : ℤ → Fin 4) (r : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ) (dest : ℤ → Fin 4) (q : ℤ)
    (payload : ℕ → ℕ → List (Fin 4)) (i : ℕ) : Tapes (SignedScalingSign.TapeCount a d) 0 :=
  bank negative (controlsAt ha Q i A) (controlsAt hd Q i D) S
    (putWord source p (fibers Q n payload).flatten) (p+((i*(Q*B) : ℕ) : ℤ)) middle r signMiddle t
    (putWord dest q (outputPrefix ha Q d negative i payload)) (q+((i*(Q*B) : ℕ) : ℤ))

theorem body_hoare {Q a d B n i : ℕ} (hQ : 0 < Q) (ha : 0 < a) (hd : 0 < d)
    (hcopA : a.Coprime Q) (hcopD : d.Coprime Q) (hB : 0 < B) (hi : i < n) (negative : Bool)
    (A : Controls a) (D : Controls d) (S : SignControls) (hA : A.Valid Q B) (hD : D.Valid Q B)
    (hS : negative = true → S.Valid Q B)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (r : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : ℕ → ℕ → List (Fin 4)) (hwidth : ∀ j y, (payload j y).length = B)
    (hblank : ∀ z, r ≤ z → z < r+((Q*B : ℕ) : ℤ) → middle z = blank)
    (hsblank : negative = true → ∀ z, t ≤ z → z < t+((Q*B : ℕ) : ℤ) → signMiddle z = blank) :
    HoareTime (SignedScalingSign.program ha hd negative)
      (fun v => v = state ha hd negative A D S Q B n source p middle r signMiddle t dest q payload i)
      (fun v => v = state ha hd negative A D S Q B n source p middle r signMiddle t dest q payload (i+1))
      (SignedScalingSign.bound Q B a d negative) := by
  have hh := SignedScalingSign.scaling_hoare hQ ha hd hcopA hcopD hB negative
    (controlsAt ha Q i A) (controlsAt hd Q i D) S (controlsAt_valid ha A hA i) (controlsAt_valid hd D hD i) hS
    (putWord source p (fibers Q n payload).flatten) (p+((i*(Q*B : ℕ) : ℕ) : ℤ)) middle r signMiddle t
    (putWord dest q (outputPrefix ha Q d negative i payload)) (q+((i*(Q*B : ℕ) : ℕ) : ℤ)) (payload i)
    (hwidth i) hblank hsblank
  rw [input_eq,output_eq hQ ha hd hcopA,source_fiber Q B n i source p payload hwidth hi,
    advanced_controlsAt,advanced_controlsAt] at hh
  have hout : putWord (putWord dest q (outputPrefix ha Q d negative i payload)) (q+((i*(Q*B : ℕ) : ℕ) : ℤ))
      (ScalingAffineBridge.signedBlocks ha Q d negative (payload i)).flatten =
      putWord dest q (outputPrefix ha Q d negative (i+1) payload) := by
    rw [← prefix_length hQ ha hcopA d negative i payload hwidth,putWord_append_forward,prefix_succ]
  rw [hout] at hh
  have hlen : (i+1)*(Q*B) = i*(Q*B)+Q*B := by ring
  simpa only [state,hlen,Nat.cast_add,add_assoc] using hh

/-- Setup can target the initial reusable state without touching any payload. -/
theorem initial_state {a d : ℕ} (ha : 0 < a) (hd : 0 < d) (negative : Bool)
    (A : Controls a) (D : Controls d) (S : SignControls) (Q B n : ℕ)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (r : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : ℕ → ℕ → List (Fin 4)) :
    SignedScalingSign.input ha negative A D S Q (putWord source p (fibers Q n payload).flatten) p
      middle r signMiddle t dest q (fun _ => []) =
    state ha hd negative A D S Q B n source p middle r signMiddle t dest q payload 0 := by
  rw [input_eq]
  simp [state,controlsAt,ScalingStream.residueState,outputPrefix,ScalingExecution.inputWord,putWord]

abbrev TapeCount (a d : ℕ) := SignedScalingSign.TapeCount a d+2
abbrev States (a d : ℕ) (negative : Bool) := 7+(SignedScalingSign.states a d negative+5)+4

/-- A genuine reusable counted loop, independent of all three dimensions. -/
def program {a d : ℕ} (ha : 0 < a) (hd : 0 < d) (negative : Bool) :
    Program (TapeCount a d) (States a d negative) 0 :=
  CountedLoopReuse.program (SignedScalingSign.program ha hd negative)

/-- One descriptor bank is reused by all n complete signed executions. Every
outer-clock copy, loop transition, and cleanup movement is charged. -/
theorem scaling_hoare {Q a d B n : ℕ} (hQ : 0 < Q) (ha : 0 < a) (hd : 0 < d)
    (hcopA : a.Coprime Q) (hcopD : d.Coprime Q) (hB : 0 < B) (negative : Bool)
    (A : Controls a) (D : Controls d) (S : SignControls) (hA : A.Valid Q B) (hD : D.Valid Q B)
    (hS : negative = true → S.Valid Q B) (ns : List Bool) (hn : Counter.value ns = n)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (r : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : ℕ → ℕ → List (Fin 4)) (hwidth : ∀ j y, (payload j y).length = B)
    (hblank : ∀ z, r ≤ z → z < r+((Q*B : ℕ) : ℤ) → middle z = blank)
    (hsblank : negative = true → ∀ z, t ≤ z → z < t+((Q*B : ℕ) : ℤ) → signMiddle z = blank) :
    HoareTime (program ha hd negative)
      (fun v => v = CountedLoopReuse.bank
        (state ha hd negative A D S Q B n source p middle r signMiddle t dest q payload 0) empty (binary ns) 1 1)
      (fun v => v = CountedLoopReuse.bank
        (state ha hd negative A D S Q B n source p middle r signMiddle t dest q payload n) empty (binary ns) 1 1)
      (n*(SignedScalingSign.bound Q B a d negative+6)+7*ns.length+16) := by
  have hh := CountedLoopReuse.loop_hoare (SignedScalingSign.program ha hd negative) ns n
    (state ha hd negative A D S Q B n source p middle r signMiddle t dest q payload)
    (fun _ => SignedScalingSign.bound Q B a d negative) hn
    (fun i hi => body_hoare hQ ha hd hcopA hcopD hB hi negative A D S hA hD hS
      source p middle r signMiddle t dest q payload hwidth hblank hsblank)
  have hcost : (∑ _i ∈ Finset.range n, SignedScalingSign.bound Q B a d negative)+6*n+7*ns.length+16 =
      n*(SignedScalingSign.bound Q B a d negative+6)+7*ns.length+16 := by
    simp only [Finset.sum_const,Finset.card_range,smul_eq_mul]
    ring
  rw [hcost] at hh
  exact hh

theorem linear_bound (Q B a d n width : ℕ) (negative : Bool) (hQ : 0 < Q) (hB : 0 < B)
    (hw : width ≤ n+1) :
    n*(SignedScalingSign.bound Q B a d negative+6)+7*width+16 ≤
      (1381+120*(a+d))*(n*(Q*B))+23 := by
  have hv : 1 ≤ Q*B := by nlinarith
  have hnv : n ≤ n*(Q*B) := Nat.le_mul_of_pos_right n (by omega)
  have hc := Nat.mul_le_mul_left (120*(a+d)+522) hnv
  unfold SignedScalingSign.bound
  split_ifs <;> nlinarith

/-- Linear in complete physical payload volume, including the outer loop and
its cleanup. Derived descriptors are prepared inputs at this reusable boundary. -/
theorem scaling_hoare_linear {Q a d B n : ℕ} (hQ : 0 < Q) (ha : 0 < a) (hd : 0 < d)
    (hcopA : a.Coprime Q) (hcopD : d.Coprime Q) (hB : 0 < B) (negative : Bool)
    (A : Controls a) (D : Controls d) (S : SignControls) (hA : A.Valid Q B) (hD : D.Valid Q B)
    (hS : negative = true → S.Valid Q B) (ns : List Bool) (hn : Counter.value ns = n)
    (cn : GrowingCounterData.Canonical ns)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (r : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : ℕ → ℕ → List (Fin 4)) (hwidth : ∀ j y, (payload j y).length = B)
    (hblank : ∀ z, r ≤ z → z < r+((Q*B : ℕ) : ℤ) → middle z = blank)
    (hsblank : negative = true → ∀ z, t ≤ z → z < t+((Q*B : ℕ) : ℤ) → signMiddle z = blank) :
    HoareTime (program ha hd negative)
      (fun v => v = CountedLoopReuse.bank
        (state ha hd negative A D S Q B n source p middle r signMiddle t dest q payload 0) empty (binary ns) 1 1)
      (fun v => v = CountedLoopReuse.bank
        (state ha hd negative A D S Q B n source p middle r signMiddle t dest q payload n) empty (binary ns) 1 1)
      ((1381+120*(a+d))*(fibers Q n payload).flatten.length+23) := by
  have hw := GrowingCounterData.canonical_width ns cn
  have hl := Nat.log2_le_self (Counter.value ns)
  have hbnd := linear_bound Q B a d n ns.length negative hQ hB (by omega)
  rw [← ScalingStream.source_length Q B n payload hwidth] at hbnd
  exact (scaling_hoare hQ ha hd hcopA hcopD hB negative A D S hA hD hS ns hn
    source p middle r signMiddle t dest q payload hwidth hblank hsblank).consequence (fun _ h => h) (fun _ h => h) hbnd

/-- The actual output tape and head at every fiber boundary. -/
theorem state_destination {a d : ℕ} (ha : 0 < a) (hd : 0 < d) (negative : Bool)
    (A : Controls a) (D : Controls d) (S : SignControls) (Q B n : ℕ)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (r : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : ℕ → ℕ → List (Fin 4)) (i : ℕ) :
    let v := state ha hd negative A D S Q B n source p middle r signMiddle t dest q payload i
    let slot := SignedScalingSign.destinationSlot a d negative
    v.tape slot = putWord dest q (outputPrefix ha Q d negative i payload) ∧
      v.head slot = q+((i*(Q*B : ℕ) : ℕ) : ℤ) := by
  cases negative <;> simp [state,bank,SignedScalingSign.destinationSlot,coreBank,
    SignedScalingExecution.destinationSlot,inverseBank,ScalingInverseExecution.destinationSlot,
    ScalingSplit.bank,Tapes.append,CountedCopyReuse.bank,SignedScalingSign.signBank,BlockNegationReuse.bank]

/-- Negation scratch remains literally unchanged through every iteration. -/
theorem state_scratch {a d : ℕ} (ha : 0 < a) (hd : 0 < d) (negative : Bool)
    (A : Controls a) (D : Controls d) (S : SignControls) (Q B n : ℕ)
    (source : ℤ → Fin 4) (p : ℤ) (middle : ℤ → Fin 4) (r : ℤ) (signMiddle : ℤ → Fin 4) (t : ℤ)
    (dest : ℤ → Fin 4) (q : ℤ) (payload : ℕ → ℕ → List (Fin 4)) (i : ℕ) :
    let v := state ha hd negative A D S Q B n source p middle r signMiddle t dest q payload i
    let slot := Fin.castAdd 5 (Fin.natAdd (SignedScalingExecution.TapeCount a d) (2 : Fin 8))
    v.tape slot = S.scratch ∧ v.head slot = S.origin := by
  simp [state,bank,Tapes.append,SignedScalingSign.signBank,BlockNegationReuse.bank]

theorem tapeCount_eq (a d : ℕ) : TapeCount a d = 40+4*(a+d) := by
  dsimp only [TapeCount]
  rw [SignedScalingSign.tapeCount_eq]
  omega

theorem stateCount_eq (a d : ℕ) (negative : Bool) :
    States a d negative = 98*(a+d)+(if negative then 561 else 229) := by
  dsimp only [States]
  rw [SignedScalingSign.stateCount_eq]
  cases negative <;> simp <;> omega

end IntegerMultBounds.Machine.SignedScalingStream
