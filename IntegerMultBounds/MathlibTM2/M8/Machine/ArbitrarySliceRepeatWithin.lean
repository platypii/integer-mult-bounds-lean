module

public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitrarySliceStepWithin
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitrarySliceRepeat
public import IntegerMultBounds.Machine.CountedLoopReuseAlphabetSpace
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitrarySliceStepBudget
public import IntegerMultBounds.Machine.BinaryCanonicalData
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitrarySliceCall
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthSchedule
public import IntegerMultBounds.MathlibTM2.M8.Machine.CallReady

/-! Runtime-counted slice calls share the proved body workspace. Count copying,
clock initialization and final cleanup have only a linear descriptor allowance. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Machine.ArbitrarySliceRepeatWithin
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
variable [Net]
noncomputable section
open Networks
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open IntegerMultBounds.MathlibTM2.M8.Machine.ArbitrarySliceCall (bank data)

open ArbitrarySliceRepeat

def coefficient : ℕ := ArbitrarySliceCallWithin.coefficient+20

omit [Net] in
private theorem counted_head_congr {s a : ℕ} (v w : Tapes s a)
    (clock descriptor : ℤ → Fin (a+4)) (p r : ℤ) (h : v.head = w.head) :
    (CountedLoopReuseAlphabet.bank v clock descriptor p r).head =
      (CountedLoopReuseAlphabet.bank w clock descriptor p r).head := by
  change (Fin.addCases (m := s) (n := 2) v.head _ : Fin (s+2) → ℤ) =
    (Fin.addCases (m := s) (n := 2) w.head _ : Fin (s+2) → ℤ)
  rw [h]

theorem repeat_within (depth : ℕ) (v : Descriptor) (hs : Fin 6 → List Bool)
    (ts bs as : List Bool) (t b a : ℕ) (hp : v.Positive) (hv : RecursiveDimensionBank.Headers v hs)
    (ht : Counter.value ts = t) (hb : Counter.value bs = b) (ha : Counter.value as = a)
    (ct : GrowingCounterData.Canonical ts) (cb : GrowingCounterData.Canonical bs)
    (ca : GrowingCounterData.Canonical as)
    (hfit : t+a*b ≤ v.width) (hw : b = Machine.width^depth)
    (hr : roleCount^depth ∣ v.rows)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (ready : CallReady.Ready f p node scalar st)
    (frame : Tapes 1 prime) (hfree : RecursiveViewFrame.Free hs frame)
    (x : Fin (volume prime v) → ZMod 2) (lo hi : ℤ)
    (hmargin : ∀ j, lo+(coefficient*volume prime v : ℕ) ≤
      (input (bank (data x) hs ts bs f p node scalar st frame) as).head j ∧
      (input (bank (data x) hs ts bs f p node scalar st frame) as).head j+
        (coefficient*volume prime v : ℕ) ≤ hi) :
    HoareWithin program (fun z => z = input (bank (data x) hs ts bs f p node scalar st frame) as)
      (fun z => z = output (bank (data (images v t b a hfit x)) hs
        (GrowingCounterData.advance (a*b) ts) bs f p node scalar st frame) as)
      (exactCost depth (volume prime v) b a ts bs as) (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi) := by
  let valid (i : ℕ) (hi : i ≤ a) : t+i*b ≤ v.width := by nlinarith
  let xs (i : ℕ) : Fin (volume prime v) → ZMod 2 :=
    if hi : i ≤ a then images v t b i (valid i hi) x else x
  let vs (i : ℕ) := bank (data (xs i)) hs (offsets b ts i) bs f p node scalar st frame
  have hV := RecursiveAffinePrepare.volume_positive Shared50ModularControl.prime_prime.two_le v hp
  have hwV : v.width ≤ volume prime v :=
    RecursiveHeaderBounds.values_le_volume Shared50ModularControl.prime_prime.two_le v hp 3
  have hbpos : 0 < b := by rw [hw]; exact pow_pos width_pos _
  have haV : a ≤ volume prime v := by nlinarith only [hfit,hbpos,hwV]
  have has := GrowingCounterData.canonical_width as ca
  rw [ha] at has
  have halog := Nat.log2_le_self a
  have hasV : as.length ≤ 2*volume prime v := by omega
  let K := 3*as.length+8
  let L := lo+(K : ℕ)
  let U := hi-(K : ℕ)
  have hreserve : ArbitrarySliceCallWithin.coefficient*volume prime v+K ≤ coefficient*volume prime v := by
    dsimp only [coefficient,K]
    nlinarith only [hasV,hV]
  have hcontrolBudget : K+as.length+1 ≤ coefficient*volume prime v := by
    dsimp only [coefficient,K]
    nlinarith only [hasV,hV]
  have hzero : vs 0 = bank (data x) hs ts bs f p node scalar st frame := by
    simp [vs,xs,images,ArbitraryWidthSchedule.run,offsets]
  have hlast : vs a = bank (data (images v t b a hfit x)) hs
      (GrowingCounterData.advance (a*b) ts) bs f p node scalar st frame := by
    simp only [vs,xs,dite_eq_left (show a ≤ a by rfl),offsets_eq b a ts ct]
  have hsliceHeads (i : ℕ) : (vs i).head = (bank (data x) hs ts bs f p node scalar st frame).head :=
    ArbitrarySliceCallWithin.bank_offset_head_eq (xs i) x hs (offsets b ts i) bs ts bs f p node scalar st frame
  have hclock := hmargin (Fin.natAdd sliceCount (0 : Fin 2))
  simp only [ArbitrarySliceRepeat.input,counted,CountedLoopReuseAlphabet.bank,Tapes.append,Fin.addCases_right,
    CountedLoopReuseAlphabet.controls] at hclock
  have hL : L ≤ 0 := by dsimp only [L]; omega
  have hU : (as.length : ℤ)+1 ≤ U := by dsimp only [U]; omega
  have hbodyMargin (i : ℕ) : ∀ j, L+(ArbitrarySliceCallWithin.coefficient*volume prime v : ℕ) ≤ (vs i).head j ∧
      (vs i).head j+(ArbitrarySliceCallWithin.coefficient*volume prime v : ℕ) ≤ U := by
    intro j
    rw [hsliceHeads i]
    have hm := hmargin (Fin.castAdd 2 j)
    simp only [ArbitrarySliceRepeat.input,counted,CountedLoopReuseAlphabet.bank,Tapes.append,Fin.addCases_left] at hm
    dsimp only [L,U]
    omega
  have hbody : ∀ i < a, HoareWithin ArbitrarySliceStep.program (· = vs i) (· = vs (i+1))
      (ArbitrarySliceStep.cost depth (volume prime v) b (offsets b ts i) bs)
      (fun z => ∀ j, L ≤ z.head j ∧ z.head j ≤ U) := by
    intro i hia
    have hstep := ArbitrarySliceStepWithin.step_within depth v hs (offsets b ts i) bs (t+i*b) b hp hv
      (offsets_value b t i ts ht) hb (offsets_canonical b i ts ct) cb (by nlinarith) hw hr
      f p node scalar st ready frame hfree (xs i) L U (hbodyMargin i)
    have hx : xs (i+1) = ArbitraryWidthSliceTranspose.array (t+i*b) b (by nlinarith) (xs i) := by
      simp only [xs,dite_eq_left (show i ≤ a by omega),dite_eq_left (show i+1 ≤ a by omega)]
      exact images_succ v t b i _ x
    simpa only [vs,offsets,hx] using hstep
  have hbodyTime : ∀ i < a, HoareTime ArbitrarySliceStep.program (· = vs i) (· = vs (i+1))
      (ArbitrarySliceStepBudget.budget depth (volume prime v)) := by
    intro i hi
    have hbV : b ≤ volume prime v := by nlinarith only [hfit,hwV,hi]
    have hslen := GrowingCounterData.canonical_width bs cb
    rw [hb] at hslen
    have hblog := Nat.log2_le_self b
    apply (hbody i hi).time.consequence (fun _ h => h) (fun _ h => h)
    exact ArbitrarySliceStepBudget.cost_le depth (volume prime v) b _ bs hV hbV
      (offsets_length_le b t i _ ts ht ct hV (by nlinarith only [hfit,hwV,hi])) (by omega)
  have hloop := CountedLoopReuseAlphabet.loop_hoare ArbitrarySliceStep.program as a vs
    (fun i => ArbitrarySliceStep.cost depth (volume prime v) b (offsets b ts i) bs) ha
    (fun i hi => (hbody i hi).time)
  have hwl := HoareWithin.of_time_invariant (H := fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi) hloop (by
    intro c hc
    obtain ⟨w,rfl,n,hn⟩ := hc
    have hh := CountedLoopReuseAlphabet.loop_heads_of_body ArbitrarySliceStep.program as vs
      (ArbitrarySliceStepBudget.budget depth (volume prime v))
      (by simpa only [ha] using hbodyTime) L U
      (by
        intro i hi j
        have hm := hbodyMargin i j
        constructor <;> omega)
      (by
        intro i hi c hc
        exact (hbody i (by simpa only [ha] using hi)).invariant hc) hn
    rw [min_eq_left hL,max_eq_left hU] at hh
    intro j
    have hj := hh j
    change lo ≤ c.head j ∧ c.head j ≤ hi
    dsimp only [L,U,K] at hj
    omega)
  have hinit := initialize_hoare (vs 0) as
  have hwi := HoareWithin.of_time_heads hinit lo hi (by
    rintro w rfl j
    rw [hzero]
    have hm := hmargin j
    have hb : RecursiveChildQuotientsConstant.cost 0 ≤ coefficient*volume prime v := by
      change 6 ≤ _
      dsimp only [coefficient]
      nlinarith only [hV]
    omega)
  have hclean := cleanup_hoare (vs a) as
  have hwc := HoareWithin.of_time_post_heads hclean lo hi (by
    rintro w rfl j
    change lo+(2*4 : ℕ) ≤ (input (vs a) as).head j ∧ (input (vs a) as).head j+(2*4 : ℕ) ≤ hi
    have he := counted_head_congr (vs a) (bank (data x) hs ts bs f p node scalar st frame)
      (fun _ => blank) (CountedLoopReuseAlphabet.binary as) 0 1 (hsliceHeads a)
    change (input (vs a) as).head = (input (bank (data x) hs ts bs f p node scalar st frame) as).head at he
    rw [he]
    have hm := hmargin j
    have hb : 8 ≤ coefficient*volume prime v := by
      dsimp only [coefficient]
      nlinarith only [hV]
    omega)
  have hfull := (hwi.seq hwl).seq hwc
  rw [hzero,hlast] at hfull
  exact hfull.consequence (fun _ h => h) (fun _ h => h) (by unfold exactCost; omega) (fun _ h => h)

/-- Digit erasure completes the repeated call with both appended tapes blank. -/
theorem consume_within (depth : ℕ) (v : Descriptor) (hs : Fin 6 → List Bool)
    (ts bs as : List Bool) (t b a : ℕ) (hp : v.Positive) (hv : RecursiveDimensionBank.Headers v hs)
    (ht : Counter.value ts = t) (hb : Counter.value bs = b) (ha : Counter.value as = a)
    (ct : GrowingCounterData.Canonical ts) (cb : GrowingCounterData.Canonical bs)
    (ca : GrowingCounterData.Canonical as)
    (hfit : t+a*b ≤ v.width) (hw : b = Machine.width^depth)
    (hr : roleCount^depth ∣ v.rows)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (ready : CallReady.Ready f p node scalar st)
    (frame : Tapes 1 prime) (hfree : RecursiveViewFrame.Free hs frame)
    (x : Fin (volume prime v) → ZMod 2) (lo hi : ℤ)
    (hmargin : ∀ j, lo+(coefficient*volume prime v : ℕ) ≤
      (input (bank (data x) hs ts bs f p node scalar st frame) as).head j ∧
      (input (bank (data x) hs ts bs f p node scalar st frame) as).head j+
        (coefficient*volume prime v : ℕ) ≤ hi) :
    HoareWithin consume (fun z => z = input (bank (data x) hs ts bs f p node scalar st frame) as)
      (fun z => z = (bank (data (images v t b a hfit x)) hs
        (GrowingCounterData.advance (a*b) ts) bs f p node scalar st frame).append (SharedBank.empty 2 prime))
      (exactCost depth (volume prime v) b a ts bs as+2*as.length+5) (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi) := by
  have hrepeat := repeat_within depth v hs ts bs as t b a hp hv ht hb ha ct cb ca hfit hw hr
    f p node scalar st ready frame hfree x lo hi hmargin
  let out := bank (data (images v t b a hfit x)) hs (GrowingCounterData.advance (a*b) ts) bs f p node scalar st frame
  have he := counted_head_congr out (bank (data x) hs ts bs f p node scalar st frame)
    (fun _ => blank) (CountedLoopReuseAlphabet.binary as) 0 1
    (ArbitrarySliceCallWithin.bank_offset_head_eq (images v t b a hfit x) x hs
      (GrowingCounterData.advance (a*b) ts) bs ts bs f p node scalar st frame)
  change (output out as).head = (input (bank (data x) hs ts bs f p node scalar st frame) as).head at he
  have hV := RecursiveAffinePrepare.volume_positive Shared50ModularControl.prime_prime.two_le v hp
  have hwV : v.width ≤ volume prime v :=
    RecursiveHeaderBounds.values_le_volume Shared50ModularControl.prime_prime.two_le v hp 3
  have hbpos : 0 < b := by rw [hw]; exact pow_pos width_pos _
  have haV : a ≤ volume prime v := by nlinarith only [hfit,hbpos,hwV]
  have has := GrowingCounterData.canonical_width as ca
  rw [ha] at has
  have halog := Nat.log2_le_self a
  have hasV : as.length ≤ 2*volume prime v := by omega
  have hbudget : 2*as.length+4 ≤ coefficient*volume prime v := by
    dsimp only [coefficient]
    nlinarith only [hasV,hV]
  have herase := HoareWithin.of_time_heads (eraseDigit_hoare out as) lo hi (by
    rintro w rfl j
    rw [he]
    have hm := hmargin j
    omega)
  exact (hrepeat.seq herase).consequence (fun _ h => h) (fun _ h => h) (by omega) (fun _ h => h)

end
end IntegerMultBounds.MathlibTM2.M8.Machine.ArbitrarySliceRepeatWithin
