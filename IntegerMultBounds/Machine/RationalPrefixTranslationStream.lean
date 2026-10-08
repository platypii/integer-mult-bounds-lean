import IntegerMultBounds.Machine.RationalPrefixTranslationExecution
import IntegerMultBounds.Machine.CountedLoopReuseAlphabet
import IntegerMultBounds.Machine.TranslationPreparedFamily

/-! Consecutive rational-controlled translations with actual mixed-prefix carry
scheduling. Field zero controls the shift; the fixed order may put it anywhere.
All other prefix fields advance on their actual tapes and retain independent
widths. Their carry cost is amortized, not rescanned per payload fiber. -/
namespace IntegerMultBounds.Machine.RationalPrefixTranslationStream

open TranslationStream (blocks fibers)
variable {radix c : ℕ} [Fact radix.Prime]

def fields (order : List (Fin (c+1))) (initial : Fin (c+1) → List (Fin radix)) (i : ℕ) :=
  PrefixCounterData.iterateFields (Fact.out : radix.Prime).two_le order i initial

@[simp] theorem fields_length (order : List (Fin (c+1))) (initial : Fin (c+1) → List (Fin radix))
    (i : ℕ) (j : Fin (c+1)) : (fields order initial i j).length = (initial j).length :=
  PrefixCounterData.iterate_widths _ _ _ _ _

theorem fields_succ (order : List (Fin (c+1))) (initial : Fin (c+1) → List (Fin radix)) (i : ℕ) :
    fields order initial (i+1) = PrefixCounterData.advanceFields (Fact.out : radix.Prime).two_le order (fields order initial i) := by
  have h (n : ℕ) (ds : Fin (c+1) → List (Fin radix)) :
      PrefixCounterData.iterateFields (Fact.out : radix.Prime).two_le order n
        (PrefixCounterData.advanceFields (Fact.out : radix.Prime).two_le order ds) =
      PrefixCounterData.advanceFields (Fact.out : radix.Prime).two_le order
        (PrefixCounterData.iterateFields (Fact.out : radix.Prime).two_le order n ds) := by
    induction n generalizing ds with
    | zero => rfl
    | succ n ih =>
      simpa only [PrefixCounterData.iterateFields] using
        ih (PrefixCounterData.advanceFields (Fact.out : radix.Prime).two_le order ds)
  exact h i initial

def descriptor (r : ℚ) (order : List (Fin (c+1))) (old : List Bool)
    (initial : Fin (c+1) → List (Fin radix)) : ℕ → List Bool
  | 0 => old
  | i+1 => RationalOffsetPrepare.result r (fields order initial i 0)

def offset (r : ℚ) (order : List (Fin (c+1))) (initial : Fin (c+1) → List (Fin radix)) (i : ℕ) : ℕ :=
  Counter.value (RationalOffsetPrepare.result r (fields order initial i 0))

def outputPrefix (r : ℚ) (order : List (Fin (c+1))) (initial : Fin (c+1) → List (Fin radix))
    (n : ℕ) (payload : ℕ → ℕ → List (Fin 4)) :=
  TranslationPreparedFamily.outputPrefix (offset r order initial) (radix^(initial 0).length) n payload

def state (r : ℚ) (order : List (Fin (c+1))) (B n : ℕ) (source dest : ℤ → Fin 4) (p q : ℤ)
    (bs qs old : List Bool) (initial : Fin (c+1) → List (Fin radix)) (payload : ℕ → ℕ → List (Fin 4)) (i : ℕ) : Tapes (16+c) radix :=
  RationalPrefixTranslationExecution.bank
    (putWord source p (fibers (radix^(initial 0).length) n payload).flatten)
    (putWord dest q (outputPrefix r order initial i payload))
    (p+((i*(radix^(initial 0).length*B) : ℕ) : ℤ)) (q+((i*(radix^(initial 0).length*B) : ℕ) : ℤ))
    bs qs (descriptor r order old initial i) (descriptor r order old initial i) (fields order initial i)

private theorem uniform_blocks (Q B i : ℕ) (payload : ℕ → ℕ → List (Fin 4))
    (hwidth : ∀ i y, (payload i y).length = B) : BlockRotationData.Uniform B (blocks Q (payload i)) := by
  intro block hb
  obtain ⟨y,_,rfl⟩ := List.mem_map.mp hb
  exact hwidth i y

private theorem fiber_length (Q B i : ℕ) (payload : ℕ → ℕ → List (Fin 4))
    (hwidth : ∀ i y, (payload i y).length = B) : (blocks Q (payload i)).flatten.length = Q*B := by
  rw [BlockRotationData.uniform_volume B _ (uniform_blocks Q B i payload hwidth)]
  simp [blocks]

private theorem source_fiber (Q B n i : ℕ) (source : ℤ → Fin 4) (p : ℤ)
    (payload : ℕ → ℕ → List (Fin 4)) (hwidth : ∀ i y, (payload i y).length = B) (hi : i < n) :
    putWord (putWord source p (fibers Q n payload).flatten) (p+((i*(Q*B) : ℕ) : ℤ))
      (blocks Q (payload i)).flatten = putWord source p (fibers Q n payload).flatten := by
  have hu : BlockRotationData.Uniform (Q*B) (fibers Q n payload) := by
    intro word hw
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hw
    exact fiber_length Q B j payload hwidth
  have hi' : i < (fibers Q n payload).length := by simpa [fibers] using hi
  have hh := FiberShift.source_fiber source p (fibers Q n payload) (Q*B) i hu hi'
  simpa [fibers] using hh

private theorem descriptor_canonical (r : ℚ) (order : List (Fin (c+1))) (old : List Bool)
    (initial : Fin (c+1) → List (Fin radix)) (cold : GrowingCounterData.Canonical old) (i : ℕ) :
    GrowingCounterData.Canonical (descriptor r order old initial i) := by
  cases i with
  | zero => exact cold
  | succ i => exact RationalOffsetPrepare.result_canonical r _

private theorem descriptor_lt (r : ℚ) (order : List (Fin (c+1))) (old : List Bool)
    (initial : Fin (c+1) → List (Fin radix)) (hold : Counter.value old < radix^(initial 0).length) (i : ℕ) :
    Counter.value (descriptor r order old initial i) < radix^(initial 0).length := by
  cases i with
  | zero => exact hold
  | succ i => simpa only [descriptor,fields_length] using RationalOffsetPrepare.result_lt r (fields order initial i 0)

theorem body_hoare (r : ℚ) (order : List (Fin (c+1))) (hne : order ≠ []) (hnodup : order.Nodup)
    {B n i : ℕ} (hB : 0 < B) (hi : i < n) (source dest : ℤ → Fin 4) (p q : ℤ)
    (bs qs old : List Bool) (initial : Fin (c+1) → List (Fin radix))
    (hb : Counter.value bs = B) (hq : Counter.value qs = radix^(initial 0).length)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (cold : GrowingCounterData.Canonical old) (hold : Counter.value old < radix^(initial 0).length)
    (payload : ℕ → ℕ → List (Fin 4)) (hwidth : ∀ i y, (payload i y).length = B) :
    HoareTime (RationalPrefixTranslationExecution.program r order hne)
      (fun v => v = state r order B n source dest p q bs qs old initial payload i)
      (fun v => v = state r order B n source dest p q bs qs old initial payload (i+1))
      (516*(radix^(initial 0).length*B)+1+
        PrefixCounterData.stepCost (Fact.out : radix.Prime).two_le order (fields order initial i)) := by
  let Q := radix^(initial 0).length
  let S := putWord source p (fibers Q n payload).flatten
  let D := putWord dest q (outputPrefix r order initial i payload)
  let P := p+((i*(Q*B) : ℕ) : ℤ)
  let R := q+((i*(Q*B) : ℕ) : ℤ)
  have hc := descriptor_canonical r order old initial cold i
  have hl := descriptor_lt r order old initial hold i
  have ht := RationalPrefixTranslationExecution.translate_hoare r order hne hnodup B hB S D P R
    (blocks Q (payload i)) bs qs (descriptor r order old initial i) (descriptor r order old initial i) (fields order initial i)
    (by simp [blocks,Q]) (uniform_blocks Q B i payload hwidth) hb (by simpa using hq) cb cq hc hc
    (by simpa using hl) (by simpa using hl)
  unfold RationalPrefixTranslationExecution.input RationalPrefixTranslationExecution.output at ht
  simp only [fields_length] at ht
  have hs : putWord S P (blocks Q (payload i)).flatten = S := source_fiber Q B n i source p payload hwidth hi
  rw [hs] at ht
  have hd : putWord D R (BlockRotationData.rotate (offset r order initial i) (blocks Q (payload i))).flatten =
      putWord dest q (outputPrefix r order initial (i+1) payload) := by
    change putWord (putWord dest q (TranslationPreparedFamily.outputPrefix (offset r order initial) (radix^(initial 0).length) i payload))
      (q+((i*(radix^(initial 0).length*B) : ℕ) : ℤ))
      (BlockRotationData.rotate (offset r order initial i) (blocks (radix^(initial 0).length) (payload i))).flatten =
      putWord dest q (TranslationPreparedFamily.outputPrefix (offset r order initial) (radix^(initial 0).length) (i+1) payload)
    rw [← TranslationPreparedFamily.prefix_length (offset r order initial) (radix^(initial 0).length) B i payload hwidth,
      putWord_append_forward,TranslationPreparedFamily.prefix_succ]
  change putWord D R (BlockRotationData.rotate (Counter.value (RationalOffsetPrepare.result r (fields order initial i 0)))
    (blocks Q (payload i))).flatten = _ at hd
  rw [hd] at ht
  have hpos (z : ℤ) : z+(i : ℤ)*((radix : ℤ)^(initial 0).length*B)+(radix : ℤ)^(initial 0).length*B =
      z+((i+1 : ℕ) : ℤ)*((radix : ℤ)^(initial 0).length*B) := by push_cast; ring
  simpa only [state,S,D,P,R,Q,descriptor,← fields_succ,Nat.cast_mul,Nat.cast_pow,hpos] using ht

def program (r : ℚ) (order : List (Fin (c+1))) (hne : order ≠ []) :=
  CountedLoopReuseAlphabet.program (RationalPrefixTranslationExecution.program (radix := radix) r order hne)

/-- Actual carry costs telescope across all prefix fields, including spectators. -/
theorem scheduler_sum_bound (order : List (Fin (c+1))) (initial : Fin (c+1) → List (Fin radix)) (n : ℕ) :
    (∑ i ∈ Finset.range n, PrefixCounterData.stepCost (Fact.out : radix.Prime).two_le order (fields order initial i)) ≤
      4*order.length*n+2*∑ j, (initial j).length := by
  have hp : (∑ i ∈ Finset.range n, PrefixCounterData.stepCost (Fact.out : radix.Prime).two_le order (fields order initial i))+
      2*PrefixCounterData.potential (fields order initial n) ≤ 4*order.length*n+2*PrefixCounterData.potential initial := by
    induction n with
    | zero => simp [fields,PrefixCounterData.iterateFields]
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have hh := PrefixCounterData.step_potential (Fact.out : radix.Prime).two_le order (fields order initial n)
      rw [← fields_succ] at hh
      nlinarith
  have hw : PrefixCounterData.potential initial ≤ ∑ j, (initial j).length :=
    Finset.sum_le_sum (fun j _ => RadixCounterData.maxWeight_le_length (initial j))
  omega

/-- Physical family execution with the exact sum of mixed-prefix carry costs. -/
theorem translate_hoare (r : ℚ) (order : List (Fin (c+1))) (hne : order ≠ []) (hnodup : order.Nodup)
    {B n : ℕ} (hB : 0 < B) (source dest : ℤ → Fin 4) (p q : ℤ)
    (bs qs ns old : List Bool) (initial : Fin (c+1) → List (Fin radix))
    (hb : Counter.value bs = B) (hq : Counter.value qs = radix^(initial 0).length) (hn : Counter.value ns = n)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (cold : GrowingCounterData.Canonical old) (hold : Counter.value old < radix^(initial 0).length)
    (payload : ℕ → ℕ → List (Fin 4)) (hwidth : ∀ i y, (payload i y).length = B) :
    HoareTime (program r order hne)
      (fun v => v = CountedLoopReuseAlphabet.bank
        (state r order B n source dest p q bs qs old initial payload 0)
        CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary ns) 1 1)
      (fun v => v = CountedLoopReuseAlphabet.bank
        (state r order B n source dest p q bs qs old initial payload n)
        CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary ns) 1 1)
      ((∑ i ∈ Finset.range n, PrefixCounterData.stepCost (Fact.out : radix.Prime).two_le order (fields order initial i))+
        n*(516*(radix^(initial 0).length*B)+7)+7*ns.length+16) := by
  have hh := CountedLoopReuseAlphabet.loop_hoare (RationalPrefixTranslationExecution.program r order hne) ns n
    (state r order B n source dest p q bs qs old initial payload)
    (fun i => 516*(radix^(initial 0).length*B)+1+PrefixCounterData.stepCost (Fact.out : radix.Prime).two_le order (fields order initial i)) hn
    (fun i hi => body_hoare r order hne hnodup hB hi source dest p q bs qs old initial hb hq cb cq cold hold payload hwidth)
  have hcost :
      (∑ i ∈ Finset.range n, (516*(radix^(initial 0).length*B)+1+
        PrefixCounterData.stepCost (Fact.out : radix.Prime).two_le order (fields order initial i)))+6*n+7*ns.length+16 =
      (∑ i ∈ Finset.range n, PrefixCounterData.stepCost (Fact.out : radix.Prime).two_le order (fields order initial i))+
        n*(516*(radix^(initial 0).length*B)+7)+7*ns.length+16 := by
    simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,smul_eq_mul]
    ring
  simpa only [program,hcost] using hh

/-- Data movement is uniformly linear in payload volume. Arbitrarily wide
spectators contribute only their initial potential, not a width scan per fiber. -/
theorem translate_hoare_linear (r : ℚ) (order : List (Fin (c+1))) (hne : order ≠ []) (hnodup : order.Nodup)
    {B n : ℕ} (hB : 0 < B) (source dest : ℤ → Fin 4) (p q : ℤ)
    (bs qs ns old : List Bool) (initial : Fin (c+1) → List (Fin radix))
    (hb : Counter.value bs = B) (hq : Counter.value qs = radix^(initial 0).length) (hn : Counter.value ns = n)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (cn : GrowingCounterData.Canonical ns) (cold : GrowingCounterData.Canonical old)
    (hold : Counter.value old < radix^(initial 0).length) (payload : ℕ → ℕ → List (Fin 4))
    (hwidth : ∀ i y, (payload i y).length = B) :
    HoareTime (program r order hne)
      (fun v => v = CountedLoopReuseAlphabet.bank
        (state r order B n source dest p q bs qs old initial payload 0)
        CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary ns) 1 1)
      (fun v => v = CountedLoopReuseAlphabet.bank
        (state r order B n source dest p q bs qs old initial payload n)
        CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary ns) 1 1)
      ((530+4*order.length)*(fibers (radix^(initial 0).length) n payload).flatten.length+
        2*(∑ j, (initial j).length)+23) := by
  apply (translate_hoare r order hne hnodup hB source dest p q bs qs ns old initial hb hq hn cb cq cold hold payload hwidth).consequence
    (fun _ h => h) (fun _ h => h) _
  rw [TranslationStream.source_length (radix^(initial 0).length) B n payload hwidth]
  have hs := scheduler_sum_bound order initial n
  have hw := GrowingCounterData.canonical_width ns cn
  have hl := Nat.log2_le_self (Counter.value ns)
  have hp : 1 ≤ radix^(initial 0).length := Nat.one_le_pow _ _ (by have := (Fact.out : radix.Prime).two_le; omega)
  have hbvol : 1 ≤ radix^(initial 0).length*B := by nlinarith
  have hnvol : n ≤ n*(radix^(initial 0).length*B) := by nlinarith
  have htail := Nat.mul_le_mul_left (4*order.length+14) hnvol
  nlinarith

/-- Exact selected-field meaning of every computed offset, without a control oracle. -/
theorem offset_value (r : ℚ) (hden : r.den < radix) (order : List (Fin (c+1)))
    (initial : Fin (c+1) → List (Fin radix)) (i : ℕ) :
    (offset r order initial i : ZMod (radix^(initial 0).length)) =
      Swap.Modular.ratMod (radix^(initial 0).length) r *
        (RadixDigits.value (fields order initial i 0) : ZMod (radix^(initial 0).length)) := by
  have hh := RationalOffsetPrepare.result_value r hden (fields order initial i 0)
  generalize hlen : (fields order initial i 0).length = b at hh
  have hb : b = (initial 0).length := hlen.symm.trans (fields_length order initial i 0)
  rw [hb] at hh
  exact hh

/-- A full mixed-prefix traversal restores all control and spectator words. -/
theorem fields_full_cycle (initial : Fin (c+1) → List (Fin radix)) :
    fields (List.finRange (c+1)) initial (radix^(∑ j, (initial j).length)) = initial :=
  PrefixCounterData.full_cycle _ _

private theorem lex_nonempty (c : ℕ) : List.finRange (c+1) ≠ [] := by
  intro h
  have hh := congrArg List.length h
  simp at hh

def lexProgram (r : ℚ) := program (radix := radix) r (List.finRange (c+1)) (lex_nonempty c)

/-- Complete mixed-prefix traversal has a uniform payload-volume bound, including
all control/spectator widths. The finite coefficient depends only on field count. -/
theorem full_cycle_hoare (r : ℚ) {B n : ℕ} (hB : 0 < B)
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs ns old : List Bool)
    (initial : Fin (c+1) → List (Fin radix)) (hperiod : n = radix^(∑ j, (initial j).length))
    (hb : Counter.value bs = B) (hq : Counter.value qs = radix^(initial 0).length) (hn : Counter.value ns = n)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (cn : GrowingCounterData.Canonical ns) (cold : GrowingCounterData.Canonical old)
    (hold : Counter.value old < radix^(initial 0).length) (payload : ℕ → ℕ → List (Fin 4))
    (hwidth : ∀ i y, (payload i y).length = B) :
    HoareTime (lexProgram r)
      (fun v => v = CountedLoopReuseAlphabet.bank
        (state r (List.finRange (c+1)) B n source dest p q bs qs old initial payload 0)
        CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary ns) 1 1)
      (fun v => v = CountedLoopReuseAlphabet.bank
        (state r (List.finRange (c+1)) B n source dest p q bs qs old initial payload n)
        CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary ns) 1 1)
      ((536+4*c)*(fibers (radix^(initial 0).length) n payload).flatten.length+23) := by
  have hh := translate_hoare_linear r (List.finRange (c+1)) (lex_nonempty c) (List.nodup_finRange _)
    hB source dest p q bs qs ns old initial hb hq hn cb cq cn cold hold payload hwidth
  apply hh.consequence (fun _ h => h) (fun _ h => h) _
  rw [TranslationStream.source_length (radix^(initial 0).length) B n payload hwidth,List.length_finRange]
  have hw := RadixToBinaryData.width_le_power (Fact.out : radix.Prime).two_le (∑ j, (initial j).length)
  rw [← hperiod] at hw
  have hp : 1 ≤ radix^(initial 0).length := Nat.one_le_pow _ _ (by have := (Fact.out : radix.Prime).two_le; omega)
  have hvol : 1 ≤ radix^(initial 0).length*B := by nlinarith
  have hnvol : n ≤ n*(radix^(initial 0).length*B) := by nlinarith
  nlinarith

end IntegerMultBounds.Machine.RationalPrefixTranslationStream
