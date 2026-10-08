import IntegerMultBounds.Machine.MultiControlPrefixTranslationExecution
import IntegerMultBounds.Machine.CountedLoopReuseAlphabet
import IntegerMultBounds.Machine.TranslationPreparedFamily

/-! Multi-control translation streams with an actual carry scheduler. The exact
bank invariant separates current shared fields from stale leaf copies and old
binary output, refreshed only by the proved physical evaluator. -/
namespace IntegerMultBounds.Machine.MultiControlPrefixTranslationStream

open TranslationStream (blocks fibers)
open RadixLinearCombinationRefresh (Expr leaves)
open MultiControlPrefixTranslationExecution (read)
variable {c radix : ℕ} [Fact radix.Prime]

def fields (order : List (Fin c)) (initial : Fin c → List (Fin radix)) (i : ℕ) :=
  PrefixCounterData.iterateFields (Fact.out : radix.Prime).two_le order i initial

@[simp] theorem fields_length (order : List (Fin c)) (initial : Fin c → List (Fin radix))
    (i : ℕ) (j : Fin c) : (fields order initial i j).length = (initial j).length :=
  PrefixCounterData.iterate_widths _ _ _ _ _

theorem fields_succ (order : List (Fin c)) (initial : Fin c → List (Fin radix)) (i : ℕ) :
    fields order initial (i+1) = PrefixCounterData.advanceFields (Fact.out : radix.Prime).two_le order (fields order initial i) := by
  have h (n : ℕ) (ds : Fin c → List (Fin radix)) :
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


/-- Stale leaf copies at each boundary are exactly the preceding physical
controls. Only the initial stale bank is supplied once. -/
def stale (order : List (Fin c)) (initial old : Fin c → List (Fin radix)) : ℕ → Fin c → List (Fin radix)
  | 0 => old
  | i+1 => fields order initial i

private theorem stale_width (order : List (Fin c)) (initial old : Fin c → List (Fin radix)) (b i : ℕ)
    (hw : ∀ j, (initial j).length = b) (ho : ∀ j, (old j).length = b) :
    ∀ j, (stale order initial old i j).length = b := by
  intro j
  cases i with
  | zero => exact ho j
  | succ i => exact (fields_length order initial i j).trans (hw j)

def offset (e : Expr c) (seed : Fin c) (order : List (Fin c)) (initial : Fin c → List (Fin radix)) (i : ℕ) : ℕ :=
  MultiControlTranslationExecution.offset e (read seed (fields order initial i))

def outputPrefix (e : Expr c) (seed : Fin c) (order : List (Fin c)) (initial : Fin c → List (Fin radix))
    (b n : ℕ) (payload : ℕ → ℕ → List (Fin 4)) :=
  TranslationPreparedFamily.outputPrefix (offset e seed order initial) (radix^b) n payload

/-- Every physical tape at every loop boundary, including stale arithmetic data. -/
def state (e : Expr c) (seed : Fin c) (order : List (Fin c)) (b B n : ℕ) (source dest : ℤ → Fin 4) (p q : ℤ)
    (bs qs : List Bool) (initial old : Fin c → List (Fin radix)) (payload : ℕ → ℕ → List (Fin 4)) (i : ℕ) :
    Tapes (MultiControlTranslationExecution.TapeCount e) radix :=
  MultiControlPrefixTranslationExecution.bank e seed
    (putWord source p (fibers (radix^b) n payload).flatten)
    (putWord dest q (outputPrefix e seed order initial b i payload))
    (p+((i*(radix^b*B) : ℕ) : ℤ)) (q+((i*(radix^b*B) : ℕ) : ℤ)) bs qs
    (MultiControlTranslationExecution.bits e (read seed (stale order initial old i)))
    (fields order initial i) (stale order initial old i)

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


theorem body_hoare (e : Expr c) (seed : Fin c) (order : List (Fin c)) (hne : order ≠ []) (hnodup : order.Nodup)
    {b B n i : ℕ} (hB : 0 < B) (hi : i < n) (source dest : ℤ → Fin 4) (p q : ℤ)
    (bs qs : List Bool) (initial old : Fin c → List (Fin radix))
    (hw : ∀ j, (initial j).length = b) (ho : ∀ j, (old j).length = b)
    (hb : Counter.value bs = B) (hq : Counter.value qs = radix^b)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (payload : ℕ → ℕ → List (Fin 4)) (hwidth : ∀ j y, (payload j y).length = B) :
    HoareTime (MultiControlPrefixTranslationExecution.program e order hne)
      (fun v => v = state e seed order b B n source dest p q bs qs initial old payload i)
      (fun v => v = state e seed order b B n source dest p q bs qs initial old payload (i+1))
      ((13*leaves e+RadixLinearCombination.linearConstant e.erase+496)*(radix^b*B)+1+
        PrefixCounterData.stepCost (Fact.out : radix.Prime).two_le order (fields order initial i)) := by
  let Q := radix^b
  let S := putWord source p (fibers Q n payload).flatten
  let D := putWord dest q (outputPrefix e seed order initial b i payload)
  let P := p+((i*(Q*B) : ℕ) : ℤ)
  let R := q+((i*(Q*B) : ℕ) : ℤ)
  have ht := MultiControlPrefixTranslationExecution.translate_hoare e seed order hne hnodup b B hB S D P R
    (blocks Q (payload i)) bs qs (fields order initial i) (stale order initial old i)
    (fun j => (fields_length order initial i j).trans (hw j)) (stale_width order initial old b i hw ho)
    (by simp [blocks,Q]) (uniform_blocks Q B i payload hwidth) hb hq cb cq
  unfold MultiControlPrefixTranslationExecution.input MultiControlPrefixTranslationExecution.output at ht
  have hs : putWord S P (blocks Q (payload i)).flatten = S := source_fiber Q B n i source p payload hwidth hi
  rw [hs] at ht
  have hd : putWord D R (BlockRotationData.rotate (offset e seed order initial i) (blocks Q (payload i))).flatten =
      putWord dest q (outputPrefix e seed order initial b (i+1) payload) := by
    change putWord (putWord dest q (TranslationPreparedFamily.outputPrefix (offset e seed order initial) (radix^b) i payload))
      (q+((i*(radix^b*B) : ℕ) : ℤ))
      (BlockRotationData.rotate (offset e seed order initial i) (blocks (radix^b) (payload i))).flatten =
      putWord dest q (TranslationPreparedFamily.outputPrefix (offset e seed order initial) (radix^b) (i+1) payload)
    rw [← TranslationPreparedFamily.prefix_length (offset e seed order initial) (radix^b) B i payload hwidth,
      putWord_append_forward,TranslationPreparedFamily.prefix_succ]
  change putWord D R (BlockRotationData.rotate (MultiControlTranslationExecution.offset e (read seed (fields order initial i)))
    (blocks Q (payload i))).flatten = _ at hd
  rw [hd] at ht
  have hpos (z : ℤ) : z+(i : ℤ)*((radix : ℤ)^b*B)+(radix : ℤ)^b*B =
      z+((i+1 : ℕ) : ℤ)*((radix : ℤ)^b*B) := by push_cast; ring
  simpa only [state,S,D,P,R,Q,stale,MultiControlPrefixTranslationExecution.advance,← fields_succ,
    Nat.cast_mul,Nat.cast_pow,hpos] using ht

def program (e : Expr c) (order : List (Fin c)) (hne : order ≠ []) :=
  CountedLoopReuseAlphabet.program (MultiControlPrefixTranslationExecution.program (radix := radix) e order hne)

/-- Actual carry costs telescope across all prefix fields, including spectators. -/
theorem scheduler_sum_bound (order : List (Fin c)) (initial : Fin c → List (Fin radix)) (n : ℕ) :
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


/-- The loop executes every control update physically, with the exact sum of
carry costs and unchanged counted-loop descriptors at its endpoints. -/
theorem translate_hoare (e : Expr c) (seed : Fin c) (order : List (Fin c)) (hne : order ≠ []) (hnodup : order.Nodup)
    {b B n : ℕ} (hB : 0 < B) (source dest : ℤ → Fin 4) (p q : ℤ)
    (bs qs ns : List Bool) (initial old : Fin c → List (Fin radix))
    (hw : ∀ j, (initial j).length = b) (ho : ∀ j, (old j).length = b)
    (hb : Counter.value bs = B) (hq : Counter.value qs = radix^b) (hn : Counter.value ns = n)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (payload : ℕ → ℕ → List (Fin 4)) (hwidth : ∀ j y, (payload j y).length = B) :
    HoareTime (program e order hne)
      (fun v => v = CountedLoopReuseAlphabet.bank (state e seed order b B n source dest p q bs qs initial old payload 0)
        CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary ns) 1 1)
      (fun v => v = CountedLoopReuseAlphabet.bank (state e seed order b B n source dest p q bs qs initial old payload n)
        CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary ns) 1 1)
      ((∑ i ∈ Finset.range n, PrefixCounterData.stepCost (Fact.out : radix.Prime).two_le order (fields order initial i))+
        n*((13*leaves e+RadixLinearCombination.linearConstant e.erase+496)*(radix^b*B)+7)+7*ns.length+16) := by
  have hh := CountedLoopReuseAlphabet.loop_hoare (MultiControlPrefixTranslationExecution.program e order hne) ns n
    (state e seed order b B n source dest p q bs qs initial old payload)
    (fun i => (13*leaves e+RadixLinearCombination.linearConstant e.erase+496)*(radix^b*B)+1+
      PrefixCounterData.stepCost (Fact.out : radix.Prime).two_le order (fields order initial i)) hn
    (fun i hi => body_hoare e seed order hne hnodup hB hi source dest p q bs qs initial old hw ho hb hq cb cq payload hwidth)
  apply hh.consequence (fun _ h => h) (fun _ h => h)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,smul_eq_mul,Nat.mul_add]
  omega

/-- Uniformly linear payload work, plus the explicitly amortized initial carry potential. -/
theorem translate_hoare_linear (e : Expr c) (seed : Fin c) (order : List (Fin c)) (hne : order ≠ []) (hnodup : order.Nodup)
    {b B n : ℕ} (hB : 0 < B) (source dest : ℤ → Fin 4) (p q : ℤ)
    (bs qs ns : List Bool) (initial old : Fin c → List (Fin radix))
    (hw : ∀ j, (initial j).length = b) (ho : ∀ j, (old j).length = b)
    (hb : Counter.value bs = B) (hq : Counter.value qs = radix^b) (hn : Counter.value ns = n)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs) (cn : GrowingCounterData.Canonical ns)
    (payload : ℕ → ℕ → List (Fin 4)) (hwidth : ∀ j y, (payload j y).length = B) :
    HoareTime (program e order hne)
      (fun v => v = CountedLoopReuseAlphabet.bank (state e seed order b B n source dest p q bs qs initial old payload 0)
        CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary ns) 1 1)
      (fun v => v = CountedLoopReuseAlphabet.bank (state e seed order b B n source dest p q bs qs initial old payload n)
        CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary ns) 1 1)
      ((13*leaves e+RadixLinearCombination.linearConstant e.erase+510+4*order.length)*
        (fibers (radix^b) n payload).flatten.length+2*(∑ j, (initial j).length)+23) := by
  apply (translate_hoare e seed order hne hnodup hB source dest p q bs qs ns initial old hw ho hb hq hn cb cq payload hwidth).consequence
    (fun _ h => h) (fun _ h => h)
  rw [TranslationStream.source_length (radix^b) B n payload hwidth]
  have hs := scheduler_sum_bound order initial n
  have hns := GrowingCounterData.canonical_width ns cn
  have hl := Nat.log2_le_self (Counter.value ns)
  have hp : 1 ≤ radix^b := Nat.one_le_pow _ _ (by have := (Fact.out : radix.Prime).two_le; omega)
  have hvol : 1 ≤ radix^b*B := by nlinarith
  have hnvol : n ≤ n*(radix^b*B) := by nlinarith
  have htail := Nat.mul_le_mul_left (4*order.length+14) hnvol
  nlinarith

private theorem lex_nonempty (seed : Fin c) : List.finRange c ≠ [] := by
  intro h
  have hh := congrArg List.length h
  simp at hh
  have := seed.isLt
  omega

def lexProgram (e : Expr c) (seed : Fin c) := program (radix := radix) e (List.finRange c) (lex_nonempty seed)

/-- A full equal-width control cycle restores the physically shared words. -/
theorem fields_full_cycle (initial : Fin c → List (Fin radix)) (b : ℕ) (hw : ∀ j, (initial j).length = b) :
    fields (List.finRange c) initial (radix^(c*b)) = initial := by
  have hh := PrefixCounterData.full_cycle (Fact.out : radix.Prime).two_le initial
  simpa [fields,hw] using hh

/-- Complete equal-width control traversal is linear in the total physical
payload volume, including expression computation and actual carry scheduling. -/
theorem full_cycle_hoare (e : Expr c) (seed : Fin c) {b B n : ℕ} (hB : 0 < B)
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs ns : List Bool) (initial old : Fin c → List (Fin radix))
    (hw : ∀ j, (initial j).length = b) (ho : ∀ j, (old j).length = b) (hperiod : n = radix^(c*b))
    (hb : Counter.value bs = B) (hq : Counter.value qs = radix^b) (hn : Counter.value ns = n)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs) (cn : GrowingCounterData.Canonical ns)
    (payload : ℕ → ℕ → List (Fin 4)) (hwidth : ∀ j y, (payload j y).length = B) :
    HoareTime (lexProgram e seed)
      (fun v => v = CountedLoopReuseAlphabet.bank (state e seed (List.finRange c) b B n source dest p q bs qs initial old payload 0)
        CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary ns) 1 1)
      (fun v => v = CountedLoopReuseAlphabet.bank (state e seed (List.finRange c) b B n source dest p q bs qs initial old payload n)
        CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary ns) 1 1)
      ((13*leaves e+RadixLinearCombination.linearConstant e.erase+512+4*c)*
        (fibers (radix^b) n payload).flatten.length+23) := by
  have hh := translate_hoare_linear e seed (List.finRange c) (lex_nonempty seed) (List.nodup_finRange c)
    hB source dest p q bs qs ns initial old hw ho hb hq hn cb cq cn payload hwidth
  apply hh.consequence (fun _ h => h) (fun _ h => h)
  rw [TranslationStream.source_length (radix^b) B n payload hwidth,List.length_finRange]
  have hsum : (∑ j, (initial j).length) = c*b := by simp [hw]
  rw [hsum]
  have hbpow := RadixToBinaryData.width_le_power (Fact.out : radix.Prime).two_le (c*b)
  rw [← hperiod] at hbpow
  have hp : 1 ≤ radix^b := Nat.one_le_pow _ _ (by have := (Fact.out : radix.Prime).two_le; omega)
  have hvol : 1 ≤ radix^b*B := by nlinarith
  have hnvol : n ≤ n*(radix^b*B) := by nlinarith
  nlinarith

/-- Every emitted shift is the expression evaluated on the actual counter iterate. -/
theorem offset_value (e : Expr c) (he : RadixLinearCombination.Valid (q := radix) e.erase)
    (seed : Fin c) (order : List (Fin c)) (initial : Fin c → List (Fin radix)) (b i : ℕ)
    (hw : ∀ j, (initial j).length = b) :
    (offset e seed order initial i : ZMod (radix^b)) =
      RadixLinearCombination.valueMod b e.erase (read seed (fields order initial i)) :=
  MultiControlTranslationExecution.offset_value e he _ b
    (RadixLinearCombinationShared.read_width seed _ b (fun j => (fields_length order initial i j).trans (hw j)))

/-- Exact accumulated destination, including its unchanged encoded background. -/
theorem state_destination (e : Expr c) (seed : Fin c) (order : List (Fin c)) (b B n : ℕ)
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs : List Bool) (initial old : Fin c → List (Fin radix))
    (payload : ℕ → ℕ → List (Fin 4)) (i : ℕ) :
    (state e seed order b B n source dest p q bs qs initial old payload i).tape
      (Fin.natAdd (MultiControlTranslationExecution.ArithmeticTapes e) (11 : Fin 12)) =
      fun z => (RadixToBinary.binaryEncoding (q := radix)).encode
        (putWord dest q (outputPrefix e seed order initial b i payload) z) := by
  simp only [state,MultiControlPrefixTranslationExecution.bank,MultiControlTranslationExecution.bank,
    Tapes.append,Fin.addCases_right]
  rfl

/-- The scheduler's mathematical iterate is the actual shared control tape. -/
theorem state_control (e : Expr c) (seed : Fin c) (order : List (Fin c)) (b B n : ℕ)
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs : List Bool) (initial old : Fin c → List (Fin radix))
    (payload : ℕ → ℕ → List (Fin 4)) (i : ℕ) (j : Fin c) :
    let slot := Fin.castAdd 12 (Fin.castAdd (RadixLinearCombinationBinary.TapeCount e.erase) j)
    (state e seed order b B n source dest p q bs qs initial old payload i).head slot = 1 ∧
    (state e seed order b B n source dest p q bs qs initial old payload i).tape slot =
      MarkedRadixRefresh.source (fields order initial i j) := by
  simp [state,MultiControlPrefixTranslationExecution.bank,MultiControlTranslationExecution.bank,
    RadixLinearCombinationReuse.state,RadixLinearCombinationRefresh.controls,Tapes.append]

end IntegerMultBounds.Machine.MultiControlPrefixTranslationStream
