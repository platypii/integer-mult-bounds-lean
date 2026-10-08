import IntegerMultBounds.Machine.RationalTranslationStream

/-! A physical arbitrary-length family of D-fiber translations with one fixed
physical H control. This is the middle-spectator loop for heterogeneous
recursive layouts: its repetition count need not be a radix power. -/
namespace IntegerMultBounds.Machine.FixedControlTranslationStream
open TranslationStream (blocks fibers)
variable {radix : ℕ} [Fact radix.Prime]

/-- Both stored binary offset copies hold the last computed offset. -/
def descriptor (r : ℚ) (old : List Bool) (xs : List (Fin radix)) : ℕ → List Bool
  | 0 => old
  | _i+1 => RationalOffsetPrepare.result r xs

def offset (r : ℚ) (xs : List (Fin radix)) (_i : ℕ) : ℕ :=
  Counter.value (RationalOffsetPrepare.result r xs)

def outputPrefix (r : ℚ) (xs : List (Fin radix)) (n : ℕ)
    (payload : ℕ → ℕ → List (Fin 4)) : List (Fin 4) :=
  TranslationPreparedFamily.outputPrefix (offset r xs) (radix^xs.length) n payload

/-- Complete bank at a physical fiber boundary, including the unchanged physical radix control. -/
def state (r : ℚ) (B n : ℕ) (source dest : ℤ → Fin 4) (p q : ℤ)
    (bs qs old : List Bool) (xs : List (Fin radix)) (payload : ℕ → ℕ → List (Fin 4)) (i : ℕ) : Tapes 16 radix :=
  RationalTranslationExecution.bank
    (putWord source p (fibers (radix^xs.length) n payload).flatten)
    (putWord dest q (outputPrefix r xs i payload))
    (p+((i*(radix^xs.length*B) : ℕ) : ℤ)) (q+((i*(radix^xs.length*B) : ℕ) : ℤ))
    bs qs (descriptor r old xs i) (descriptor r old xs i) xs

private theorem blocks_uniform (Q B i : ℕ) (payload : ℕ → ℕ → List (Fin 4))
    (hwidth : ∀ i y, (payload i y).length = B) : BlockRotationData.Uniform B (blocks Q (payload i)) := by
  intro block hb
  obtain ⟨y,_,rfl⟩ := List.mem_map.mp hb
  exact hwidth i y

private theorem fiber_length (Q B i : ℕ) (payload : ℕ → ℕ → List (Fin 4))
    (hwidth : ∀ i y, (payload i y).length = B) : (blocks Q (payload i)).flatten.length = Q*B := by
  rw [BlockRotationData.uniform_volume B _ (blocks_uniform Q B i payload hwidth)]
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

private theorem descriptor_canonical (r : ℚ) (old : List Bool) (xs : List (Fin radix))
    (cold : GrowingCounterData.Canonical old) (i : ℕ) : GrowingCounterData.Canonical (descriptor r old xs i) := by
  cases i with
  | zero => exact cold
  | succ i => exact RationalOffsetPrepare.result_canonical r xs

private theorem descriptor_lt (r : ℚ) (old : List Bool) (xs : List (Fin radix))
    (hold : Counter.value old < radix^xs.length) (i : ℕ) :
    Counter.value (descriptor r old xs i) < radix^xs.length := by
  cases i with
  | zero => exact hold
  | succ i => simpa only [descriptor] using RationalOffsetPrepare.result_lt r xs

/-- Translation alone preserves the physical control throughout the loop. -/
def bodyProgram (r : ℚ) := RationalTranslationExecution.program (radix := radix) r

theorem body_hoare (r : ℚ) {B n i : ℕ} (hB : 0 < B) (hi : i < n)
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs old : List Bool) (xs : List (Fin radix))
    (hb : Counter.value bs = B) (hq : Counter.value qs = radix^xs.length)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (cold : GrowingCounterData.Canonical old) (hold : Counter.value old < radix^xs.length)
    (payload : ℕ → ℕ → List (Fin 4)) (hwidth : ∀ i y, (payload i y).length = B) :
    HoareTime (bodyProgram r)
      (fun v => v = state r B n source dest p q bs qs old xs payload i)
      (fun v => v = state r B n source dest p q bs qs old xs payload (i+1))
      (516*(radix^xs.length*B)) := by
  let Q := radix^xs.length
  let S := putWord source p (fibers Q n payload).flatten
  let D := putWord dest q (outputPrefix r xs i payload)
  let P := p+((i*(Q*B) : ℕ) : ℤ)
  let R := q+((i*(Q*B) : ℕ) : ℤ)
  have hc := descriptor_canonical r old xs cold i
  have hl := descriptor_lt r old xs hold i
  have ht := RationalTranslationExecution.translate_hoare_fiber r B hB S D P R
    (blocks Q (payload i)) bs qs (descriptor r old xs i) (descriptor r old xs i) xs
    (by simp [blocks,Q]) (blocks_uniform Q B i payload hwidth) hb (by simpa using hq) cb cq hc hc
    (by simpa using hl) (by simpa using hl)
  unfold RationalTranslationExecution.input RationalTranslationExecution.output at ht
  have hs : putWord S P (blocks Q (payload i)).flatten = S :=
    source_fiber Q B n i source p payload hwidth hi
  rw [hs] at ht
  have hd : putWord D R (BlockRotationData.rotate (offset r xs i) (blocks Q (payload i))).flatten =
      putWord dest q (outputPrefix r xs (i+1) payload) := by
    change putWord (putWord dest q (TranslationPreparedFamily.outputPrefix (offset r xs) (radix^xs.length) i payload))
      (q+((i*(radix^xs.length*B) : ℕ) : ℤ))
      (BlockRotationData.rotate (offset r xs i) (blocks (radix^xs.length) (payload i))).flatten =
      putWord dest q (TranslationPreparedFamily.outputPrefix (offset r xs) (radix^xs.length) (i+1) payload)
    rw [← TranslationPreparedFamily.prefix_length (offset r xs) (radix^xs.length) B i payload hwidth,
      putWord_append_forward,TranslationPreparedFamily.prefix_succ]
  change putWord D R (BlockRotationData.rotate (Counter.value (RationalOffsetPrepare.result r xs))
    (blocks Q (payload i))).flatten = _ at hd
  rw [hd] at ht
  have hpos (z : ℤ) : z+(i : ℤ)*((Q : ℤ)*B)+(Q : ℤ)*B =
      z+((i+1 : ℕ) : ℤ)*((Q : ℤ)*B) := by push_cast; ring
  simp only [Q,Nat.cast_pow] at hpos
  simpa only [bodyProgram,state,S,D,P,R,Q,descriptor,Nat.cast_mul,Nat.cast_pow,hpos] using ht

/-- One fixed counted machine around concrete computation and translation at stationary control. -/
def program (r : ℚ) := CountedLoopReuseAlphabet.program (bodyProgram (radix := radix) r)

theorem translate_hoare (r : ℚ) {B n : ℕ} (hB : 0 < B)
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs ns old : List Bool) (xs : List (Fin radix))
    (hb : Counter.value bs = B) (hq : Counter.value qs = radix^xs.length) (hn : Counter.value ns = n)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (cold : GrowingCounterData.Canonical old) (hold : Counter.value old < radix^xs.length)
    (payload : ℕ → ℕ → List (Fin 4)) (hwidth : ∀ i y, (payload i y).length = B) :
    HoareTime (program r)
      (fun v => v = CountedLoopReuseAlphabet.bank
        (state r B n source dest p q bs qs old xs payload 0)
        CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary ns) 1 1)
      (fun v => v = CountedLoopReuseAlphabet.bank
        (state r B n source dest p q bs qs old xs payload n)
        CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary ns) 1 1)
      (n*(516*(radix^xs.length*B)+6)+7*ns.length+16) := by
  have hh := CountedLoopReuseAlphabet.loop_hoare (bodyProgram r) ns n
    (state r B n source dest p q bs qs old xs payload) (fun _ => 516*(radix^xs.length*B)) hn
    (fun i hi => body_hoare r hB hi source dest p q bs qs old xs hb hq cb cq cold hold payload hwidth)
  have hcost : (∑ _i ∈ Finset.range n, 516*(radix^xs.length*B))+6*n+7*ns.length+16 =
      n*(516*(radix^xs.length*B)+6)+7*ns.length+16 := by
    simp only [Finset.sum_const,Finset.card_range,smul_eq_mul]
    ring
  simpa only [program,hcost] using hh

/-- Complete family runtime, measured against literal source volume, including
all offset computations, descriptor replacement and loop controls. -/
theorem translate_hoare_linear (r : ℚ) {B n : ℕ} (hB : 0 < B)
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs ns old : List Bool) (xs : List (Fin radix))
    (hb : Counter.value bs = B) (hq : Counter.value qs = radix^xs.length) (hn : Counter.value ns = n)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (cn : GrowingCounterData.Canonical ns) (cold : GrowingCounterData.Canonical old)
    (hold : Counter.value old < radix^xs.length) (payload : ℕ → ℕ → List (Fin 4))
    (hwidth : ∀ i y, (payload i y).length = B) :
    HoareTime (program r)
      (fun v => v = CountedLoopReuseAlphabet.bank
        (state r B n source dest p q bs qs old xs payload 0)
        CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary ns) 1 1)
      (fun v => v = CountedLoopReuseAlphabet.bank
        (state r B n source dest p q bs qs old xs payload n)
        CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary ns) 1 1)
      (529*(fibers (radix^xs.length) n payload).flatten.length+23) := by
  apply (translate_hoare r hB source dest p q bs qs ns old xs hb hq hn cb cq cold hold payload hwidth).consequence
    (fun _ h => h) (fun _ h => h) _
  rw [TranslationStream.source_length (radix^xs.length) B n payload hwidth]
  have hw := GrowingCounterData.canonical_width ns cn
  have hl := Nat.log2_le_self (Counter.value ns)
  have hp : 1 ≤ radix^xs.length := Nat.one_le_pow _ _ (by have := (Fact.out : radix.Prime).two_le; omega)
  have hbvol : 1 ≤ radix^xs.length*B := by nlinarith
  have hnvol : n ≤ n*(radix^xs.length*B) := by nlinarith
  nlinarith


end IntegerMultBounds.Machine.FixedControlTranslationStream
