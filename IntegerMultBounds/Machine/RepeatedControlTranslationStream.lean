import IntegerMultBounds.Machine.RepeatedControlTranslationExecution

/-! Arbitrary-prefix execution of heterogeneous controlled shifts. The inner
count C repeats D translations at fixed H; the outer count n increments H once
per entire C group. Choosing n=L*q^b handles arbitrary outer prefix cardinality
L and returns the control to zero. Both counts are runtime binary descriptors;
program/tape counts are independent of them. -/
namespace IntegerMultBounds.Machine.RepeatedControlTranslationStream
open TranslationStream (fibers)
open RationalTranslationStream (control descriptor control_length control_succ)
variable {radix : ℕ} [Fact radix.Prime]

def groups (Q C n : ℕ) (payload : ℕ → ℕ → ℕ → List (Fin 4)) : List (List (Fin 4)) :=
  (List.range n).map (fun i => (fibers Q C (payload i)).flatten)

def outputPrefix (r : ℚ) (xs : List (Fin radix)) (C n : ℕ)
    (payload : ℕ → ℕ → ℕ → List (Fin 4)) : List (Fin 4) :=
  ((List.range n).map (fun i => FixedControlTranslationStream.outputPrefix r (control xs i) C (payload i))).flatten

def state (r : ℚ) (B C n : ℕ) (source dest : ℤ → Fin 4) (p q : ℤ)
    (bs qs cs old : List Bool) (xs : List (Fin radix))
    (payload : ℕ → ℕ → ℕ → List (Fin 4)) (i : ℕ) :=
  RepeatedControlTranslationExecution.bank
    (putWord source p (groups (radix^xs.length) C n payload).flatten)
    (putWord dest q (outputPrefix r xs C i payload))
    (p+((i*(C*(radix^xs.length*B)) : ℕ) : ℤ)) (q+((i*(C*(radix^xs.length*B)) : ℕ) : ℤ))
    bs qs cs (descriptor r old xs i) (control xs i)

private theorem groups_uniform (Q B C n : ℕ) (payload : ℕ → ℕ → ℕ → List (Fin 4))
    (hwidth : ∀ i c y, (payload i c y).length = B) :
    BlockRotationData.Uniform (C*(Q*B)) (groups Q C n payload) := by
  intro word hw
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hw
  exact TranslationStream.source_length Q B C (payload i) (hwidth i)

theorem source_length (Q B C n : ℕ) (payload : ℕ → ℕ → ℕ → List (Fin 4))
    (hwidth : ∀ i c y, (payload i c y).length = B) :
    (groups Q C n payload).flatten.length = n*(C*(Q*B)) := by
  rw [BlockRotationData.uniform_volume (C*(Q*B)) _ (groups_uniform Q B C n payload hwidth)]
  simp [groups]

private theorem source_group (Q B C n i : ℕ) (source : ℤ → Fin 4) (p : ℤ)
    (payload : ℕ → ℕ → ℕ → List (Fin 4)) (hwidth : ∀ i c y, (payload i c y).length = B) (hi : i < n) :
    putWord (putWord source p (groups Q C n payload).flatten) (p+((i*(C*(Q*B)) : ℕ) : ℤ))
      (fibers Q C (payload i)).flatten = putWord source p (groups Q C n payload).flatten := by
  have hh := FiberShift.source_fiber source p (groups Q C n payload) (C*(Q*B)) i
    (groups_uniform Q B C n payload hwidth) (by simpa [groups] using hi)
  simpa [groups] using hh

theorem output_length (r : ℚ) (xs : List (Fin radix)) (B C n : ℕ)
    (payload : ℕ → ℕ → ℕ → List (Fin 4)) (hwidth : ∀ i c y, (payload i c y).length = B) :
    (outputPrefix r xs C n payload).length = n*(C*(radix^xs.length*B)) := by
  unfold outputPrefix
  rw [BlockRotationData.uniform_volume (C*(radix^xs.length*B))]
  · simp
  · intro word hw
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hw
    unfold FixedControlTranslationStream.outputPrefix
    rw [TranslationPreparedFamily.prefix_length _ _ B _ _ (hwidth i),control_length]

theorem output_succ (r : ℚ) (xs : List (Fin radix)) (C n : ℕ)
    (payload : ℕ → ℕ → ℕ → List (Fin 4)) :
    outputPrefix r xs C (n+1) payload = outputPrefix r xs C n payload ++
      FixedControlTranslationStream.outputPrefix r (control xs n) C (payload n) := by
  simp [outputPrefix,List.range_succ,List.map_append,List.flatten_append]

private theorem descriptor_canonical (r : ℚ) (old : List Bool) (xs : List (Fin radix))
    (cold : GrowingCounterData.Canonical old) (i : ℕ) : GrowingCounterData.Canonical (descriptor r old xs i) := by
  cases i with
  | zero => exact cold
  | succ i => exact RationalOffsetPrepare.result_canonical r (control xs i)

private theorem descriptor_lt (r : ℚ) (old : List Bool) (xs : List (Fin radix))
    (hold : Counter.value old < radix^xs.length) (i : ℕ) :
    Counter.value (descriptor r old xs i) < radix^xs.length := by
  cases i with
  | zero => exact hold
  | succ i => simpa only [descriptor,control_length] using RationalOffsetPrepare.result_lt r (control xs i)

theorem body_hoare (r : ℚ) {B C n i : ℕ} (hB : 0 < B) (hC : 0 < C) (hi : i < n)
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs cs old : List Bool) (xs : List (Fin radix))
    (hb : Counter.value bs = B) (hq : Counter.value qs = radix^xs.length) (hc : Counter.value cs = C)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (cc : GrowingCounterData.Canonical cs) (cold : GrowingCounterData.Canonical old)
    (hold : Counter.value old < radix^xs.length)
    (payload : ℕ → ℕ → ℕ → List (Fin 4)) (hwidth : ∀ i c y, (payload i c y).length = B) :
    HoareTime (RepeatedControlTranslationExecution.program r)
      (fun v => v = state r B C n source dest p q bs qs cs old xs payload i)
      (fun v => v = state r B C n source dest p q bs qs cs old xs payload (i+1))
      (557*(C*(radix^xs.length*B))) := by
  let Q := radix^xs.length
  let S := putWord source p (groups Q C n payload).flatten
  let D := putWord dest q (outputPrefix r xs C i payload)
  let P := p+((i*(C*(Q*B)) : ℕ) : ℤ)
  let R := q+((i*(C*(Q*B)) : ℕ) : ℤ)
  have ht := RepeatedControlTranslationExecution.group_hoare r hB hC S D P R bs qs cs
    (descriptor r old xs i) (control xs i) hb (by simpa using hq) hc cb cq cc
    (descriptor_canonical r old xs cold i) (by simpa using descriptor_lt r old xs hold i)
    (payload i) (hwidth i)
  simp only [control_length] at ht
  have hs : putWord S P (fibers Q C (payload i)).flatten = S :=
    source_group Q B C n i source p payload hwidth hi
  rw [hs] at ht
  have hd : putWord D R (FixedControlTranslationStream.outputPrefix r (control xs i) C (payload i)) =
      putWord dest q (outputPrefix r xs C (i+1) payload) := by
    change putWord (putWord dest q (outputPrefix r xs C i payload))
      (q+((i*(C*(radix^xs.length*B)) : ℕ) : ℤ))
      (FixedControlTranslationStream.outputPrefix r (control xs i) C (payload i)) = _
    rw [← output_length r xs B C i payload hwidth,putWord_append_forward,output_succ]
  rw [hd] at ht
  have hpos (z : ℤ) : z+(i : ℤ)*((C : ℤ)*((Q : ℤ)*B))+(C : ℤ)*((Q : ℤ)*B) =
      z+((i+1 : ℕ) : ℤ)*((C : ℤ)*((Q : ℤ)*B)) := by push_cast; ring
  simp only [Q,Nat.cast_pow] at hpos
  simpa only [state,S,D,P,R,Q,descriptor,← control_succ,Nat.cast_mul,Nat.cast_pow,hpos] using ht

/-- Twenty physical tapes, with two independent restored counted-loop banks. -/
def program (r : ℚ) := CountedLoopReuseAlphabet.program (RepeatedControlTranslationExecution.program (radix := radix) r)

theorem stream_hoare (r : ℚ) {B C n : ℕ} (hB : 0 < B) (hC : 0 < C)
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs cs ns old : List Bool) (xs : List (Fin radix))
    (hb : Counter.value bs = B) (hq : Counter.value qs = radix^xs.length)
    (hc : Counter.value cs = C) (hn : Counter.value ns = n)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (cc : GrowingCounterData.Canonical cs) (cn : GrowingCounterData.Canonical ns)
    (cold : GrowingCounterData.Canonical old) (hold : Counter.value old < radix^xs.length)
    (payload : ℕ → ℕ → ℕ → List (Fin 4)) (hwidth : ∀ i c y, (payload i c y).length = B) :
    HoareTime (program r)
      (fun v => v = CountedLoopReuseAlphabet.bank (state r B C n source dest p q bs qs cs old xs payload 0)
        CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary ns) 1 1)
      (fun v => v = CountedLoopReuseAlphabet.bank (state r B C n source dest p q bs qs cs old xs payload n)
        CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary ns) 1 1)
      (570*(n*(C*(radix^xs.length*B)))+23) := by
  have hh := CountedLoopReuseAlphabet.loop_hoare (RepeatedControlTranslationExecution.program r) ns n
    (state r B C n source dest p q bs qs cs old xs payload) (fun _ => 557*(C*(radix^xs.length*B))) hn
    (fun i hi => body_hoare r hB hC hi source dest p q bs qs cs old xs hb hq hc cb cq cc cold hold payload hwidth)
  apply hh.consequence (fun _ h => h) (fun _ h => h) ?_
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul]
  have hw := GrowingCounterData.canonical_width ns cn
  rw [hn] at hw
  have hl := Nat.log2_le_self n
  have hQ : 0 < radix^xs.length := pow_pos (Fact.out : radix.Prime).pos _
  have hv : 1 ≤ C*(radix^xs.length*B) := Nat.mul_pos hC (Nat.mul_pos hQ hB)
  have hvn := Nat.mul_le_mul_left n hv
  nlinarith

private theorem advance_add {q : ℕ} (hq : 2 ≤ q) (n m : ℕ) (xs : List (Fin q)) :
    RadixCounterData.advance hq (n+m) xs =
      RadixCounterData.advance hq n (RadixCounterData.advance hq m xs) := by
  induction m generalizing xs with
  | zero => simp [RadixCounterData.advance]
  | succ m ih =>
    change RadixCounterData.advance hq (n+m) (RadixCounterData.increment hq xs) = _
    exact ih (RadixCounterData.increment hq xs)

/-- Any number L of complete H cycles restores the original zero control. -/
theorem control_prefix_cycles (b L : ℕ) :
    control (RadixCounterData.zeros (Fact.out : radix.Prime).two_le b) (L*(radix^b)) =
      RadixCounterData.zeros (Fact.out : radix.Prime).two_le b := by
  unfold RationalTranslationStream.control
  induction L with
  | zero => simp [RadixCounterData.advance]
  | succ L ih =>
    rw [Nat.succ_mul,advance_add,RadixCounterData.full_cycle]
    exact ih

end IntegerMultBounds.Machine.RepeatedControlTranslationStream
