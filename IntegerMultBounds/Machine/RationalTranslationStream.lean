import IntegerMultBounds.Machine.RationalTranslationExecution
import IntegerMultBounds.Machine.CountedLoopReuseAlphabet
import IntegerMultBounds.Machine.RadixCounter
import IntegerMultBounds.Machine.TranslationPreparedFamily

/-! Complete varying-offset translation over a single cyclic radix coordinate.
Each fiber computes its rational offset from the current physical control word,
executes translation, and physically increments that control word. An actual
arbitrary-alphabet binary-counted loop processes the consecutive fiber family.
The initial marked controls/workspace are explicit recurring-state inputs. -/
namespace IntegerMultBounds.Machine.RationalTranslationStream

open TranslationStream (blocks fibers)
variable {radix : ℕ} [Fact radix.Prime]

/-- The actual cyclic prefix-control word after i incrementer calls. -/
def control (xs : List (Fin radix)) (i : ℕ) : List (Fin radix) :=
  RadixCounterData.advance (Fact.out : radix.Prime).two_le i xs

@[simp] theorem control_length (xs : List (Fin radix)) (i : ℕ) : (control xs i).length = xs.length :=
  RadixCounterData.advance_length _ _ _

theorem control_succ (xs : List (Fin radix)) (i : ℕ) :
    control xs (i+1) = RadixCounterData.increment (Fact.out : radix.Prime).two_le (control xs i) := by
  have h (n : ℕ) (ys : List (Fin radix)) :
      RadixCounterData.advance (Fact.out : radix.Prime).two_le n
        (RadixCounterData.increment (Fact.out : radix.Prime).two_le ys) =
      RadixCounterData.increment (Fact.out : radix.Prime).two_le
        (RadixCounterData.advance (Fact.out : radix.Prime).two_le n ys) := by
    induction n generalizing ys with
    | zero => rfl
    | succ n ih => simpa only [RadixCounterData.advance] using ih (RadixCounterData.increment (Fact.out : radix.Prime).two_le ys)
  exact h i xs

/-- Both stored binary offset copies hold the last computed offset. -/
def descriptor (r : ℚ) (old : List Bool) (xs : List (Fin radix)) : ℕ → List Bool
  | 0 => old
  | i+1 => RationalOffsetPrepare.result r (control xs i)

def offset (r : ℚ) (xs : List (Fin radix)) (i : ℕ) : ℕ :=
  Counter.value (RationalOffsetPrepare.result r (control xs i))

def outputPrefix (r : ℚ) (xs : List (Fin radix)) (n : ℕ)
    (payload : ℕ → ℕ → List (Fin 4)) : List (Fin 4) :=
  TranslationPreparedFamily.outputPrefix (offset r xs) (radix^xs.length) n payload

/-- Complete bank at a physical fiber boundary, including live radix control. -/
def state (r : ℚ) (B n : ℕ) (source dest : ℤ → Fin 4) (p q : ℤ)
    (bs qs old : List Bool) (xs : List (Fin radix)) (payload : ℕ → ℕ → List (Fin 4)) (i : ℕ) : Tapes 16 radix :=
  RationalTranslationExecution.bank
    (putWord source p (fibers (radix^xs.length) n payload).flatten)
    (putWord dest q (outputPrefix r xs i payload))
    (p+((i*(radix^xs.length*B) : ℕ) : ℤ)) (q+((i*(radix^xs.length*B) : ℕ) : ℤ))
    bs qs (descriptor r old xs i) (descriptor r old xs i) (control xs i)

private def incrementPlacement : Fin (1+15) ≃ Fin 16 := Equiv.swap 0 15

def incrementProgram : Program 16 3 radix :=
  Placement.placed (RadixCounter.program (Fact.out : radix.Prime).two_le) incrementPlacement

private theorem increment_hoare (source dest : ℤ → Fin 4) (p q : ℤ)
    (bs qs supplied old : List Bool) (xs : List (Fin radix)) :
    HoareTime incrementProgram
      (fun v => v = RationalTranslationExecution.bank source dest p q bs qs supplied old xs)
      (fun v => v = RationalTranslationExecution.bank source dest p q bs qs supplied old
        (RadixCounterData.increment (Fact.out : radix.Prime).two_le xs))
      (2*RadixCounterData.carrySteps xs) := by
  have hc := RadixCounter.increment_hoare (Fact.out : radix.Prime).two_le MarkedWordCleanup.empty xs rfl
    (by simp [MarkedWordCleanup.empty,show (1:ℤ)+xs.length ≠ 0 by omega])
  have ha : Placement.active incrementPlacement (RationalTranslationExecution.bank source dest p q bs qs supplied old xs) =
      RadixCounter.tapes MarkedWordCleanup.empty xs := by
    unfold Placement.active incrementPlacement RationalTranslationExecution.bank Tapes.append
    congr 1 <;> funext i <;> fin_cases i <;> rfl
  have hf : Placement.active incrementPlacement
      (RationalTranslationExecution.bank source dest p q bs qs supplied old (RadixCounterData.increment (Fact.out : radix.Prime).two_le xs)) =
      RadixCounter.tapes MarkedWordCleanup.empty (RadixCounterData.increment (Fact.out : radix.Prime).two_le xs) := by
    unfold Placement.active incrementPlacement RationalTranslationExecution.bank Tapes.append
    congr 1 <;> funext i <;> fin_cases i <;> rfl
  have he : Placement.extra incrementPlacement (RationalTranslationExecution.bank source dest p q bs qs supplied old xs) =
      Placement.extra incrementPlacement
        (RationalTranslationExecution.bank source dest p q bs qs supplied old (RadixCounterData.increment (Fact.out : radix.Prime).two_le xs)) := by
    unfold Placement.extra incrementPlacement RationalTranslationExecution.bank Tapes.append
    congr 1
    funext i
    fin_cases i <;> rfl
  apply (Placement.hoare_at hc incrementPlacement _ ha).consequence (fun _ h => h) _ le_rfl
  rintro v ⟨w,rfl,rfl⟩
  rw [Placement.replace,he,← hf]
  exact Placement.view _ _

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
  | succ i => exact RationalOffsetPrepare.result_canonical r (control xs i)

private theorem descriptor_lt (r : ℚ) (old : List Bool) (xs : List (Fin radix))
    (hold : Counter.value old < radix^xs.length) (i : ℕ) :
    Counter.value (descriptor r old xs i) < radix^xs.length := by
  cases i with
  | zero => exact hold
  | succ i => simpa only [descriptor,control_length] using RationalOffsetPrepare.result_lt r (control xs i)

/-- Translate one fiber using the current physical control, then increment it. -/
def bodyProgram (r : ℚ) : Program 16 ((((4+((2+(2*r.num.natAbs+r.den+1)+2)+18+6))+7)+217)+3) radix :=
  seq (RationalTranslationExecution.program r) incrementProgram

theorem body_hoare (r : ℚ) {B n i : ℕ} (hB : 0 < B) (hi : i < n)
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs old : List Bool) (xs : List (Fin radix))
    (hb : Counter.value bs = B) (hq : Counter.value qs = radix^xs.length)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (cold : GrowingCounterData.Canonical old) (hold : Counter.value old < radix^xs.length)
    (payload : ℕ → ℕ → List (Fin 4)) (hwidth : ∀ i y, (payload i y).length = B) :
    HoareTime (bodyProgram r)
      (fun v => v = state r B n source dest p q bs qs old xs payload i)
      (fun v => v = state r B n source dest p q bs qs old xs payload (i+1))
      (521*(radix^xs.length*B)) := by
  let Q := radix^xs.length
  let S := putWord source p (fibers Q n payload).flatten
  let D := putWord dest q (outputPrefix r xs i payload)
  let P := p+((i*(Q*B) : ℕ) : ℤ)
  let R := q+((i*(Q*B) : ℕ) : ℤ)
  have hc := descriptor_canonical r old xs cold i
  have hl := descriptor_lt r old xs hold i
  have ht := RationalTranslationExecution.translate_hoare_fiber r B hB S D P R
    (blocks Q (payload i)) bs qs (descriptor r old xs i) (descriptor r old xs i) (control xs i)
    (by simp [blocks,Q]) (blocks_uniform Q B i payload hwidth) hb (by simpa using hq) cb cq hc hc
    (by simpa using hl) (by simpa using hl)
  simp only [control_length] at ht
  unfold RationalTranslationExecution.input RationalTranslationExecution.output at ht
  simp only [control_length] at ht
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
  change putWord D R (BlockRotationData.rotate (Counter.value (RationalOffsetPrepare.result r (control xs i)))
    (blocks Q (payload i))).flatten = _ at hd
  rw [hd] at ht
  have hn := increment_hoare S (putWord dest q (outputPrefix r xs (i+1) payload))
    (P+Q*B) (R+Q*B) bs qs (RationalOffsetPrepare.result r (control xs i))
    (RationalOffsetPrepare.result r (control xs i)) (control xs i)
  have hh := ht.seq hn
  have hpos (z : ℤ) : z+(i : ℤ)*((Q : ℤ)*B)+(Q : ℤ)*B =
      z+((i+1 : ℕ) : ℤ)*((Q : ℤ)*B) := by push_cast; ring
  have hh' : HoareTime (bodyProgram r)
      (fun v => v = state r B n source dest p q bs qs old xs payload i)
      (fun v => v = state r B n source dest p q bs qs old xs payload (i+1))
      (516*(Q*B)+1+2*RadixCounterData.carrySteps (control xs i)) := by
    simpa only [bodyProgram,state,S,D,P,R,descriptor,← control_succ,Nat.cast_mul,hpos] using hh
  apply hh'.consequence (fun _ h => h) (fun _ h => h) _
  have hcsteps := (RadixCounterData.carrySteps_bounds (control xs i)).2
  rw [control_length] at hcsteps
  have hw := RadixToBinaryData.width_le_power (Fact.out : radix.Prime).two_le xs.length
  have hp : 1 ≤ Q := Nat.one_le_pow _ _ (by have := (Fact.out : radix.Prime).two_le; omega)
  have hm : Q ≤ Q*B := by nlinarith
  change 516*(Q*B)+1+2*RadixCounterData.carrySteps (control xs i) ≤ 521*(Q*B)
  dsimp [Q] at *
  omega

/-- One fixed counted machine around concrete computation, translation and control increment. -/
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
      (n*(521*(radix^xs.length*B)+6)+7*ns.length+16) := by
  have hh := CountedLoopReuseAlphabet.loop_hoare (bodyProgram r) ns n
    (state r B n source dest p q bs qs old xs payload) (fun _ => 521*(radix^xs.length*B)) hn
    (fun i hi => body_hoare r hB hi source dest p q bs qs old xs hb hq cb cq cold hold payload hwidth)
  have hcost : (∑ _i ∈ Finset.range n, 521*(radix^xs.length*B))+6*n+7*ns.length+16 =
      n*(521*(radix^xs.length*B)+6)+7*ns.length+16 := by
    simp only [Finset.sum_const,Finset.card_range,smul_eq_mul]
    ring
  simpa only [program,hcost] using hh

/-- Complete family runtime, measured against literal source volume, including
all offset computations, increments, descriptor replacement and loop controls. -/
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
      (534*(fibers (radix^xs.length) n payload).flatten.length+23) := by
  apply (translate_hoare r hB source dest p q bs qs ns old xs hb hq hn cb cq cold hold payload hwidth).consequence
    (fun _ h => h) (fun _ h => h) _
  rw [TranslationStream.source_length (radix^xs.length) B n payload hwidth]
  have hw := GrowingCounterData.canonical_width ns cn
  have hl := Nat.log2_le_self (Counter.value ns)
  have hp : 1 ≤ radix^xs.length := Nat.one_le_pow _ _ (by have := (Fact.out : radix.Prime).two_le; omega)
  have hbvol : 1 ≤ radix^xs.length*B := by nlinarith
  have hnvol : n ≤ n*(radix^xs.length*B) := by nlinarith
  nlinarith

/-- The current physical radix word is the cyclic integer value after i increments. -/
theorem control_value (xs : List (Fin radix)) (i : ℕ) :
    RadixDigits.value (control xs i) = (RadixDigits.value xs+i)%radix^xs.length :=
  RadixCounterData.advance_value _ _ _

/-- Each actual rotation offset is the fixed rational multiple of the current
cyclic prefix coordinate, rather than an independently supplied descriptor. -/
theorem offset_value (r : ℚ) (hden : r.den < radix) (xs : List (Fin radix)) (i : ℕ) :
    (offset r xs i : ZMod (radix^xs.length)) =
      Swap.Modular.ratMod (radix^xs.length) r * ((RadixDigits.value xs+i : ℕ) : ZMod (radix^xs.length)) := by
  have hh := RationalOffsetPrepare.result_value r hden (control xs i)
  generalize hlen : (control xs i).length = b at hh
  have hb : b = xs.length := hlen.symm.trans (control_length xs i)
  rw [hb] at hh
  simpa only [offset,control_value,ZMod.natCast_mod] using hh

/-- Starting from a zero prefix, the control completes a literal full residue cycle. -/
theorem control_full_cycle (b : ℕ) :
    control (RadixCounterData.zeros (Fact.out : radix.Prime).two_le b) (radix^b) =
      RadixCounterData.zeros (Fact.out : radix.Prime).two_le b :=
  RadixCounterData.full_cycle _ _

/-- The full output has exactly the original physical length. -/
theorem output_length (r : ℚ) (B n : ℕ) (xs : List (Fin radix))
    (payload : ℕ → ℕ → List (Fin 4)) (hwidth : ∀ i y, (payload i y).length = B) :
    (outputPrefix r xs n payload).length = (fibers (radix^xs.length) n payload).flatten.length := by
  rw [TranslationStream.source_length (radix^xs.length) B n payload hwidth]
  exact TranslationPreparedFamily.prefix_length _ _ _ _ _ hwidth

end IntegerMultBounds.Machine.RationalTranslationStream
