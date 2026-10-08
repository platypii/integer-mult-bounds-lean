import IntegerMultBounds.Machine.MultiControlPrefixTranslationBootstrap
import IntegerMultBounds.Machine.PrefixCounterInitPlacement

/-! Physical generation of the common radix control bank from blank fields.
Each width is read from a canonical binary descriptor by PrefixCounterInit;
its generated fields are statically shared with the actual multi-control stream.
All initializer clocks, descriptors and spare tapes remain exact frames. -/
namespace IntegerMultBounds.Machine.MultiControlPrefixTranslationInit

open RadixLinearCombinationRefresh (Expr leaves)
open PrefixCounterInitPlacement (handoff extras)
variable {c radix : ℕ} [Fact radix.Prime]

abbrev FrameCount (e : Expr c) := RadixLinearCombinationBinary.TapeCount e.erase+14

def streamPlacement (e : Expr c) : Fin (c+FrameCount e) ≃ Fin (MultiControlPrefixTranslationBootstrap.TapeCount e) :=
  finCongr (by
    unfold FrameCount MultiControlPrefixTranslationBootstrap.TapeCount MultiControlTranslationExecution.TapeCount
      MultiControlTranslationExecution.ArithmeticTapes RadixLinearCombinationShared.TapeCount
    omega)

def initial (b : ℕ) : Fin c → List (Fin radix) := fun _ => RadixCounterData.zeros (Fact.out : radix.Prime).two_le b

@[simp] theorem initial_length (b : ℕ) (i : Fin c) : (initial (radix := radix) b i).length = b := by simp [initial]

private theorem active_initial (e : Expr c) (seed : Fin c) (b n : ℕ) (source dest : ℤ → Fin 4) (p q : ℤ)
    (bs qs ns : List Bool) (payload : ℕ → ℕ → List (Fin 4)) :
    Placement.active (streamPlacement e)
      (MultiControlPrefixTranslationBootstrap.input e seed b n source dest p q bs qs ns (initial (radix := radix) b) payload) =
      PrefixCounter.tapes (fun _ => RadixZeroFill.radixEmpty) (initial (radix := radix) b) := by
  unfold Placement.active MultiControlPrefixTranslationBootstrap.input Tapes.reindex
  apply congrArg₂ Tapes.mk
  · funext i
    change ((RadixLinearCombinationBootstrap.input e (MultiControlPrefixTranslationExecution.read seed (initial (radix := radix) b))).append _).head
      (Fin.castAdd 14 (Fin.castAdd (RadixLinearCombinationBinary.TapeCount e.erase) i)) = _
    simp [Tapes.append,RadixLinearCombinationBootstrap.input,RadixLinearCombinationRefresh.controls]
  · funext i
    change ((RadixLinearCombinationBootstrap.input e (MultiControlPrefixTranslationExecution.read seed (initial (radix := radix) b))).append _).tape
      (Fin.castAdd 14 (Fin.castAdd (RadixLinearCombinationBinary.TapeCount e.erase) i)) = _
    simp only [Tapes.append,Fin.addCases_left,RadixLinearCombinationBootstrap.input,RadixLinearCombinationRefresh.controls,
      RadixLinearCombinationShared.read_at]
    rfl

def program (e : Expr c) (seed : Fin c) :=
  PrefixCounterInitPlacement.program (Fact.out : radix.Prime).two_le
    (MultiControlPrefixTranslationBootstrap.lexProgram (radix := radix) e seed) (streamPlacement e)

def input (e : Expr c) (seed : Fin c) (b n : ℕ) (ws : Fin c → List Bool)
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs ns : List Bool) (payload : ℕ → ℕ → List (Fin 4)) :=
  (PrefixCounterInit.input (q := radix) c ws).append
    (Placement.extra (streamPlacement e)
      (MultiControlPrefixTranslationBootstrap.input e seed b n source dest p q bs qs ns (initial (radix := radix) b) payload))

def streamOutput (e : Expr c) (seed : Fin c) (b B n : ℕ) (source dest : ℤ → Fin 4) (p q : ℤ)
    (bs qs ns : List Bool) (payload : ℕ → ℕ → List (Fin 4)) :=
  CountedLoopReuseAlphabet.bank
    (MultiControlPrefixTranslationStream.state e seed (List.finRange c) b B n source dest p q bs qs (initial (radix := radix) b) (initial (radix := radix) b) payload n)
    CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary ns) 1 1

def output (e : Expr c) (seed : Fin c) (b B n : ℕ) (ws : Fin c → List Bool)
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs ns : List Bool) (payload : ℕ → ℕ → List (Fin 4)) :=
  Placement.replace (handoff (streamPlacement e))
    ((PrefixCounterInit.output (Fact.out : radix.Prime).two_le c ws (fun _ => b)).append
      (Placement.extra (streamPlacement e)
        (MultiControlPrefixTranslationBootstrap.input e seed b n source dest p q bs qs ns (initial (radix := radix) b) payload)))
    (streamOutput (radix := radix) e seed b B n source dest p q bs qs ns payload)

/-- The active output is exactly the complete executed counted-stream bank. -/
theorem output_active (e : Expr c) (seed : Fin c) (b B n : ℕ) (ws : Fin c → List Bool)
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs ns : List Bool) (payload : ℕ → ℕ → List (Fin 4)) :
    Placement.active (handoff (streamPlacement e)) (output (radix := radix) e seed b B n ws source dest p q bs qs ns payload) =
      streamOutput e seed b B n source dest p q bs qs ns payload := Placement.active_replace _ _ _

/-- All initializer complement tapes remain exactly as the real initializer left
 them, including immutable width descriptors, cleaned clocks and the spare. -/
theorem output_initializer_frame (e : Expr c) (seed : Fin c) (b B n : ℕ) (ws : Fin c → List Bool)
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs ns : List Bool) (payload : ℕ → ℕ → List (Fin 4)) :
    Placement.extra (handoff (streamPlacement e)) (output (radix := radix) e seed b B n ws source dest p q bs qs ns payload) =
      Placement.extra (handoff (streamPlacement e))
        ((PrefixCounterInit.output (Fact.out : radix.Prime).two_le c ws (fun _ => b)).append
          (Placement.extra (streamPlacement e)
            (MultiControlPrefixTranslationBootstrap.input e seed b n source dest p q bs qs ns (initial (radix := radix) b) payload))) :=
  Placement.extra_replace _ _ _

/-- No radix controls, work sentinels, stale sources or arithmetic results are
supplied. Every such tape is initialized by the composed physical machine. -/
theorem full_cycle_hoare (e : Expr c) (seed : Fin c) {b B n : ℕ} (hB : 0 < B) (ws : Fin c → List Bool)
    (hw : ∀ j, Counter.value (ws j) = b) (cw : ∀ j, GrowingCounterData.Canonical (ws j))
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs ns : List Bool) (hperiod : n = radix^(c*b))
    (hb : Counter.value bs = B) (hq : Counter.value qs = radix^b) (hn : Counter.value ns = n)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs) (cn : GrowingCounterData.Canonical ns)
    (payload : ℕ → ℕ → List (Fin 4)) (hwidth : ∀ j y, (payload j y).length = B) :
    HoareTime (program (radix := radix) e seed) (fun v => v = input e seed b n ws source dest p q bs qs ns payload)
      (fun v => v = output e seed b B n ws source dest p q bs qs ns payload)
      (15*(c*b)+29*c+(28*leaves e+2*RadixLinearCombination.linearConstant e.erase+552+4*c)*
        (TranslationStream.fibers (radix^b) n payload).flatten.length+27) := by
  have hs := MultiControlPrefixTranslationBootstrap.full_cycle_hoare e seed hB source dest p q bs qs ns (initial (radix := radix) b)
    (initial_length b) hperiod hb hq hn cb cq cn payload hwidth
  have hh := PrefixCounterInitPlacement.initialize_then (Fact.out : radix.Prime).two_le (streamPlacement e) ws
    (fun _ => b) hw cw _ _ (active_initial e seed b n source dest p q bs qs ns payload) hs
  apply hh.consequence (fun _ h => h) (fun _ h => h)
  simp
  omega

/-- Even field generation is absorbed into the complete physical payload volume. -/
theorem full_cycle_hoare_linear (e : Expr c) (seed : Fin c) {b B n : ℕ} (hB : 0 < B) (ws : Fin c → List Bool)
    (hw : ∀ j, Counter.value (ws j) = b) (cw : ∀ j, GrowingCounterData.Canonical (ws j))
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs ns : List Bool) (hperiod : n = radix^(c*b))
    (hb : Counter.value bs = B) (hq : Counter.value qs = radix^b) (hn : Counter.value ns = n)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs) (cn : GrowingCounterData.Canonical ns)
    (payload : ℕ → ℕ → List (Fin 4)) (hwidth : ∀ j y, (payload j y).length = B) :
    HoareTime (program (radix := radix) e seed) (fun v => v = input e seed b n ws source dest p q bs qs ns payload)
      (fun v => v = output e seed b B n ws source dest p q bs qs ns payload)
      ((28*leaves e+2*RadixLinearCombination.linearConstant e.erase+594+33*c)*
        (TranslationStream.fibers (radix^b) n payload).flatten.length) := by
  apply (full_cycle_hoare e seed hB ws hw cw source dest p q bs qs ns hperiod hb hq hn cb cq cn payload hwidth).consequence
    (fun _ h => h) (fun _ h => h)
  rw [TranslationStream.source_length (radix^b) B n payload hwidth]
  have hwpow := RadixToBinaryData.width_le_power (Fact.out : radix.Prime).two_le (c*b)
  rw [← hperiod] at hwpow
  have hp : 1 ≤ radix^b := Nat.one_le_pow _ _ (by have := (Fact.out : radix.Prime).two_le; omega)
  have hnp : 1 ≤ n := by rw [hperiod]; exact Nat.one_le_pow _ _ (by have := (Fact.out : radix.Prime).two_le; omega)
  have hv : n ≤ n*(radix^b*B) := Nat.le_mul_of_pos_right _ (Nat.mul_pos (by omega) hB)
  have hm := Nat.mul_le_mul_left (29*c+27) (hnp.trans hv)
  nlinarith

omit [Fact radix.Prime] in
/-- Initially every generated field tape itself is entirely blank, head zero. -/
theorem initial_field_blank (ws : Fin c → List Bool) (i : Fin c) :
    (PrefixCounterInit.input (q := radix) c ws).head (PrefixCounterInit.fieldSlot c i) = 0 ∧
    (PrefixCounterInit.input (q := radix) c ws).tape (PrefixCounterInit.fieldSlot c i) = (fun _ => blank) := by
  induction c with
  | zero => exact Fin.elim0 i
  | succ c ih =>
    induction i using Fin.cases with
    | zero => exact ⟨rfl,rfl⟩
    | succ i =>
      simp only [PrefixCounterInit.input,PrefixCounterInit.fieldSlot_succ,Tapes.append,Fin.addCases_right]
      exact ih (fun j => ws j.succ) i

end IntegerMultBounds.Machine.MultiControlPrefixTranslationInit
