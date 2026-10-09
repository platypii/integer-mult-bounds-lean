import IntegerMultBounds.Machine.ButterflyRecordEmit
import IntegerMultBounds.Machine.ButterflyGuard

/-! One complete paired coefficient record: extract all four serialized fields,
compute the exact butterfly, erase the extracted inputs, and emit both complex
outputs. All forty-eight private tapes return blank for the next record. -/
namespace IntegerMultBounds.Machine.ButterflyRecord
noncomputable section
open DelimitedRadixRecord (Context)
open ButterflyRecordRead (components afterStreams)
open ButterflySigned (signedValue complexValue)

def arithmetic := RawLinearCombinationCleanup.prepend ButterflyNumerator.program 4
def program := seq (seq (seq ButterflyRecordRead.program arithmetic)
  ButterflyRecordOutputData.program) ButterflyRecordEmit.program

def output (a b : Context 2) (out : Fin 2 → ℤ → Fin 6) (pos : Fin 2 → ℤ) :=
  ButterflyRecordEmit.output (afterStreams a b out pos) (fun i => ButterflyNumerator.words i (components a b))

theorem component_width (a b : Context 2) (w : ℕ)
    (ha : a.re.length=w ∧ a.im.length=w) (hb : b.re.length=w ∧ b.im.length=w) :
    ∀ i,(components a b i).length=w := by
  intro i
  rcases i with _|i
  · exact ha.1
  rcases i with _|i
  · exact ha.2
  rcases i with _|i
  · exact hb.1
  · exact hb.2

/-- The same fixed machine handles every record and every coefficient width. -/
theorem runs (a b : Context 2) (out : Fin 2 → ℤ → Fin 6) (pos : Fin 2 → ℤ) (w : ℕ)
    (ha : a.re.length=w ∧ a.im.length=w) (hb : b.re.length=w ∧ b.im.length=w) :
    HoareTime program (fun v => v=ButterflyRecordRead.input a b out pos)
      (fun v => v=output a b out pos) (192*w+667) := by
  have hw := component_width a b w ha hb
  have h0 := ButterflyRecordRead.runs a b out pos
  have h1 := RawLinearCombinationCleanup.prepend_runs ButterflyNumerator.program _ _
    (afterStreams a b out pos) (ButterflyNumerator.runs (components a b) w hw)
  have h2 := ButterflyRecordOutputData.runs (afterStreams a b out pos) (components a b)
    (fun i => ButterflyNumerator.words i (components a b)) w hw
  have h3 := ButterflyRecordEmit.runs (afterStreams a b out pos)
    (fun i => ButterflyNumerator.words i (components a b))
  simp only [ButterflyNumerator.words_length _ _ w hw] at h3
  exact (((h0.seq h1).seq h2).seq h3).consequence (fun _ h => h) (fun _ h => h)
    (by rw [ha.1,ha.2,hb.1,hb.2]; omega)

/-- Mathematical input values are the actual signed words read from the streams. -/
def values (a b : Context 2) (half precision : ℕ) : Fin 2 → ℂ :=
  ![complexValue (signedValue half a.re) (signedValue half a.im) precision,
    complexValue (signedValue half b.re) (signedValue half b.im) precision]

def resultValues (a b : Context 2) (half precision : ℕ) : Fin 2 → ℂ :=
  let zs := fun i => ButterflyNumerator.words i (components a b)
  ![complexValue (signedValue half (zs 0)) (signedValue half (zs 1)) precision,
    complexValue (signedValue half (zs 2)) (signedValue half (zs 3)) precision]

/-- The actual grid invariant of a kernel prefix supplies the signed guard. The
caller provides neither a modular codec premise nor an extra no-overflow bound. -/
theorem exact_of_prefix_grid (a b : Context 2) (p D j : ℕ) (hj : j≤D)
    (ha : a.re.length=ButterflyGuard.width p D ∧ a.im.length=ButterflyGuard.width p D)
    (hb : b.re.length=ButterflyGuard.width p D ∧ b.im.length=ButterflyGuard.width p D)
    (hgrid : ∀ i,Networks.GaussianPrecision.BoundedGrid (p+j) ((2^p)*4^j)
      (values a b (ButterflyGuard.halfWidth p D) (p+j) i)) :
    resultValues a b (ButterflyGuard.halfWidth p D) (p+j+1) 0=
      (values a b (ButterflyGuard.halfWidth p D) (p+j) 0+
       values a b (ButterflyGuard.halfWidth p D) (p+j) 1+
       Complex.I*(values a b (ButterflyGuard.halfWidth p D) (p+j) 0-
       values a b (ButterflyGuard.halfWidth p D) (p+j) 1))/2 ∧
    resultValues a b (ButterflyGuard.halfWidth p D) (p+j+1) 1=
      (values a b (ButterflyGuard.halfWidth p D) (p+j) 0+
       values a b (ButterflyGuard.halfWidth p D) (p+j) 1-
       Complex.I*(values a b (ButterflyGuard.halfWidth p D) (p+j) 0-
       values a b (ButterflyGuard.halfWidth p D) (p+j) 1))/2 := by
  have h0 := ButterflyGuard.represented_bound (signedValue (ButterflyGuard.halfWidth p D) a.re)
    (signedValue (ButterflyGuard.halfWidth p D) a.im) (p+j) ((2^p)*4^j) (hgrid 0)
  have h1 := ButterflyGuard.represented_bound (signedValue (ButterflyGuard.halfWidth p D) b.re)
    (signedValue (ButterflyGuard.halfWidth p D) b.im) (p+j) ((2^p)*4^j) (hgrid 1)
  have hh := ButterflySigned.words_butterfly (components a b) (ButterflyGuard.halfWidth p D) (p+j)
    (component_width a b _ ha hb) (((2^p)*4^j:ℕ):ℤ)
    (by intro i; fin_cases i
        · exact h0.1
        · exact h0.2
        · exact h1.1
        · exact h1.2)
    (by exact_mod_cast ButterflyGuard.guard p D j hj)
  exact hh

end
end IntegerMultBounds.Machine.ButterflyRecord
