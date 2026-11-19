module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackFormulaCompiler

/-! Evaluate determinant formulas from row-major matrix tapes and fixed-width constants. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback.RingFormula
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host LabelTraversal Node
variable {ι : Type} {T Q A M m : ℕ} [NeZero M] {P U : Type}

/-- A matrix identifier followed by its row and column. -/
abbrev Entry (ι : Type) (m : ℕ) := ι × Fin m × Fin m

def entryValue (mat : ι → Matrix (Fin m) (Fin m) (ZMod M)) (a : Entry ι m) := mat a.1 a.2.1 a.2.2

def readLeaf (ports : Leaf (Entry ι m) → Fin T → Fin 7 ↪ Fin T) (a : Leaf (Entry ι m)) (out : Fin T) :
    Pr P T Q A U :=
  let r := ports a out
  match a with
  | .input (_,i,j) => readMatrixWord (i.val*m+j.val) r
  | .zero | .one => bcopy (r 2) (r 3) (r 4) (r 5)

def readTime (H : ℕ) : Leaf (Entry ι m) → ℕ
  | .input (_,i,j) => 8*((i.val*m+j.val)*H)+14*H+22
  | .zero | .one => 6*H+6

/-- Every fixed matrix formula has a quadratic field-width budget. Its
coefficient is obtained by evaluating the same cost expression at width one. -/
theorem time_readTime_le (f : RingFormula (Entry ι m)) (H : ℕ) :
    time H (readTime H) f ≤ time 1 (readTime 1) f * (H+1)^2 := by
  induction f with
  | input a =>
    obtain ⟨b,i,j⟩ := a
    simp only [time, readTime]
    ring_nf
    omega
  | zero | one =>
    simp only [time, readTime]
    ring_nf
    omega
  | sub x y hx hy | mul x y hx hy =>
    simp only [time, Gate.time]
    grw [hx, hy]
    ring_nf
    omega

def leafReady (ports : Leaf (Entry ι m) → Fin T → Fin 7 ↪ Fin T)
    (mat : ι → Matrix (Fin m) (Fin m) (ZMod M)) (H : ℕ)
    (a : Leaf (Entry ι m)) (out : Fin T) (R : Regs T A) :=
  let r := ports a out
  r 3 = out ∧ match a with
  | .input (b,_,_) => (∃ tail, R (r 2) = matrixWords A H (mat b) ++ tail) ∧
      (R (r 1)).length = H ∧ ∀ k : Fin 7, k = 0 ∨ 4 ≤ k → R (r k) = []
  | .zero | .one => R (r 2) = binSyms H (a.value (entryValue mat)).val ∧ R (r 4) = [] ∧ R (r 5) = []

theorem readLeaf_writes (body : P → Pr P T Q A U) (ports : Leaf (Entry ι m) → Fin T → Fin 7 ↪ Fin T)
    (mat : ι → Matrix (Fin m) (Fin m) (ZMod M)) (H : ℕ) (a : Leaf (Entry ι m)) (out : Fin T) :
    Writes body (leafReady ports mat H a out) out (readLeaf ports a out)
      (binSyms H (a.value (entryValue mat)).val) (readTime H a) := by
  intro v S h
  have copy (r : Fin 7 ↪ Fin T) (x : ZMod M) (dst : r 3 = out) (src : S.R (r 2) = binSyms H x.val)
      (free : S.R (r 4) = []) (saved : S.R (r 5) = []) :
      ∃ z n, z.user = v.user ∧ n ≤ 6*H+6 ∧ Exec body (bcopy (r 2) (r 3) (r 4) (r 5)) (mk v S) n
        (mk z {S with R := Function.update S.R out (binSyms H x.val ++ S.R out)}) := by
    obtain ⟨z,hz,run⟩ := bcopy_exec body (a := r 2) (c := r 3) (t₁ := r 4) (t₂ := r 5)
      (by simp [List.nodup_cons,r.injective.eq_iff]) v S free saved
    rw [src,length_binSyms] at run
    exact ⟨z,_,hz,le_rfl,run.cast rfl (by rw [dst])⟩
  cases a with
  | input a =>
    obtain ⟨b,i,j⟩ := a
    obtain ⟨dst,⟨tail,src⟩,width,free⟩ := h
    obtain ⟨z,hz,run⟩ := readMatrixWord_exec body _ (mat b) i j H v S tail src width free
    rw [dst] at run
    exact ⟨z,_,hz,le_rfl,run⟩
  | zero | one =>
    obtain ⟨dst,src,free,saved⟩ := h
    exact copy _ _ dst src free saved

theorem compile_from_matrices (body : P → Pr P T Q A U)
    (ports : Leaf (Entry ι m) → Fin T → Fin 7 ↪ Fin T) (bank : ℕ → Fin T → Fin 13 ↪ Fin T)
    (mat : ι → Matrix (Fin m) (Fin m) (ZMod M)) (H : ℕ) (hm : M < 2^H)
    (f : RingFormula (Entry ι m)) (out : Fin T) :
    Writes body (prepared bank (entryValue mat) H (leafReady ports mat H) f 0 out) out
      (compile (readLeaf ports) bank f 0 out) (binSyms H (eval (entryValue mat) f).val) (time H (readTime H) f) :=
  compile_writes bank _ H _ body hm _ _ (readLeaf_writes body ports mat H) f 0 out

def matrixInput (b : ι) (i j : Fin m) : RingFormula (Entry ι m) := .input (b,i,j)

theorem determinant_writes (body : P → Pr P T Q A U)
    (ports : Leaf (Entry ι m) → Fin T → Fin 7 ↪ Fin T) (bank : ℕ → Fin T → Fin 13 ↪ Fin T)
    (mat : ι → Matrix (Fin m) (Fin m) (ZMod M)) (H : ℕ) (hm : M < 2^H) (b : ι) (out : Fin T) :
    let f := determinant (matrixInput b)
    Writes body (prepared bank (entryValue mat) H (leafReady ports mat H) f 0 out) out
      (compile (readLeaf ports) bank f 0 out) (binSyms H (mat b).det.val) (time H (readTime H) f) := by
  intro f
  have run := compile_from_matrices body ports bank mat H hm f out
  have same (k : ι) : (Matrix.of fun i j => mat k i j) = mat k := rfl
  simpa only [f,eval_determinant,matrixInput,eval,entryValue,same] using run

theorem numerator_writes (body : P → Pr P T Q A U)
    (ports : Leaf (Entry ι m) → Fin T → Fin 7 ↪ Fin T) (bank : ℕ → Fin T → Fin 13 ↪ Fin T)
    (mat : ι → Matrix (Fin m) (Fin m) (ZMod M)) (H : ℕ) (hm : M < 2^H) (g proj : ι) (i j : Fin m) (out : Fin T) :
    let f := numerator (matrixInput g) (matrixInput proj) i j
    Writes body (prepared bank (entryValue mat) H (leafReady ports mat H) f 0 out) out
      (compile (readLeaf ports) bank f 0 out) (binSyms H (conjugateNumerator (mat g) (mat proj) i j).val)
      (time H (readTime H) f) := by
  intro f
  have run := compile_from_matrices body ports bank mat H hm f out
  have same (k : ι) : (Matrix.of fun i j => mat k i j) = mat k := rfl
  simpa only [f,eval_numerator,matrixInput,eval,entryValue,same] using run

end IntegerMultBounds.MathlibTM2.Cover.Fallback.RingFormula
