module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvBatchUnary

/-! # A fixed bank for the shared short-convolution batch primitive

All register compatibility is discharged here, once. The same 117-tape program handles every
batch size, padded record size and precision. Its inputs are raw pair-symbol streams and unary
dimensions; its output is the full stream of truncated convolution coefficients. No caller
supplies prepared counters, a header, or a register-layout or execution hypothesis.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv.Fixed

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.Spec.SignedRingProduct

/-- The vendored product retains its original 91-register bank. -/
def hostReg (k : Fin 91) : Fin 117 := ⟨k.val, by omega⟩

/-- Nine stream/conversion registers, followed by the four shared data registers. -/
def ringReg : RpReg → Fin 117
  | .xs => 91 | .ys => 92 | .out => 93 | .wn => 94 | .sv => 95
  | .ta => 96 | .tb => 97 | .acc => 98 | .tmp => 99
  | .d0 => 0 | .d1 => 1 | .d2 => 2 | .d3 => 3

/-- Setup reuses the product's word-width, header and five conversion-work registers. -/
def setupReg : SetupReg → Fin 117
  | .p => 100 | .l => 101 | .w => 94 | .a => 102 | .b => 103
  | .countX => 104 | .padX => 105 | .countY => 106 | .padY => 107
  | .header => 0 | .ta => 96 | .tb => 97 | .acc => 98 | .sv => 95 | .tmp => 99

/-- The raw streams, record count, and six batch-work registers. -/
inductive BatchReg
  | records | recordSaved | srcX | srcY | saved | acc | buf | savedBlock | tmp
  deriving DecidableEq

def batchReg : BatchReg → Fin 117
  | .records => 108 | .recordSaved => 109 | .srcX => 110 | .srcY => 111
  | .saved => 112 | .acc => 113 | .buf => 114 | .savedBlock => 115 | .tmp => 116

theorem ringReg_injective : Function.Injective ringReg := by
  intro r s h
  cases r <;> cases s <;> simp_all [ringReg, Fin.ext_iff]

theorem setupReg_injective : Function.Injective setupReg := by
  intro r s h
  cases r <;> cases s <;> simp_all [setupReg, Fin.ext_iff]

theorem layout : RpLayout ringReg hostReg := by
  refine ⟨ringReg_injective, ?_, rfl, rfl, rfl, rfl, ?_⟩
  · intro i j h
    apply Fin.ext
    exact congrArg (fun k : Fin 117 => k.val) h
  · intro r k hk he
    have e := congrArg Fin.val he
    cases r <;> simp [ringReg, hostReg] at e <;> omega

theorem counts_off (s : SetupReg) (hs : s ∈ setupCounters) (r : RpReg) :
    setupReg s ≠ ringReg r := by
  simp only [setupCounters, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl <;> cases r <;> decide

theorem counts_private (s : SetupReg) (hs : s ∈ setupCounters) (k : Fin 91) :
    setupReg s ≠ hostReg k := by
  intro he
  have e := congrArg Fin.val he
  simp only [setupCounters, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl <;> simp [setupReg, hostReg] at e <;> omega

theorem packX_distinct :
    [batchReg .records, batchReg .recordSaved, setupReg .countX, setupReg .padX,
      batchReg .srcX, batchReg .saved, batchReg .acc, batchReg .buf, batchReg .savedBlock,
      batchReg .tmp, ringReg .xs].Nodup := by decide +kernel

theorem packY_distinct :
    [batchReg .records, batchReg .recordSaved, setupReg .countY, setupReg .padY,
      batchReg .srcY, batchReg .saved, batchReg .acc, batchReg .buf, batchReg .savedBlock,
      batchReg .tmp, ringReg .ys].Nodup := by decide +kernel

theorem packY_off :
    ∀ k ∈ [batchReg .records, batchReg .recordSaved, setupReg .countY, setupReg .padY,
      batchReg .srcY, batchReg .saved, batchReg .acc, batchReg .buf, batchReg .savedBlock,
      batchReg .tmp], k ≠ ringReg .xs := by
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem data_off :
    ∀ k ∈ [batchReg .records, batchReg .recordSaved, batchReg .srcX, batchReg .srcY,
      batchReg .saved, batchReg .acc, batchReg .buf, batchReg .savedBlock, batchReg .tmp],
      ∀ s ∈ setupWritten, k ≠ setupReg s := by
  intro k hk s hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  simp only [setupWritten, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hs with rfl | rfl | rfl | rfl | rfl <;> decide

variable {Q A : ℕ} {U P : Type}

/-- One program, independent of every numerical input dimension. -/
noncomputable def program (hQ : rpStates ≤ Q) : Pr P 117 Q A U :=
  batchFromUnary setupReg ringReg hostReg layout (by decide) hQ
    (batchReg .records) (batchReg .recordSaved) (batchReg .srcX) (batchReg .srcY)
    (batchReg .saved) (batchReg .acc) (batchReg .buf) (batchReg .savedBlock) (batchReg .tmp)

/-- Input streams and dimensions occupy nine right stacks; all work registers start empty. -/
def inputBank (p l w M a b : ℕ) (X Y : ℕ → List GaussianInt)
    (tail : List (Fin (A + 4))) (k : Fin 117) : List (Fin (A + 4)) :=
  if k.val = 94 then List.replicate w tick else
  if k.val = 100 then List.replicate p tick else
  if k.val = 101 then List.replicate l tick else
  if k.val = 102 then List.replicate a tick else
  if k.val = 103 then List.replicate b tick else
  if k.val = 108 then List.replicate M tick else
  if k.val = 110 then cstream A w ((List.range M).flatMap X) else
  if k.val = 111 then cstream A w ((List.range M).flatMap Y) else
  if k.val = 93 then tail else []

/-- The native input/output stacks may hold arbitrary spectator data. -/
def start (p l w M a b : ℕ) (X Y : ℕ → List GaussianInt)
    (tail : List (Fin (A + 4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) : Stacks 117 A where
  inp := inp
  out := out
  L := fun _ => []
  R := inputBank p l w M a b X Y tail

/-- Counted raw operands may have borrowed suffixes; work and output ports are unchanged. -/
def inputBankWithTails (p l w M a b : ℕ) (X Y : ℕ → List GaussianInt)
    (tail tailX tailY : List (Fin (A + 4))) (k : Fin 117) : List (Fin (A + 4)) :=
  if k.val = 110 then inputBank p l w M a b X Y tail k ++ tailX else
  if k.val = 111 then inputBank p l w M a b X Y tail k ++ tailY else
  inputBank p l w M a b X Y tail k

/-- Fixed bank with suffixes beneath both counted operand streams. -/
def startWithTails (p l w M a b : ℕ) (X Y : ℕ → List GaussianInt)
    (tail tailX tailY : List (Fin (A + 4))) (inp : List (Bool ⊕ Bool))
    (out : List Bool) : Stacks 117 A :=
  { start p l w M a b X Y tail inp out with
    R := inputBankWithTails p l w M a b X Y tail tailX tailY }

@[simp] theorem inputBankWithTails_nil (p l w M a b : ℕ) (X Y : ℕ → List GaussianInt)
    (tail : List (Fin (A + 4))) :
    inputBankWithTails p l w M a b X Y tail [] [] = inputBank p l w M a b X Y tail := by
  funext k
  simp [inputBankWithTails]

@[simp] theorem startWithTails_nil (p l w M a b : ℕ) (X Y : ℕ → List GaussianInt)
    (tail : List (Fin (A + 4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    startWithTails p l w M a b X Y tail [] [] inp out =
      start p l w M a b X Y tail inp out := by
  simp [startWithTails, start]

/-- The emitted coefficient order, including all padded coefficients of each record. -/
def result (p l M : ℕ) (X Y : ℕ → List GaussianInt) : List GaussianInt :=
  rpStream M (fun n => coeff p l (X n) (Y n))

/-- A public time bound with setup and cleanup charged once for the whole batch. -/
def cost (p l w M : ℕ) : ℕ :=
  M * (rpRecBound p l w + 44 * (2 ^ l * w) + 50) + rpFixCost p l w +
    46 * (2 ^ l * w) + 8 * w + 18 * l + ldrHeaderCost p l w +
    2 * (header p (2 ^ l) w).length + 63

variable {body : P → Pr P 117 Q A U}

/-- The complete primitive on a concrete fixed bank. Every setup/layout obligation is
resolved internally. Exactly the result stream is pushed onto the output register. -/
theorem exec_with_tails (hQ : rpStates ≤ Q) (hA : 4 ≤ A)
    {p l w M a b : ℕ} (hp : 1 ≤ p) (hw : p + 2 ≤ w)
    (ha : a ≤ 2 ^ l) (hb : b ≤ 2 ^ l) (hab : a + b ≤ 2 ^ l + 1)
    (X Y : ℕ → List GaussianInt)
    (hlenX : ∀ n < M, (X n).length = a) (hlenY : ∀ n < M, (Y n).length = b)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * p))
    (hY : ∀ n < M, ∀ z ∈ Y n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * p))
    (v : HS 117 Q A U) (tail tailX tailY : List (Fin (A + 4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    ∃ v' n, v'.user = v.user ∧ n ≤ cost p l w M ∧
      Exec body (program hQ) (mk v (startWithTails p l w M a b X Y tail tailX tailY inp out)) n
        (mk v' { startWithTails p l w M a b X Y tail tailX tailY inp out with R :=
          (Function.update (inputBankWithTails p l w M a b X Y tail tailX tailY) (ringReg .out)
            (cstream A w (result p l M X Y) ++ tail)) }) := by
  let S := startWithTails p l w M a b X Y tail tailX tailY inp out
  have clean : RpClean hostReg S := by
    refine ⟨fun _ => rfl, fun k _ => ?_⟩
    have hk := k.isLt
    simp [S, startWithTails, start, inputBankWithTails, inputBank, hostReg,
      show k.val ≠ 94 by omega, show k.val ≠ 100 by omega,
      show k.val ≠ 101 by omega, show k.val ≠ 102 by omega,
      show k.val ≠ 103 by omega, show k.val ≠ 108 by omega,
      show k.val ≠ 110 by omega, show k.val ≠ 111 by omega, show k.val ≠ 93 by omega]
  have setupEmpty : ∀ s ∈ setupWritten ++ setupScratch, S.R (setupReg s) = [] := by
    intro s hs
    simp only [setupWritten, setupScratch, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hs
    rcases hs with (rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl) <;>
      simp [S, startWithTails, start, inputBankWithTails, inputBank, setupReg]
  have scratchEmpty : ∀ k ∈ [batchReg .recordSaved, batchReg .saved, batchReg .acc,
      batchReg .buf, batchReg .savedBlock, batchReg .tmp], S.R k = [] := by
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [S, startWithTails, start, inputBankWithTails, inputBank, batchReg]
  have ringEmpty : ∀ r ∈ [RpReg.xs, .ys, .sv, .ta, .tb, .acc, .tmp, .d1, .d2, .d3],
      S.R (ringReg r) = [] := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [S, startWithTails, start, inputBankWithTails, inputBank, ringReg]
  obtain ⟨v', n, hu, hn, he⟩ := batchFromUnary_prefix_exec (body := body) layout (by decide) hQ hA
    setupReg setupReg_injective rfl rfl counts_off counts_private hp hw ha hb hab X Y
    hlenX hlenY hX hY (batchReg .records) (batchReg .recordSaved) (batchReg .srcX) (batchReg .srcY)
    (batchReg .saved) (batchReg .acc) (batchReg .buf) (batchReg .savedBlock) (batchReg .tmp)
    packX_distinct packY_distinct packY_off data_off v S tailX tailY clean
    (by simp [S, startWithTails, start, inputBankWithTails, inputBank, setupReg]) (by simp [S, startWithTails, start, inputBankWithTails, inputBank, setupReg])
    (by simp [S, startWithTails, start, inputBankWithTails, inputBank, setupReg]) (by simp [S, startWithTails, start, inputBankWithTails, inputBank, setupReg])
    (by simp [S, startWithTails, start, inputBankWithTails, inputBank, setupReg]) setupEmpty
    (by simp [S, startWithTails, start, inputBankWithTails, inputBank, batchReg])
    (by simp [S, startWithTails, start, inputBankWithTails, inputBank, batchReg]) (by simp [S, startWithTails, start, inputBankWithTails, inputBank, batchReg])
    scratchEmpty ringEmpty
  refine ⟨v', n, hu, hn.trans (batchUnaryCost_le_linear p l w M a b (by omega) ha hb), ?_⟩
  have hout : inputBankWithTails p l w M a b X Y tail tailX tailY (ringReg .out) = tail := by
    simp [inputBankWithTails, inputBank, ringReg]
  simpa only [program, S, startWithTails, start, hout, result] using he

theorem exec (hQ : rpStates ≤ Q) (hA : 4 ≤ A)
    {p l w M a b : ℕ} (hp : 1 ≤ p) (hw : p + 2 ≤ w)
    (ha : a ≤ 2 ^ l) (hb : b ≤ 2 ^ l) (hab : a + b ≤ 2 ^ l + 1)
    (X Y : ℕ → List GaussianInt)
    (hlenX : ∀ n < M, (X n).length = a) (hlenY : ∀ n < M, (Y n).length = b)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * p))
    (hY : ∀ n < M, ∀ z ∈ Y n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * p))
    (v : HS 117 Q A U) (tail : List (Fin (A + 4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    ∃ v' n, v'.user = v.user ∧ n ≤ cost p l w M ∧
      Exec body (program hQ) (mk v (start p l w M a b X Y tail inp out)) n
        (mk v' { start p l w M a b X Y tail inp out with R :=
          (Function.update (inputBank p l w M a b X Y tail) (ringReg .out)
            (cstream A w (result p l M X Y) ++ tail)) }) := by
  simpa only [startWithTails_nil, inputBankWithTails_nil] using
    exec_with_tails hQ hA hp hw ha hb hab X Y hlenX hlenY hX hY v tail [] [] inp out

/-- The concrete finite program has no procedure names or external procedure body. -/
noncomputable def closedProgram : Pr Empty 117 rpStates 4 Unit := program le_rfl

def closedBody (x : Empty) : Pr Empty 117 rpStates 4 Unit := nomatch x

/-- One fixed finite program works for every admissible batch. Its full bank frame restores
all input and work tapes, preserves spectator input/output stacks, and preserves the output tail. -/
theorem closed_exec {p l w M a b : ℕ} (hp : 1 ≤ p) (hw : p + 2 ≤ w)
    (ha : a ≤ 2 ^ l) (hb : b ≤ 2 ^ l) (hab : a + b ≤ 2 ^ l + 1)
    (X Y : ℕ → List GaussianInt)
    (hlenX : ∀ n < M, (X n).length = a) (hlenY : ∀ n < M, (Y n).length = b)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * p))
    (hY : ∀ n < M, ∀ z ∈ Y n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * p))
    (v : HS 117 rpStates 4 Unit) (tail : List (Fin 8))
    (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    ∃ v' n, v'.user = v.user ∧ n ≤ cost p l w M ∧
      Exec closedBody closedProgram (mk v (start p l w M a b X Y tail inp out)) n
        (mk v' { start p l w M a b X Y tail inp out with R :=
          (Function.update (inputBank p l w M a b X Y tail) (ringReg .out)
            (cstream 4 w (result p l M X Y) ++ tail)) }) := by
  simpa only [closedProgram] using exec (body := closedBody) le_rfl (by decide)
    hp hw ha hb hab X Y hlenX hlenY hX hY v tail inp out

@[simp] theorem result_length (p l M : ℕ) (X Y : ℕ → List GaussianInt) :
    (result p l M X Y).length = M * 2 ^ l := length_rpStream _ _

/-- Every output coefficient is the truncated integer convolution at this stream position. -/
theorem result_coeff (p l M : ℕ) (X Y : ℕ → List GaussianInt)
    (n : ℕ) (hn : n < M) (c : Fin (2 ^ l)) :
    (result p l M X Y)[n * 2 ^ l + c.val]? = some (coeff p l (X n) (Y n) c) :=
  rpStream_get _ n hn c

/-- The error bound for every returned coefficient, independent of batch size. -/
theorem result_err (p l M : ℕ) (a b : ℕ) (hab : a + b ≤ 2 ^ l + 1)
    (X Y : ℕ → List GaussianInt)
    (hlenX : ∀ n < M, (X n).length = a) (hlenY : ∀ n < M, (Y n).length = b)
    (n : ℕ) (hn : n < M) (c : Fin (2 ^ l)) :
    ‖((2 ^ l : ℕ) : ℂ) * value p ((result p l M X Y)[n * 2 ^ l + c.val]?.getD 0) -
      ∑ i ∈ Finset.range (c.val + 1), value p (block (X n) i) * value p (block (Y n) (c.val - i))‖ ≤
        2 * (2 ^ l : ℕ) / (2 : ℝ) ^ p := by
  rw [result_coeff p l M X Y n hn c]
  apply coeff_err
  rw [hlenX n hn, hlenY n hn]
  exact hab

end IntegerMultBounds.MathlibTM2.Mult.ShortConv.Fixed
