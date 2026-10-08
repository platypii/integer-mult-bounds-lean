import IntegerMultBounds.Machine.RadixLinearCombinationRefresh

/-! Physical shared-source preparation through canonical binary output.
The refresh stage synchronizes the compiler's actual leaf bank before arithmetic;
every source copy and conversion step is executed by the finite tape machine. -/
namespace IntegerMultBounds.Machine.RadixLinearCombinationShared

open RadixDigits
open RadixLinearCombinationRefresh (Expr Size controls)
open MarkedWordCleanup (one word)
variable {c q : ℕ} [Fact q.Prime]

/-- Retain a prefix as additional active tapes under a fixed placement. -/
def prefixPlacement {s u t : ℕ} (c : ℕ) (e : Fin (s+u) ≃ Fin t) :
    Fin ((c+s)+u) ≃ Fin (c+t) where
  toFun := Fin.addCases (Fin.addCases (Fin.castAdd t) (fun i => Fin.natAdd c (e (Fin.castAdd u i))))
    (fun i => Fin.natAdd c (e (Fin.natAdd s i)))
  invFun := Fin.addCases (fun i => Fin.castAdd u (Fin.castAdd s i))
    (fun i => Fin.addCases (fun j => Fin.castAdd u (Fin.natAdd c j)) (Fin.natAdd (c+s)) (e.symm i))
  left_inv := by
    intro i
    induction i using Fin.addCases with
    | left i => induction i using Fin.addCases <;> simp
    | right i => simp
  right_inv := by
    intro i
    induction i using Fin.addCases with
    | left i => simp
    | right i => obtain ⟨j,rfl⟩ := e.surjective i; induction j using Fin.addCases <;> simp

omit [Fact q.Prime] in
private theorem prefix_active {s u t : ℕ} (e : Fin (s+u) ≃ Fin t) (v : Tapes c q) (w : Tapes t q) :
    Placement.active (prefixPlacement c e) (v.append w) = v.append (Placement.active e w) := by
  unfold Placement.active prefixPlacement Tapes.append
  congr 1 <;> funext i <;> induction i using Fin.addCases <;> simp

omit [Fact q.Prime] in
private theorem prefix_extra {s u t : ℕ} (e : Fin (s+u) ≃ Fin t) (v : Tapes c q) (w : Tapes t q) :
    Placement.extra (prefixPlacement c e) (v.append w) = Placement.extra e w := by
  unfold Placement.extra prefixPlacement Tapes.append
  congr 1 <;> funext i <;> simp

abbrev TapeCount (e : Expr c) := c+RadixLinearCombinationBinary.TapeCount e.erase
abbrev States (e : Expr c) := RadixLinearCombinationRefresh.States e+RadixLinearCombinationBinary.States e.erase

def input (e : Expr c) (xs old : ℕ → List (Fin q)) : Tapes (TapeCount e) q :=
  (controls xs).append (RadixLinearCombinationBinary.input e.erase old)

def output (e : Expr c) (xs : ℕ → List (Fin q)) : Tapes (TapeCount e) q :=
  (controls xs).append (RadixLinearCombinationBinary.output e.erase xs)

def refreshPlacement (e : Expr c) : Fin ((c+Size e)+2) ≃ Fin (TapeCount e) :=
  prefixPlacement c (RadixLinearCombinationBinary.arithmeticPlacement e.erase)

omit [Fact q.Prime] in
private theorem refresh_active (e : Expr c) (xs old : ℕ → List (Fin q)) :
    Placement.active (refreshPlacement e) (input e xs old) = RadixLinearCombinationRefresh.bank e xs old := by
  rw [input,refreshPlacement,prefix_active]
  congr 1
  rw [RadixLinearCombination.bank_split]
  unfold Placement.active RadixLinearCombinationBinary.arithmeticPlacement RadixLinearCombinationBinary.input
    RadixLinearCombinationBinary.bank
  congr 1 <;> funext i <;> induction i using Fin.addCases with
  | left i => fin_cases i; simp [Tapes.append,one]
  | right i => simp [Tapes.append]

omit [Fact q.Prime] in
private theorem refresh_extra (e : Expr c) (xs old : ℕ → List (Fin q)) :
    Placement.extra (refreshPlacement e) (input e xs old) =
      Placement.extra (refreshPlacement e) (input e xs xs) := by
  rw [input,input,refreshPlacement,prefix_extra,prefix_extra]
  unfold Placement.extra RadixLinearCombinationBinary.arithmeticPlacement RadixLinearCombinationBinary.input
    RadixLinearCombinationBinary.bank
  congr 1 <;> funext i <;> fin_cases i <;> simp [Tapes.append]

def program (e : Expr c) : Program (TapeCount e) (States e) q :=
  seq (Placement.placed (RadixLinearCombinationRefresh.program e) (refreshPlacement e))
    (Placement.placed (RadixLinearCombinationBinary.program e.erase)
      (finAddFlip : Fin (RadixLinearCombinationBinary.TapeCount e.erase+c) ≃ Fin (TapeCount e)))

omit [Fact q.Prime] in
theorem refresh_hoare (e : Expr c) (xs old : ℕ → List (Fin q)) :
    HoareTime (Placement.placed (RadixLinearCombinationRefresh.program e) (refreshPlacement e))
      (fun v => v = input e xs old) (fun v => v = input e xs xs)
      (RadixLinearCombinationRefresh.runtime e xs old) := by
  apply (Placement.hoare_at (RadixLinearCombinationRefresh.refresh_hoare e xs old) (refreshPlacement e)
    (input e xs old) (refresh_active e xs old)).consequence (fun _ h => h) _ le_rfl
  rintro v ⟨w,rfl,rfl⟩
  rw [Placement.replace,refresh_extra,← refresh_active e xs xs]
  exact Placement.view _ _

private theorem arithmetic_hoare (e : Expr c) (xs : ℕ → List (Fin q)) (b : ℕ)
    (hw : ∀ i, (xs i).length = b) :
    HoareTime (Placement.placed (RadixLinearCombinationBinary.program e.erase)
      (finAddFlip : Fin (RadixLinearCombinationBinary.TapeCount e.erase+c) ≃ Fin (TapeCount e)))
      (fun v => v = input e xs xs) (fun v => v = output e xs)
      ((RadixLinearCombination.linearConstant e.erase+40)*q^b) := by
  let wire : Fin (RadixLinearCombinationBinary.TapeCount e.erase+c) ≃ Fin (TapeCount e) := finAddFlip
  have ha : Placement.active wire (input e xs xs) = RadixLinearCombinationBinary.input e.erase xs := by
    unfold Placement.active wire input
    congr 1 <;> funext i <;> simp [Tapes.append] <;> rfl
  have hb : Placement.active wire (output e xs) = RadixLinearCombinationBinary.output e.erase xs := by
    unfold Placement.active wire output
    congr 1 <;> funext i <;> simp [Tapes.append] <;> rfl
  have hf : Placement.extra wire (input e xs xs) = Placement.extra wire (output e xs) := by
    unfold Placement.extra wire input output
    congr 1 <;> funext i <;> simp [Tapes.append]
  apply (Placement.hoare_at (RadixLinearCombinationBinary.compute_hoare_linear e.erase xs b hw)
    wire (input e xs xs) ha).consequence (fun _ h => h) _ le_rfl
  rintro v ⟨w,rfl,rfl⟩
  rw [Placement.replace,hf,← hb]
  exact Placement.view _ _

/-- Refresh costs are charged separately, allowing old copies of arbitrary width. -/
theorem compute_hoare (e : Expr c) (xs old : ℕ → List (Fin q)) (b : ℕ)
    (hw : ∀ i, (xs i).length = b) :
    HoareTime (program e) (fun v => v = input e xs old) (fun v => v = output e xs)
      (RadixLinearCombinationRefresh.runtime e xs old+1+
        (RadixLinearCombination.linearConstant e.erase+40)*q^b) :=
  (refresh_hoare e xs old).seq (arithmetic_hoare e xs b hw)

/-- End-to-end preparation is linear in the radix modulus for bounded stale
copies. The multiplicative constant depends only on the fixed expression. -/
theorem compute_hoare_linear (e : Expr c) (xs old : ℕ → List (Fin q)) (b : ℕ)
    (hw : ∀ i, (xs i).length = b) (ho : ∀ i : Fin c, (old i.val).length ≤ b) :
    HoareTime (program e) (fun v => v = input e xs old) (fun v => v = output e xs)
      ((13*RadixLinearCombinationRefresh.leaves e+RadixLinearCombination.linearConstant e.erase+40)*q^b) := by
  apply (compute_hoare e xs old b hw).consequence (fun _ h => h) (fun _ h => h)
  have hr := RadixLinearCombinationRefresh.runtime_le e xs old b (fun i => (hw i.val).le) ho
  have hb := RadixToBinaryData.width_le_power (Fact.out : q.Prime).two_le b
  have hp : 1 ≤ q^b := Nat.one_le_pow _ _ (by have := (Fact.out : q.Prime).two_le; omega)
  have hh : 4*b+9 ≤ 13*q^b := by omega
  have hm := Nat.mul_le_mul_left (RadixLinearCombinationRefresh.leaves e) hh
  nlinarith

/-- Literal shared controls and heads survive the entire preparation. -/
theorem output_controls (e : Expr c) (xs : ℕ → List (Fin q)) :
    Placement.active (Equiv.refl (Fin (c+RadixLinearCombinationBinary.TapeCount e.erase))) (output e xs) = controls xs := by
  unfold Placement.active output
  congr 1 <;> funext i <;> simp [Tapes.append] <;> rfl

/-- The actual output slot contains the canonical binary encoding. -/
theorem output_binary (e : Expr c) (xs : ℕ → List (Fin q)) :
    let i := Fin.natAdd c (Fin.castAdd (RadixLinearCombination.AuxTapes e.erase) (0 : Fin 3))
    (output e xs).head i = 1 ∧ (output e xs).tape i =
      fun z => (RadixToBinary.binaryEncoding (q := q)).encode
        (CountedCopyReuse.binary (RadixLinearCombinationBinary.bits e.erase xs) z) := by
  simpa only [output,Tapes.append,Fin.addCases_right] using RadixLinearCombinationBinary.output_binary e.erase xs

/-- Extend an actual finite control bank without introducing any extra physical
source. Out-of-range mathematical indices alias an explicitly chosen bank slot. -/
def read (seed : Fin c) (xs : Fin c → List (Fin q)) (i : ℕ) : List (Fin q) :=
  if h : i < c then xs ⟨i,h⟩ else xs seed

omit [Fact q.Prime] in
@[simp] theorem read_at (seed i : Fin c) (xs : Fin c → List (Fin q)) :
    read seed xs i.val = xs i := by simp [read,i.isLt]

omit [Fact q.Prime] in
theorem read_width (seed : Fin c) (xs : Fin c → List (Fin q)) (b : ℕ)
    (hw : ∀ i, (xs i).length = b) : ∀ i, (read seed xs i).length = b := by
  intro i
  unfold read
  split <;> exact hw _

/-- Preparation whose data parameters are only the finitely many physical
controls and old leaf sources, with no condition on an infinite input family. -/
theorem compute_finite_hoare (e : Expr c) (seed : Fin c) (xs old : Fin c → List (Fin q)) (b : ℕ)
    (hw : ∀ i, (xs i).length = b) (ho : ∀ i, (old i).length ≤ b) :
    HoareTime (program e) (fun v => v = input e (read seed xs) (read seed old))
      (fun v => v = output e (read seed xs))
      ((13*RadixLinearCombinationRefresh.leaves e+RadixLinearCombination.linearConstant e.erase+40)*q^b) := by
  apply compute_hoare_linear e _ _ b (read_width seed xs b hw)
  intro i
  simpa using ho i

/-- The computed canonical bits denote the actual rational expression modulo
q to the common word width. Denominator validity is the explicit side condition. -/
theorem bits_value (e : Expr c) (he : RadixLinearCombination.Valid (q := q) e.erase)
    (seed : Fin c) (xs : Fin c → List (Fin q)) (b : ℕ) (hw : ∀ i, (xs i).length = b) :
    (Counter.value (RadixLinearCombinationBinary.bits e.erase (read seed xs)) : ZMod (q^b)) =
      RadixLinearCombination.valueMod b e.erase (read seed xs) :=
  RadixLinearCombinationBinary.bits_value e.erase he _ b (read_width seed xs b hw)

end IntegerMultBounds.Machine.RadixLinearCombinationShared
