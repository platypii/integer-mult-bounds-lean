import IntegerMultBounds.Machine.RadixLinearCombination

/-! Complete fixed linear-combination preparation: compute a radix expression,
convert its modular residue once to canonical binary, and erase the final radix
scratch. Original marked controls are preserved, with every scratch head reset. Each
expression leaf has its own supplied marked source copy, as in the arithmetic
compiler; this module does not duplicate or refresh repeated logical controls. -/
namespace IntegerMultBounds.Machine.RadixLinearCombinationBinary

open RadixDigits
open RadixLinearCombination (Expr AuxTapes workspace)
open MarkedWordCleanup (one word)
variable {q : ℕ} [Fact q.Prime]

abbrev TapeCount (e : Expr) := 3+AuxTapes e
abbrev States (e : Expr) := (RadixLinearCombination.States e+18)+6

def bits (e : Expr) (xs : ℕ → List (Fin q)) := RadixToBinaryData.output (RadixLinearCombination.result e xs)

def bank (e : Expr) (xs : ℕ → List (Fin q)) (f : ℤ → Fin (q+4)) (p : ℤ) (ys : List (Fin q)) :
    Tapes (TapeCount e) q :=
  (⟨![p,0,0],![f,fun _ => blank,word (ys.map digitSymbol)]⟩ : Tapes 3 q).append (workspace e xs)

def input (e : Expr) (xs : ℕ → List (Fin q)) : Tapes (TapeCount e) q := bank e xs (fun _ => blank) 0 []

def output (e : Expr) (xs : ℕ → List (Fin q)) : Tapes (TapeCount e) q :=
  bank e xs ((RadixToBinary.binaryState q (bits e xs)).tape 0) 1 []

/-- Output of the radix compiler shares converter slot2; its entire workspace
is a static frame, and the two converter work tapes are excluded from it. -/
def arithmeticPlacement (e : Expr) : Fin (RadixLinearCombination.TapeCount e+2) ≃ Fin (TapeCount e) where
  toFun := Fin.addCases (Fin.addCases (fun _ => Fin.castAdd (AuxTapes e) (2 : Fin 3)) (Fin.natAdd 3))
    (fun i => Fin.castAdd (AuxTapes e) (Fin.castAdd 1 i))
  invFun := Fin.addCases
    (fun i => ![Fin.natAdd (1+AuxTapes e) (0 : Fin 2),Fin.natAdd (1+AuxTapes e) (1 : Fin 2),
      Fin.castAdd 2 (Fin.castAdd (AuxTapes e) (0 : Fin 1))] i)
    (fun i => Fin.castAdd 2 (Fin.natAdd 1 i))
  left_inv := by
    intro i
    induction i using Fin.addCases with
    | left i =>
      induction i using Fin.addCases with
      | left i => fin_cases i; simp
      | right i => simp
    | right i => fin_cases i <;> simp
  right_inv := by
    intro i
    induction i using Fin.addCases with
    | left i => fin_cases i <;> simp
    | right i => simp

private def cleanupThree : Program 3 6 q :=
  Placement.placed (u := 2) MarkedWordCleanup.program (Equiv.swap 0 (2 : Fin 3))

omit [Fact q.Prime] in
private theorem arithmetic_active (e : Expr) (xs : ℕ → List (Fin q)) (ys : List (Fin q)) :
    Placement.active (arithmeticPlacement e) (bank e xs (fun _ => blank) 0 ys) = RadixLinearCombination.bank e xs ys := by
  rw [RadixLinearCombination.bank_split]
  unfold Placement.active arithmeticPlacement bank
  congr 1 <;> funext i <;> induction i using Fin.addCases with
  | left i => fin_cases i; simp [Tapes.append,one]
  | right i => simp [Tapes.append]

omit [Fact q.Prime] in
private theorem arithmetic_extra (e : Expr) (xs : ℕ → List (Fin q)) (ys : List (Fin q)) :
    Placement.extra (arithmeticPlacement e) (bank e xs (fun _ => blank) 0 ys) =
      Placement.extra (arithmeticPlacement e) (input e xs) := by
  unfold Placement.extra arithmeticPlacement input bank
  congr 1
  funext i
  fin_cases i <;> simp [Tapes.append]

private theorem arithmetic_hoare (e : Expr) (xs : ℕ → List (Fin q)) (b : ℕ) (hw : ∀ i, (xs i).length = b) :
    HoareTime (Placement.placed (RadixLinearCombination.program e) (arithmeticPlacement e))
      (fun v => v = input e xs)
      (fun v => v = bank e xs (fun _ => blank) 0 (RadixLinearCombination.result e xs))
      (RadixLinearCombination.runtime e b) := by
  have hh := Placement.hoare_at (RadixLinearCombination.compute_hoare e xs b hw) (arithmeticPlacement e)
    (input e xs) (arithmetic_active e xs [])
  apply hh.consequence (fun _ h => h) _ le_rfl
  rintro v ⟨w,rfl,rfl⟩
  rw [Placement.replace,← arithmetic_extra e xs (RadixLinearCombination.result e xs),← arithmetic_active]
  exact Placement.view _ _

private theorem conversion_hoare (e : Expr) (xs : ℕ → List (Fin q)) (ys : List (Fin q)) :
    HoareTime (extend (RadixToBinary.convertProgram (Fact.out : q.Prime).two_le) (AuxTapes e))
      (fun v => v = bank e xs (fun _ => blank) 0 ys)
      (fun v => v = bank e xs ((RadixToBinary.binaryState q (RadixToBinaryData.output ys)).tape 0) 1 ys)
      (10*value ys+6*ys.length+14) := by
  have hh := FamilyPlacementAlphabet.extend_hoare (RadixToBinary.convert_hoare (Fact.out : q.Prime).two_le ys) (workspace e xs)
  exact hh

omit [Fact q.Prime] in
private theorem cleanup_hoare (e : Expr) (xs : ℕ → List (Fin q)) (f : ℤ → Fin (q+4)) (p : ℤ) (ys : List (Fin q)) :
    HoareTime (extend cleanupThree (AuxTapes e))
      (fun v => v = bank e xs f p ys) (fun v => v = bank e xs f p []) (2*ys.length+6) := by
  let before : Tapes 3 q := ⟨![p,0,0],![f,fun _ => blank,word (ys.map digitSymbol)]⟩
  let after : Tapes 3 q := ⟨![p,0,0],![f,fun _ => blank,fun _ => blank]⟩
  let wire : Fin (1+2) ≃ Fin 3 := Equiv.swap 0 2
  have hd : ∀ x ∈ ys.map digitSymbol, x ≠ (blank : Fin (q+4)) := by
    intro x hx
    obtain ⟨y,_,rfl⟩ := List.mem_map.mp hx
    intro h
    have hv := congrArg Fin.val h
    simp only [digitSymbol,blank] at hv
    omega
  have ha : Placement.active wire before = one (word (ys.map digitSymbol)) 0 := by
    unfold Placement.active wire before one
    congr 1 <;> funext i <;> fin_cases i <;> rfl
  have hf : Placement.active wire after = one (fun _ => blank) 0 := by
    unfold Placement.active wire after one
    congr 1 <;> funext i <;> fin_cases i <;> rfl
  have he : Placement.extra wire before = Placement.extra wire after := by
    unfold Placement.extra wire before after
    congr 1
    funext i
    fin_cases i <;> rfl
  have hh := Placement.hoare_at (MarkedWordCleanup.cleanup_hoare (ys.map digitSymbol) hd) wire before ha
  have hc : HoareTime cleanupThree (fun v => v = before) (fun v => v = after) (2*ys.length+6) := by
    apply hh.consequence (fun _ h => h) _ (by simp)
    rintro v ⟨w,rfl,rfl⟩
    rw [Placement.replace,he,← hf]
    exact Placement.view _ _
  exact FamilyPlacementAlphabet.extend_hoare hc (workspace e xs)

def program (e : Expr) : Program (TapeCount e) (States e) q :=
  seq (seq (Placement.placed (RadixLinearCombination.program e) (arithmeticPlacement e))
    (extend (RadixToBinary.convertProgram (Fact.out : q.Prime).two_le) (AuxTapes e)))
    (extend cleanupThree (AuxTapes e))

theorem compute_hoare (e : Expr) (xs : ℕ → List (Fin q)) (b : ℕ) (hw : ∀ i, (xs i).length = b) :
    HoareTime (program e) (fun v => v = input e xs) (fun v => v = output e xs)
      (RadixLinearCombination.runtime e b+10*value (RadixLinearCombination.result e xs)+8*b+22) := by
  have hh := ((arithmetic_hoare e xs b hw).seq (conversion_hoare e xs (RadixLinearCombination.result e xs))).seq
    (cleanup_hoare e xs _ 1 (RadixLinearCombination.result e xs))
  exact hh.consequence (fun _ h => h) (fun _ h => h) (by rw [RadixLinearCombination.result_length e xs b hw]; omega)

/-- All arithmetic, canonical conversion and final cleanup are linear in the
radix modulus, with a constant determined solely by the fixed expression. -/
theorem compute_hoare_linear (e : Expr) (xs : ℕ → List (Fin q)) (b : ℕ) (hw : ∀ i, (xs i).length = b) :
    HoareTime (program e) (fun v => v = input e xs) (fun v => v = output e xs)
      ((RadixLinearCombination.linearConstant e+40)*q^b) := by
  apply (compute_hoare e xs b hw).consequence (fun _ h => h) (fun _ h => h)
  have hc := RadixLinearCombination.runtime_le (q := q) e b
  have hv := value_lt (Fact.out : q.Prime).two_le (RadixLinearCombination.result e xs)
  rw [RadixLinearCombination.result_length e xs b hw] at hv
  have hb := RadixToBinaryData.width_le_power (Fact.out : q.Prime).two_le b
  have hp : 1 ≤ q^b := Nat.one_le_pow _ _ (by have := (Fact.out : q.Prime).two_le; omega)
  nlinarith

theorem bits_canonical (e : Expr) (xs : ℕ → List (Fin q)) : GrowingCounterData.Canonical (bits e xs) :=
  RadixToBinaryData.output_canonical _

theorem bits_value (e : Expr) (he : RadixLinearCombination.Valid (q := q) e) (xs : ℕ → List (Fin q))
    (b : ℕ) (hw : ∀ i, (xs i).length = b) :
    (Counter.value (bits e xs) : ZMod (q^b)) = RadixLinearCombination.valueMod b e xs := by
  rw [bits,RadixToBinaryData.output_value]
  exact RadixLinearCombination.result_value e he xs b hw

theorem bits_lt (e : Expr) (xs : ℕ → List (Fin q)) (b : ℕ) (hw : ∀ i, (xs i).length = b) :
    Counter.value (bits e xs) < q^b := by
  rw [bits,RadixToBinaryData.output_value]
  have hh := value_lt (Fact.out : q.Prime).two_le (RadixLinearCombination.result e xs)
  simpa only [RadixLinearCombination.result_length e xs b hw] using hh

/-- The actual first tape is the encoded canonical binary descriptor. -/
theorem output_binary (e : Expr) (xs : ℕ → List (Fin q)) :
    (output e xs).head (Fin.castAdd (AuxTapes e) (0 : Fin 3)) = 1 ∧
    (output e xs).tape (Fin.castAdd (AuxTapes e) (0 : Fin 3)) =
      fun z => (RadixToBinary.binaryEncoding (q := q)).encode (CountedCopyReuse.binary (bits e xs) z) := by
  simp only [output,bank,Tapes.append,Fin.addCases_left]
  exact ⟨rfl,rfl⟩

/-- Both converter scratch tapes are fully blank, including former marker cells. -/
theorem output_scratch (e : Expr) (xs : ℕ → List (Fin q)) :
    let v := output e xs
    v.head (Fin.castAdd (AuxTapes e) (1 : Fin 3)) = 0 ∧
    v.tape (Fin.castAdd (AuxTapes e) (1 : Fin 3)) = (fun _ => blank) ∧
    v.head (Fin.castAdd (AuxTapes e) (2 : Fin 3)) = 0 ∧
    v.tape (Fin.castAdd (AuxTapes e) (2 : Fin 3)) = (fun _ => blank) := by
  simp [output,bank,Tapes.append,word,putWord]

/-- Every marked leaf source and all arithmetic scratch survive literally in
the restored workspace, with the exact heads from the supplied initial bank. -/
theorem output_workspace (e : Expr) (xs : ℕ → List (Fin q)) :
    Placement.extra (Equiv.refl (Fin (3+AuxTapes e))) (output e xs) = workspace e xs := by
  unfold Placement.extra output bank
  cases hw : workspace e xs
  simp [Tapes.append]

/-- Fixed coefficient lists have explicit control-count dependent runtime. -/
theorem list_hoare (terms : List (ℕ × ℚ)) (xs : ℕ → List (Fin q)) (b : ℕ) (hw : ∀ i, (xs i).length = b) :
    HoareTime (program (RadixLinearCombination.ofList terms))
      (fun v => v = input (RadixLinearCombination.ofList terms) xs)
      (fun v => v = output (RadixLinearCombination.ofList terms) xs) ((34*terms.length+47)*q^b) := by
  simpa only [RadixLinearCombination.ofList,RadixLinearCombination.ofTerms_linearConstant,Nat.add_assoc]
    using compute_hoare_linear (RadixLinearCombination.ofList terms) xs b hw

theorem list_bits_value (terms : List (ℕ × ℚ)) (ht : ∀ term ∈ terms, term.2.den < q)
    (xs : ℕ → List (Fin q)) (b : ℕ) (hw : ∀ i, (xs i).length = b) :
    (Counter.value (bits (RadixLinearCombination.ofList terms) xs) : ZMod (q^b)) =
      (terms.map (fun term => Swap.Modular.ratMod (q^b) term.2*(value (xs term.1) : ZMod (q^b)))).sum := by
  rw [bits_value _ (RadixLinearCombination.ofList_valid terms ht) xs b hw,RadixLinearCombination.ofList_value]

omit [Fact q.Prime] in
theorem list_tapeCount (terms : List (ℕ × ℚ)) : TapeCount (RadixLinearCombination.ofList terms) = 3*terms.length+4 := by
  have hh := RadixLinearCombination.ofTerms_tapeCount (0,0) terms
  dsimp only [TapeCount,RadixLinearCombination.TapeCount,RadixLinearCombination.ofList] at hh ⊢
  omega

end IntegerMultBounds.Machine.RadixLinearCombinationBinary
