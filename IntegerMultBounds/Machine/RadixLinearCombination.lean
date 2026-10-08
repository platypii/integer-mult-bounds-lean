import IntegerMultBounds.Machine.RadixAddReusable
import IntegerMultBounds.Machine.RadixRationalBinary

/-! A fixed finite arithmetic-expression compiler for rational linear
combinations of marked radix controls. Every leaf executes the fixed rational
kernel; every addition executes modular radix addition and erases both temporary
operands. The complete bank restores every original source and scratch head.
Each leaf has its own supplied marked source tape, including the zero seed.
Repeated logical indices do not imply a free physical copy or refresh operation. -/
namespace IntegerMultBounds.Machine.RadixLinearCombination

open RadixDigits
open MarkedWordCleanup (one word marked)

inductive Expr where
  | term (index : ℕ) (coefficient : ℚ)
  | add (left right : Expr)

def AuxTapes : Expr → ℕ
  | .term _ _ => 1
  | .add l r => (1+AuxTapes l)+(1+AuxTapes r)

abbrev TapeCount (e : Expr) := 1+AuxTapes e

def States : Expr → ℕ
  | .term _ r => 2+(2*r.num.natAbs+r.den+1)+2
  | .add l r => (States l+States r)+18

variable {q : ℕ} [Fact q.Prime]

def result : (e : Expr) → (ℕ → List (Fin q)) → List (Fin q)
  | .term i r, xs => RadixRationalBinary.result r (xs i)
  | .add l r, xs => RadixAddReusable.result (Fact.out : q.Prime).two_le (result l xs) (result r xs)

/-- The only persistent words are marked original controls. All intermediate
slots are blank; the first tape contains the explicitly supplied result word. -/
def bank : (e : Expr) → (ℕ → List (Fin q)) → List (Fin q) → Tapes (TapeCount e) q
  | .term i _, xs, zs => (one (word (zs.map digitSymbol)) 0).append (one (marked ((xs i).map digitSymbol)) 1)
  | .add l r, xs, zs => (one (word (zs.map digitSymbol)) 0).append ((bank l xs []).append (bank r xs []))

/-- Fixed slot pairing selects the two child results and the new parent result. -/
def additionPlacement (l r : Expr) :
    Fin (3+(AuxTapes l+AuxTapes r)) ≃ Fin ((TapeCount l+TapeCount r)+1) :=
  FamilyPlacement.withFrame (r := 1) (FamilyPlacement.pair
    (Equiv.refl (Fin (1+AuxTapes l))) (Equiv.refl (Fin (1+AuxTapes r))))

/-- First tape and all remaining tapes of every bank are a literal append. -/
def workspace : (e : Expr) → (ℕ → List (Fin q)) → Tapes (AuxTapes e) q
  | .term i _, xs => one (marked ((xs i).map digitSymbol)) 1
  | .add l r, xs => (bank l xs []).append (bank r xs [])

omit [Fact q.Prime] in
theorem bank_split (e : Expr) (xs : ℕ → List (Fin q)) (zs : List (Fin q)) :
    bank e xs zs = (one (word (zs.map digitSymbol)) 0).append (workspace e xs) := by cases e <;> rfl

omit [Fact q.Prime] in
private theorem combination_bank (l r : Expr) (xs : ℕ → List (Fin q)) (us vs zs : List (Fin q)) :
    Placement.combine (additionPlacement l r) (RadixAddReusable.bank us vs zs)
      ((workspace l xs).append (workspace r xs)) =
      ((bank l xs us).append (bank r xs vs)).append (one (word (zs.map digitSymbol)) 0) := by
  unfold additionPlacement
  have hb : RadixAddReusable.bank us vs zs =
      ((one (word (us.map digitSymbol)) 0).append (one (word (vs.map digitSymbol)) 0)).append
      (one (word (zs.map digitSymbol)) 0) := by
    unfold RadixAddReusable.bank one Tapes.append
    congr 1 <;> funext i <;> fin_cases i <;> rfl
  rw [hb,FamilyPlacementAlphabet.combine_withFrame,FamilyPlacementAlphabet.combine_pair,bank_split l,bank_split r]
  rfl

omit [Fact q.Prime] in
private theorem flip_bank {s t : ℕ} (v : Tapes s q) (w : Tapes t q) :
    (v.append w).reindex (finAddFlip : Fin (s+t) ≃ Fin (t+s)) = w.append v := by
  let e : Fin (s+t) ≃ Fin (t+s) := finAddFlip
  have ha : Placement.active e (w.append v) = v := by
    cases v; simp [Placement.active,e,Tapes.append,finAddFlip_apply_castAdd]
  have he : Placement.extra e (w.append v) = w := by
    cases w; simp [Placement.extra,e,Tapes.append,finAddFlip_apply_natAdd]
  simpa only [ha,he,Placement.combine] using Placement.view e (w.append v)

omit [Fact q.Prime] in
private theorem exact_reindex {t s states : ℕ} {M : Program t states q} {v w : Tapes t q} {cost : ℕ}
    (h : HoareTime M (fun x => x = v) (fun x => x = w) cost) (e : Fin t ≃ Fin s) :
    HoareTime (reindex M e) (fun x => x = v.reindex e) (fun x => x = w.reindex e) cost := by
  apply (h.reindex e).consequence _ _ le_rfl
  · rintro x rfl; exact ⟨_,rfl,rfl⟩
  · rintro x ⟨y,rfl,rfl⟩; rfl

omit [Fact q.Prime] in
private theorem exact_placed {s u t states : ℕ} {M : Program s states q} {v w : Tapes s q} {cost : ℕ}
    (h : HoareTime M (fun x => x = v) (fun x => x = w) cost) (e : Fin (s+u) ≃ Fin t) (frame : Tapes u q) :
    HoareTime (Placement.placed M e) (fun x => x = Placement.combine e v frame)
      (fun x => x = Placement.combine e w frame) cost := by
  apply (Placement.hoare_at h e (Placement.combine e v frame) (Placement.active_combine _ _ _)).consequence
    (fun _ h => h) _ le_rfl
  rintro x ⟨small,hsmall,rfl⟩
  subst small
  simp only [Placement.replace,Placement.extra_combine]

/-- The transition table depends only on the fixed expression and prime radix. -/
def program : (e : Expr) → Program (TapeCount e) (States e) q
  | .term _ r => reindex (RadixRationalBinary.arithmeticProgram r) (Equiv.swap 0 1)
  | .add l r => reindex
      (seq (extend (FamilyPlacementAlphabet.sequence (program l) (program r)) 1)
        (Placement.placed (RadixAddReusable.consumeProgram q (Fact.out : q.Prime).two_le) (additionPlacement l r)))
      (finAddFlip : Fin ((TapeCount l+TapeCount r)+1) ≃ Fin (1+(TapeCount l+TapeCount r)))

def runtime : Expr → ℕ → ℕ
  | .term _ _, b => 2*b+5
  | .add l r, b => runtime l b+runtime r b+6*b+21

theorem result_length (e : Expr) (xs : ℕ → List (Fin q)) (b : ℕ) (hw : ∀ i, (xs i).length = b) :
    (result e xs).length = b := by
  induction e with
  | term i r => simpa only [result,RadixRationalBinary.result,RadixRationalData.digits_length] using hw i
  | add l r hl hr => exact (RadixAddReusable.result_length _ _ _ (hl.trans hr.symm)).trans hl

/-- Every intermediate arithmetic result is consumed and erased. The endpoint
contains only the requested result and the original marked source controls. -/
theorem compute_hoare (e : Expr) (xs : ℕ → List (Fin q)) (b : ℕ) (hw : ∀ i, (xs i).length = b) :
    HoareTime (program e) (fun v => v = bank e xs []) (fun v => v = bank e xs (result e xs)) (runtime e b) := by
  induction e with
  | term i r =>
    have hh := exact_reindex (RadixRationalBinary.arithmetic_stage_hoare r (xs i)) (Equiv.swap 0 (1 : Fin 2))
    have hi : (RadixRationalBinary.pair (RadixRationalBinary.source (xs i)) (fun _ => blank) 1 0).reindex (Equiv.swap 0 1) =
        bank (.term i r) xs [] := by
      unfold RadixRationalBinary.pair Copy.tapes Copy.cfg Config.tapes Tapes.reindex bank one Tapes.append
      congr 1 <;> funext j <;> fin_cases j <;> rfl
    have ho : (RadixRationalBinary.pair (RadixRationalBinary.source (xs i)) (RadixRationalBinary.radix (RadixRationalBinary.result r (xs i))) 1 0).reindex (Equiv.swap 0 1) =
        bank (.term i r) xs (result (.term i r) xs) := by
      unfold RadixRationalBinary.pair Copy.tapes Copy.cfg Config.tapes Tapes.reindex bank one Tapes.append
      congr 1 <;> funext j <;> fin_cases j <;> rfl
    simpa only [hi,ho,hw i,program,runtime,TapeCount,AuxTapes,States] using hh
  | add l r hl hr =>
    have hp := FamilyPlacementAlphabet.extend_hoare (FamilyPlacementAlphabet.sequence_hoare hl hr)
      (one (word ([] : List (Fin (q+4)))) 0)
    have he := exact_placed (RadixAddReusable.consume_hoare (Fact.out : q.Prime).two_le (result l xs) (result r xs)
      ((result_length l xs b hw).trans (result_length r xs b hw).symm)) (additionPlacement l r)
      ((workspace l xs).append (workspace r xs))
    rw [combination_bank,combination_bank,result_length l xs b hw] at he
    have hh := exact_reindex (hp.seq he) (finAddFlip : Fin ((TapeCount l+TapeCount r)+1) ≃ Fin (1+(TapeCount l+TapeCount r)))
    rw [flip_bank,flip_bank] at hh
    exact hh.consequence (fun _ h => h) (fun _ h => h) (by simp only [runtime]; omega)

/-- Denominators are compile-time side conditions, never an arithmetic oracle. -/
def Valid : Expr → Prop
  | .term _ r => r.den < q
  | .add l r => Valid l ∧ Valid r

def valueMod (b : ℕ) : Expr → (ℕ → List (Fin q)) → ZMod (q^b)
  | .term i r, xs => Swap.Modular.ratMod (q^b) r * (value (xs i) : ZMod (q^b))
  | .add l r, xs => valueMod b l xs+valueMod b r xs

theorem result_value (e : Expr) (he : Valid (q := q) e) (xs : ℕ → List (Fin q)) (b : ℕ)
    (hw : ∀ i, (xs i).length = b) : (value (result e xs) : ZMod (q^b)) = valueMod b e xs := by
  induction e with
  | term i r =>
    have hh := RadixRational.output_ratMod r he (xs i)
    rw [hw i] at hh
    exact hh
  | add l r hl hr =>
    unfold result
    rw [RadixAddReusable.result_value _ _ _ ((result_length l xs b hw).trans (result_length r xs b hw).symm),
      result_length l xs b hw,ZMod.natCast_mod,Nat.cast_add,hl he.1,hr he.2]
    rfl

def linearConstant : Expr → ℕ
  | .term _ _ => 7
  | .add l r => linearConstant l+linearConstant r+27

theorem runtime_le (e : Expr) (b : ℕ) : runtime e b ≤ linearConstant e*q^b := by
  have hb := RadixToBinaryData.width_le_power (Fact.out : q.Prime).two_le b
  have hp : 1 ≤ q^b := Nat.one_le_pow _ _ (by have := (Fact.out : q.Prime).two_le; omega)
  induction e with
  | term i r => dsimp [runtime,linearConstant]; omega
  | add l r hl hr => dsimp [runtime,linearConstant]; nlinarith

theorem compute_hoare_linear (e : Expr) (xs : ℕ → List (Fin q)) (b : ℕ) (hw : ∀ i, (xs i).length = b) :
    HoareTime (program e) (fun v => v = bank e xs []) (fun v => v = bank e xs (result e xs)) (linearConstant e*q^b) :=
  (compute_hoare e xs b hw).consequence (fun _ h => h) (fun _ h => h) (runtime_le e b)

/-- Fixed indexed coefficient list, with a physical zero term as the seed.
The seed uses control zero only to obtain the common word width. -/
def ofTerms (first : ℕ × ℚ) : List (ℕ × ℚ) → Expr
  | [] => .term first.1 first.2
  | next::rest => .add (.term first.1 first.2) (ofTerms next rest)

def ofList (terms : List (ℕ × ℚ)) : Expr := ofTerms (0,0) terms

omit [Fact q.Prime] in
theorem ofTerms_valid (first : ℕ × ℚ) (terms : List (ℕ × ℚ)) (hf : first.2.den < q)
    (ht : ∀ term ∈ terms, term.2.den < q) : Valid (q := q) (ofTerms first terms) := by
  induction terms generalizing first with
  | nil => exact hf
  | cons next rest ih => exact ⟨hf,ih next (ht next (by simp)) (fun term hm => ht term (by simp [hm]))⟩

theorem ofList_valid (terms : List (ℕ × ℚ)) (ht : ∀ term ∈ terms, term.2.den < q) :
    Valid (q := q) (ofList terms) :=
  ofTerms_valid (0,0) terms (by simpa using (Fact.out : q.Prime).one_lt) ht

omit [Fact q.Prime] in
theorem ofTerms_value (b : ℕ) (first : ℕ × ℚ) (terms : List (ℕ × ℚ)) (xs : ℕ → List (Fin q)) :
    valueMod b (ofTerms first terms) xs =
      Swap.Modular.ratMod (q^b) first.2*(value (xs first.1) : ZMod (q^b))+
        (terms.map (fun term => Swap.Modular.ratMod (q^b) term.2*(value (xs term.1) : ZMod (q^b)))).sum := by
  induction terms generalizing first with
  | nil => simp [ofTerms,valueMod]
  | cons next rest ih => simp [ofTerms,valueMod,ih]

omit [Fact q.Prime] in
theorem ofList_value (b : ℕ) (terms : List (ℕ × ℚ)) (xs : ℕ → List (Fin q)) :
    valueMod b (ofList terms) xs =
      (terms.map (fun term => Swap.Modular.ratMod (q^b) term.2*(value (xs term.1) : ZMod (q^b)))).sum := by
  simp [ofList,ofTerms_value,Swap.Modular.ratMod_zero]

omit [Fact q.Prime] in
theorem ofTerms_tapeCount (first : ℕ × ℚ) (terms : List (ℕ × ℚ)) :
    TapeCount (ofTerms first terms) = 3*terms.length+2 := by
  induction terms generalizing first with
  | nil => rfl
  | cons next rest ih =>
    have hh := ih next
    simp only [TapeCount,ofTerms,AuxTapes,List.length_cons] at hh ⊢
    omega

omit [Fact q.Prime] in
theorem ofTerms_linearConstant (first : ℕ × ℚ) (terms : List (ℕ × ℚ)) :
    linearConstant (ofTerms first terms) = 34*terms.length+7 := by
  induction terms generalizing first with
  | nil => rfl
  | cons next rest ih => simp [ofTerms,linearConstant,ih]; omega

/-- A coefficient list is compiled into actual arithmetic, with a full-bank
postcondition and a coefficient-count dependent constant independent of b. -/
theorem list_hoare (terms : List (ℕ × ℚ)) (xs : ℕ → List (Fin q)) (b : ℕ)
    (hw : ∀ i, (xs i).length = b) :
    HoareTime (program (ofList terms)) (fun v => v = bank (ofList terms) xs [])
      (fun v => v = bank (ofList terms) xs (result (ofList terms) xs)) ((34*terms.length+7)*q^b) := by
  simpa only [ofList,ofTerms_linearConstant] using compute_hoare_linear (ofList terms) xs b hw

/-- Mathematical value of the physically produced list-compiled radix word. -/
theorem list_result_value (terms : List (ℕ × ℚ)) (ht : ∀ term ∈ terms, term.2.den < q)
    (xs : ℕ → List (Fin q)) (b : ℕ) (hw : ∀ i, (xs i).length = b) :
    (value (result (ofList terms) xs) : ZMod (q^b)) =
      (terms.map (fun term => Swap.Modular.ratMod (q^b) term.2*(value (xs term.1) : ZMod (q^b)))).sum := by
  rw [result_value _ (ofList_valid terms ht) xs b hw,ofList_value]

end IntegerMultBounds.Machine.RadixLinearCombination
