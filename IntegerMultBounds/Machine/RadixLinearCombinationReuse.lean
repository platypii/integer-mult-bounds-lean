import IntegerMultBounds.Machine.MarkedBinaryCleanup

/-! Repeated shared-control evaluation with physical previous-result erasure.
The caller may advance the shared controls between calls; stale leaf copies and
the old binary descriptor are charged and removed by the next finite program. -/
namespace IntegerMultBounds.Machine.RadixLinearCombinationReuse

open RadixLinearCombinationRefresh (Expr controls leaves)
open RadixDigits
open MarkedWordCleanup (one word)
variable {c q : ℕ}

abbrev TapeCount (e : Expr c) := RadixLinearCombinationShared.TapeCount e

/-- Current shared controls, stale expression sources, and an actual old binary
word. This exact tape state is independent of the old word's semantic value. -/
def state (e : Expr c) (xs old : ℕ → List (Fin q)) (bs : List Bool) : Tapes (TapeCount e) q :=
  (controls xs).append (RadixLinearCombinationBinary.bank e.erase old ((RadixToBinary.binaryState q bs).tape 0) 1 [])

private def clearBinary (e : Expr c) : Program (RadixLinearCombinationBinary.TapeCount e.erase) 4 q :=
  extend (extend MarkedBinaryCleanup.program 2) (RadixLinearCombination.AuxTapes e.erase)

private theorem bank_pair (e : Expr c) (old : ℕ → List (Fin q)) (f : ℤ → Fin (q+4)) (p : ℤ) :
    ((one f p).append (⟨fun _ => 0,fun _ _ => blank⟩ : Tapes 2 q)).append (RadixLinearCombination.workspace e.erase old) =
      RadixLinearCombinationBinary.bank e.erase old f p [] := by
  unfold RadixLinearCombinationBinary.bank
  congr 1
  unfold one Tapes.append
  congr 1 <;> funext i <;> fin_cases i <;> rfl

private theorem clear_binary_hoare (e : Expr c) (old : ℕ → List (Fin q)) (bs : List Bool) :
    HoareTime (clearBinary e)
      (fun v => v = RadixLinearCombinationBinary.bank e.erase old ((RadixToBinary.binaryState q bs).tape 0) 1 [])
      (fun v => v = RadixLinearCombinationBinary.input e.erase old) (2*bs.length+4) := by
  have hb : RadixToBinary.binaryState q bs = one ((RadixToBinary.binaryState q bs).tape 0) 1 := rfl
  have h := FamilyPlacementAlphabet.extend_hoare
    (FamilyPlacementAlphabet.extend_hoare (MarkedBinaryCleanup.cleanup_hoare (q := q) bs)
      (⟨fun _ => 0,fun _ _ => blank⟩ : Tapes 2 q)) (RadixLinearCombination.workspace e.erase old)
  rw [hb,bank_pair,bank_pair] at h
  exact h

def resetProgram (e : Expr c) : Program (TapeCount e) 4 q :=
  Placement.placed (clearBinary e)
    (finAddFlip : Fin (RadixLinearCombinationBinary.TapeCount e.erase+c) ≃ Fin (TapeCount e))

/-- Cleanup preserves the entire current control bank and stale leaf bank. -/
theorem reset_hoare (e : Expr c) (xs old : ℕ → List (Fin q)) (bs : List Bool) :
    HoareTime (resetProgram e) (fun v => v = state e xs old bs)
      (fun v => v = RadixLinearCombinationShared.input e xs old) (2*bs.length+4) := by
  let wire : Fin (RadixLinearCombinationBinary.TapeCount e.erase+c) ≃ Fin (TapeCount e) := finAddFlip
  have hb : Placement.active wire (state e xs old bs) =
      RadixLinearCombinationBinary.bank e.erase old ((RadixToBinary.binaryState q bs).tape 0) 1 [] := by
    unfold Placement.active wire state
    congr 1 <;> funext i <;> simp [Tapes.append] <;> rfl
  have ha : Placement.active wire (RadixLinearCombinationShared.input e xs old) =
      RadixLinearCombinationBinary.input e.erase old := by
    unfold Placement.active wire RadixLinearCombinationShared.input
    congr 1 <;> funext i <;> simp [Tapes.append] <;> rfl
  have hf : Placement.extra wire (state e xs old bs) =
      Placement.extra wire (RadixLinearCombinationShared.input e xs old) := by
    unfold Placement.extra wire state RadixLinearCombinationShared.input
    congr 1 <;> funext i <;> simp [Tapes.append]
  apply (Placement.hoare_at (clear_binary_hoare e old bs) wire _ hb).consequence (fun _ h => h) _ le_rfl
  rintro v ⟨w,rfl,rfl⟩
  rw [Placement.replace,hf,← ha]
  exact Placement.view _ _

variable [Fact q.Prime]

abbrev States (e : Expr c) := 4+RadixLinearCombinationShared.States e

def program (e : Expr c) : Program (TapeCount e) (States e) q :=
  seq (resetProgram e) (RadixLinearCombinationShared.program e)

/-- Full reuse with the precise stale binary-word erasure charge. -/
theorem compute_hoare (e : Expr c) (xs old : ℕ → List (Fin q)) (bs : List Bool) (b : ℕ)
    (hw : ∀ i, (xs i).length = b) (ho : ∀ i : Fin c, (old i.val).length ≤ b) :
    HoareTime (program e) (fun v => v = state e xs old bs)
      (fun v => v = RadixLinearCombinationShared.output e xs)
      (2*bs.length+5+(13*leaves e+RadixLinearCombination.linearConstant e.erase+40)*q^b) :=
  (reset_hoare e xs old bs).seq (RadixLinearCombinationShared.compute_hoare_linear e xs old b hw ho)

/-- A binary output fitting the current modulus keeps full reuse linear. -/
theorem compute_hoare_linear (e : Expr c) (xs old : ℕ → List (Fin q)) (bs : List Bool) (b : ℕ)
    (hw : ∀ i, (xs i).length = b) (ho : ∀ i : Fin c, (old i.val).length ≤ b) (hb : bs.length ≤ q^b) :
    HoareTime (program e) (fun v => v = state e xs old bs)
      (fun v => v = RadixLinearCombinationShared.output e xs)
      ((13*leaves e+RadixLinearCombination.linearConstant e.erase+47)*q^b) := by
  apply (compute_hoare e xs old bs b hw ho).consequence (fun _ h => h) (fun _ h => h)
  have hp : 1 ≤ q^b := Nat.one_le_pow _ _ (by have := (Fact.out : q.Prime).two_le; omega)
  nlinarith

/-- The compiler's own previous output satisfies the reuse width condition. -/
theorem bits_length_le (e : Expr c) (old : ℕ → List (Fin q)) (b : ℕ) (hw : ∀ i, (old i).length = b) :
    (RadixLinearCombinationBinary.bits e.erase old).length ≤ q^b := by
  have hl := GrowingCounterData.canonical_width (RadixLinearCombinationBinary.bits e.erase old)
    (RadixLinearCombinationBinary.bits_canonical e.erase old)
  have hv := RadixLinearCombinationBinary.bits_lt e.erase old b hw
  have hn := Nat.log_le_self 2 (Counter.value (RadixLinearCombinationBinary.bits e.erase old))
  rw [← Nat.log2_eq_log_two] at hn
  omega

/-- Prior output, with only the common control bank advanced externally. Every
stale internal word is subsequently refreshed by this program. -/
theorem compute_after_advance (e : Expr c) (xs old : ℕ → List (Fin q)) (b : ℕ)
    (hw : ∀ i, (xs i).length = b) (ho : ∀ i, (old i).length = b) :
    HoareTime (program e)
      (fun v => v = (controls xs).append (RadixLinearCombinationBinary.output e.erase old))
      (fun v => v = RadixLinearCombinationShared.output e xs)
      ((13*leaves e+RadixLinearCombination.linearConstant e.erase+47)*q^b) :=
  compute_hoare_linear e xs old (RadixLinearCombinationBinary.bits e.erase old) b hw
    (fun i => (ho i.val).le) (bits_length_le e old b ho)

theorem compute_finite_after_advance (e : Expr c) (seed : Fin c) (xs old : Fin c → List (Fin q)) (b : ℕ)
    (hw : ∀ i, (xs i).length = b) (ho : ∀ i, (old i).length = b) :
    HoareTime (program e)
      (fun v => v = (controls (RadixLinearCombinationShared.read seed xs)).append
        (RadixLinearCombinationBinary.output e.erase (RadixLinearCombinationShared.read seed old)))
      (fun v => v = RadixLinearCombinationShared.output e (RadixLinearCombinationShared.read seed xs))
      ((13*leaves e+RadixLinearCombination.linearConstant e.erase+47)*q^b) :=
  compute_after_advance e _ _ b (RadixLinearCombinationShared.read_width seed xs b hw)
    (RadixLinearCombinationShared.read_width seed old b ho)

end IntegerMultBounds.Machine.RadixLinearCombinationReuse
