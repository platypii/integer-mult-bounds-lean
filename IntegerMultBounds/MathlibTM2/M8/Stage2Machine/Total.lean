module

public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Bound
public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Padded

/-!
# The stage-2 supplier as the root of the binary interchange

The binary wrappers of the cost chain run their root descriptor through one fixed machine with a
paid time budget. Here that machine is the stage-2 supplier (`Supplier.runs`). Its run time is at
most `C V max(1,e)^τ₂`, so the budget `cost d` is that bound rounded down (`runs`); it is uniformly
`O(V max(1,e)^τ₂)` (`uniform_bound`), with `τ₂ = 1 - 123899714039/10¹⁵` (`tau`).

The family's program counters take a width `Capacity` (an instance at the seam). The supplier's
tape and state counts are sealed (`count`, `states`): they are large closed numbers, and a
consumer comparing them structurally must never unfold them. The supplier keeps its caller's tapes
and pads them with blank private tapes (`input_pad`), so a program on the caller runs on the
supplier's bank (`private_hoare`) and a sparse header bank stays sparse (`Padded.headerBank_eq`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Total

noncomputable section
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open SharedPlacementAlphabet (setTape)
open M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord)
open M8.Machine.ArbitraryWidthHighExchangeJoin (exchangeCount movementCount)
open M8.Machine.ArbitraryWidthHighCommonFallback (elementaryCount)
open RevMachine
variable {t : ℕ}

/-- **The stage-2 exponent** `τ₂`. -/
def tau : ℝ := 1 - 123899714039 / 10 ^ 15

theorem tau_range : 0 < tau ∧ tau < 1 := by norm_num [tau]

/-! ### Relabelled tape counts -/

/-- Tapes, relabelled along an equal tape count. -/
def recast {n m a : ℕ} (h : n = m) (v : Tapes n a) : Tapes m a :=
  ⟨fun i => v.head (Fin.cast h.symm i), fun i => v.tape (Fin.cast h.symm i)⟩

/-- A program, relabelled along equal tape and state counts. -/
def recastProgram {n m q r a : ℕ} (h : n = m) (hq : q = r) (M : Program n q a) : Program m r a :=
  hq ▸ h ▸ M

theorem hoare_recast {n m q r a b : ℕ} (h : n = m) (hq : q = r) {M : Program n q a} {v w : Tapes n a}
    (hM : HoareTime M (fun z => z = v) (fun z => z = w) b) :
    HoareTime (recastProgram h hq M) (fun z => z = recast h v) (fun z => z = recast h w) b := by
  subst h hq; exact hM

/-- The state count of a program family. -/
def statesOf {α β : Type} {n q a : ℕ} (_ : α → β → Program n q a) : ℕ := q

theorem _root_.IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Padded.recast {s u u' a : ℕ} (h : u = u')
    {F : Tapes s a → Tapes u a} {ℓ : Fin s → Fin u} (hp : Padded F ℓ) :
    Padded (fun c => recast h (F c)) (fun j => Fin.cast h (ℓ j)) := by
  subst h; exact hp

/-- A width for the family's program counters. -/
class Capacity where
  bits : ℕ
  fits : Fintype.card (Graph.PC (RevHalf.pcs rev97m).length) ≤ 2 ^ bits

/-- The bits of the family's program counters, sealed. -/
irreducible_def pcBits : ℕ := Fintype.card (Graph.PC (RevHalf.pcs rev97m).length)

/-- The family's program counters fit `pcBits` bits. -/
theorem pcCapacity : Fintype.card (Graph.PC (RevHalf.pcs rev97m).length) ≤ 2 ^ pcBits := by
  rw [pcBits_def]; exact Bound.le_two_pow _

/-- The supplier's tape count over a caller of `t` tapes, sealed, so that a closed tape count is
never unfolded. -/
irreducible_def count [Capacity] (t : ℕ) : ℕ := Supplier.count Capacity.fits t

/-- The supplier's state count, sealed. -/
irreducible_def states [Capacity] (t : ℕ) : ℕ := statesOf (Supplier.program Capacity.fits (t := t))

variable [Capacity]
local notation "capacity" => Capacity.fits

theorem exists_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ {t : ℕ} (caller : Tapes t prime) (headers : Fin 6 → Fin t) (source : Fin t)
      (d : Descriptor) (hs : Fin 6 → List Bool), d.Positive → RecursiveDimensionBank.Headers d hs →
      (∀ i, caller.tape (headers i) = RadixZeroFill.encodedBinary (hs i)) → (∀ i, caller.head (headers i) = 1) →
      ∀ x : Fin (volume prime d) → ZMod 2, caller.tape source = sourceWord x → caller.head source = 0 →
      ∃ c : ℕ, (c : ℝ) ≤ C * volume prime d * ((max 1 d.width : ℕ) : ℝ) ^ HighBody.tau₂ HighCost.K ∧
        HoareTime (Supplier.program capacity headers source) (fun z => z = Supplier.input capacity caller)
          (fun z => z = Supplier.input capacity (setTape caller source
            (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd d.rows) x)) 0)) c :=
  Supplier.runs capacity (Spec.familySpec capacity) (HighCost.exponents Bound.tau_eq)

/-- The constant of the supplier's uniform bound. -/
def constant : ℝ := Classical.choose exists_constant

theorem constant_pos : 0 < constant := (Classical.choose_spec exists_constant).1

/-- The supplier's time budget on a descriptor. -/
def cost (d : Descriptor) : ℕ :=
  ⌊constant * volume prime d * ((max 1 d.width : ℕ) : ℝ) ^ tau⌋₊

/-- The caller with the supplier's blank private banks. -/
def input (caller : Tapes t prime) : Tapes (count t) prime :=
  recast (count_def t).symm (Supplier.input capacity caller)

/-- The supplier's program. -/
def program (headers : Fin 6 → Fin t) (source : Fin t) : Program (count t) (states t) prime :=
  recastProgram (count_def t).symm (states_def t).symm (Supplier.program capacity headers source)

/-- The slot of a caller tape among the supplier's banks. -/
def slot (j : Fin t) : Fin (count t) := Fin.cast (count_def t).symm (Supplier.slot capacity (Fin.castAdd 2 j))

omit [Capacity] in
theorem tau_eq : HighBody.tau₂ HighCost.K = tau := by rw [Bound.tau₂_eq]; rfl

/-- **The supplier's run** within its budget. -/
theorem runs (caller : Tapes t prime) (headers : Fin 6 → Fin t) (source : Fin t)
    (d : Descriptor) (hs : Fin 6 → List Bool) (hp : d.Positive)
    (hv : RecursiveDimensionBank.Headers d hs)
    (ht : ∀ i, caller.tape (headers i) = RadixZeroFill.encodedBinary (hs i))
    (hh : ∀ i, caller.head (headers i) = 1)
    (x : Fin (volume prime d) → ZMod 2)
    (hf : caller.tape source = sourceWord x) (hhead : caller.head source = 0) :
    HoareTime (program headers source) (fun w => w = input caller)
      (fun w => w = input (setTape caller source
        (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd d.rows) x)) 0)) (cost d) := by
  obtain ⟨c, hc, h⟩ := (Classical.choose_spec exists_constant).2 caller headers source d hs hp hv ht hh
    x hf hhead
  exact (hoare_recast (count_def t).symm (states_def t).symm h).consequence (fun _ h => h) (fun _ h => h) (Nat.le_floor (hc.trans_eq
    (congrArg (fun r : ℝ => constant * (volume prime d : ℝ) * ((max 1 d.width : ℕ) : ℝ) ^ r) tau_eq)))

/-- **The supplier's budget** is uniformly `O(V max(1,e)^τ₂)`. -/
theorem uniform_bound : ∃ C : ℝ, 0 < C ∧ ∀ d : Descriptor,
    (cost d : ℝ) ≤ C * volume prime d * ((max 1 d.width : ℕ) : ℝ) ^ tau :=
  ⟨constant, constant_pos, fun _ => Nat.floor_le (mul_nonneg (mul_nonneg
    (constant_pos).le (Nat.cast_nonneg _)) (Real.rpow_nonneg (Nat.cast_nonneg _) _))⟩

/-! ### The private banks -/

/-- A program on the caller, run on the supplier's bank. -/
def extendPrivate {states : ℕ} (M : Program t states prime) :=
  recastProgram (count_def t).symm rfl
    (Supplier.extendOuter (High.extendBanks capacity (extend (extend (extend M 2) 16) 19)))

theorem private_hoare {states budget : ℕ} {M : Program t states prime} {v w : Tapes t prime}
    (h : HoareTime M (fun z => z = v) (fun z => z = w) budget) :
    HoareTime (extendPrivate M) (fun z => z = input v) (fun z => z = input w) budget :=
  hoare_recast (count_def t).symm rfl (Supplier.extend_outer (High.extend_banks_hoare capacity
    (hoare_extend_eq (hoare_extend_eq (hoare_extend_eq h Supplier.guard) (FixedHeaderBankCopy.empty 16))
    MetaShared.privateInput)))

omit [Capacity] in
theorem empty_blank {n a : ℕ} (j : Fin n) :
    (SharedBank.empty n a).head j = 0 ∧ (SharedBank.empty n a).tape j = fun _ => blank := ⟨rfl, rfl⟩

omit [Capacity] in
/-- Stage 1's branch banks pad. -/
theorem branch_pad {s : ℕ} : Padded (M8.Machine.ArbitraryWidthHighBranchPrepare.input (t := s) (a := prime))
    (fun j => Fin.castAdd 1 (Fin.castAdd 12 (Fin.castAdd 17 j))) :=
  ((Padded.append (FixedHeaderBankCopy.empty 17) empty_blank).comp
    (Padded.append (FixedHeaderBankCopy.empty 12) empty_blank)).comp
    (Padded.append ArbitraryWidthZeroHeaderShared.empty (fun _ => ⟨rfl, rfl⟩))

omit [Capacity] in
/-- Stage 1's private banks pad. -/
theorem outer_pad {s : ℕ} : Padded (Supplier.outer (t := s)) Supplier.outerSlot :=
  ((((Padded.append (FixedHeaderBankCopy.empty 16) empty_blank).comp
    (Padded.append M8.Machine.ArbitraryWidthHighPrepareShared.privateInput empty_blank)).comp branch_pad).comp
    (((Padded.append (SharedBank.empty exchangeCount prime) empty_blank).comp
      (Padded.append (SharedBank.empty movementCount prime) empty_blank)).comp
      (Padded.append (SharedBank.empty M8.Machine.ArbitraryWidthHighRun.paddingCount prime) empty_blank))).comp
    (Padded.append (FixedHeaderBankCopy.empty elementaryCount) empty_blank)

/-- The high path's private banks pad. -/
theorem high_pad {s : ℕ} : Padded (High.input capacity (t := s)) (Supplier.innerSlot capacity) :=
  ((((Padded.append (FixedHeaderBankCopy.empty 16) empty_blank).comp
    (Padded.append MetaShared.privateInput empty_blank)).comp branch_pad).comp
    (Padded.append (Width.privateIn (q := prime)) (fun _ => ⟨rfl, rfl⟩))).comp
    (((Padded.append (SharedBank.empty exchangeCount prime) empty_blank).comp
      (Padded.append (SharedBank.empty movementCount prime) empty_blank)).comp
      (Padded.append (SharedBank.empty (HighBody.padCount capacity) prime) empty_blank))

/-- **The supplier's banks pad its caller.** -/
theorem input_pad : Padded (input (t := t)) slot :=
  (((Padded.append Supplier.guard empty_blank).comp high_pad).comp outer_pad).recast (count_def t).symm

end
end IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Total
