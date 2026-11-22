module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackFormulaInputs
public import IntegerMultBounds.Machine.FlatCoordinateLayout

/-! Pack binary coordinate values into a binary rank with the modular formula evaluator. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine Cover.Fallback RingFormula

/-- Evaluate the place-value expansion, starting from its least significant digit. -/
def binaryRankFormula {ι : Type} (radix : RingFormula ι) (digits : List (RingFormula ι)) : RingFormula ι :=
  digits.foldr (fun x y => .sub x (.sub .zero (.mul radix y))) .zero

private theorem binaryRankFormula_eval {ι R : Type} [CommRing R] (read : ι → R) (radix : RingFormula ι)
    {d : ℕ} (digits : Fin d → RingFormula ι) :
    eval read (binaryRankFormula radix (List.ofFn digits)) =
      ∑ i, eval read (digits i)*(eval read radix)^i.val := by
  induction d with
  | zero => simp [binaryRankFormula,eval]
  | succ d ih =>
    rw [List.ofFn_succ,Fin.sum_univ_succ]
    change eval read (digits 0) - (0 - eval read radix *
      eval read (binaryRankFormula radix (List.ofFn (fun i => digits i.succ)))) = _
    rw [ih,Finset.mul_sum]
    simp [pow_succ,mul_assoc,mul_comm]

/-- The radix is a single input. Each remaining leaf requests one
coordinate in the exact order of the physical rank. -/
def sweepBinaryRankCode : RingFormula (Option (Fin 128)) :=
  binaryRankFormula (.input none) (List.ofFn fun i : Fin 128 => .input (some i.rev))

def rankInput {M : ℕ} (x : Fin 128 → ZMod M) : Option (Fin 128) → ZMod (M^128)
  | none => M
  | some i => (x i).val

theorem sweepBinaryRankCode_eval (M : ℕ) [NeZero M] [NeZero (M^128)] (x : Fin 128 → ZMod M) :
    (eval (rankInput x) sweepBinaryRankCode).val = (FlatCoordinateLayout.rank x).val := by
  have number : eval (rankInput x) sweepBinaryRankCode =
      ((FlatCoordinateLayout.rank x).val : ZMod (M^128)) := by
    simp only [sweepBinaryRankCode,binaryRankFormula_eval,eval,rankInput,
      FlatCoordinateLayout.rank,finFunctionFinEquiv_apply,FlatCoordinateLayout.finEquiv_symm_val,
      Nat.cast_sum,Nat.cast_mul,Nat.cast_pow]
  rw [number,ZMod.val_natCast,Nat.mod_eq_of_lt (FlatCoordinateLayout.rank x).isLt]

open Host Node Cover.LabelTraversal in
/-- The rank program calls coordinate writers directly. Both modular
evaluations use the same binary width, so no digit conversion is needed. -/
theorem sweepBinaryRank_writes {T Q A : ℕ} {P U : Type} (body : P → Pr P T Q A U)
    (M H : ℕ) [NeZero M] [NeZero (M^128)] (fits : M^128 < 2^H)
    (x : Fin 128 → ZMod M) (bank : ℕ → Fin T → Fin 13 ↪ Fin T)
    (leaf : Leaf (Option (Fin 128)) → Fin T → Pr P T Q A U)
    (ready : Leaf (Option (Fin 128)) → Fin T → Regs T A → Prop) (cost : Leaf (Option (Fin 128)) → ℕ)
    (emit : ∀ a out, Writes body (ready a out) out (leaf a out)
      (binSyms H (a.value (rankInput x)).val) (cost a)) (out : Fin T) :
    Writes body (prepared bank (rankInput x) H ready sweepBinaryRankCode 0 out) out
      (compile leaf bank sweepBinaryRankCode 0 out) (binSyms H (FlatCoordinateLayout.rank x).val)
      (time H cost sweepBinaryRankCode) := by
  rw [← sweepBinaryRankCode_eval M x]
  exact compile_writes bank _ H ready body fits leaf cost emit sweepBinaryRankCode 0 out

open Host Node Cover.LabelTraversal

/-- Dispatch a coordinate request to its port evaluator. The radix and the
two ring constants are copied from fixed-width binary words. -/
def rankLeafProgram {P U : Type} {T Q A : ℕ}
    (coord : Fin 128 → Fin T → Pr P T Q A U)
    (regs : Leaf (Option (Fin 128)) → Fin T → Fin 4 ↪ Fin T)
    (a : Leaf (Option (Fin 128))) (out : Fin T) : Pr P T Q A U :=
  match a with
  | .input (some i) => coord i out
  | _ => let r := regs a out; bcopy (r 0) (r 1) (r 2) (r 3)

def rankLeafReady {M T A : ℕ} (H : ℕ) (x : Fin 128 → ZMod M)
    (coord : Fin 128 → Fin T → Regs T A → Prop)
    (regs : Leaf (Option (Fin 128)) → Fin T → Fin 4 ↪ Fin T)
    (a : Leaf (Option (Fin 128))) (out : Fin T) (R : Regs T A) : Prop :=
  match a with
  | .input (some i) => coord i out R
  | _ => let r := regs a out
         r 1 = out ∧ R (r 0) = binSyms H (a.value (rankInput x)).val ∧ R (r 2) = [] ∧ R (r 3) = []

def rankLeafCost (H : ℕ) (cost : Fin 128 → ℕ) : Leaf (Option (Fin 128)) → ℕ
  | .input (some i) => cost i
  | _ => 6*H+6

theorem rankFromCoordinates_writes {T Q A M : ℕ} [NeZero M] [NeZero (M^128)] {P U : Type}
    (body : P → Pr P T Q A U) (H : ℕ) (fits : M^128 < 2^H)
    (x : Fin 128 → ZMod M) (bank : ℕ → Fin T → Fin 13 ↪ Fin T)
    (regs : Leaf (Option (Fin 128)) → Fin T → Fin 4 ↪ Fin T)
    (coord : Fin 128 → Fin T → Pr P T Q A U) (ready : Fin 128 → Fin T → Regs T A → Prop)
    (cost : Fin 128 → ℕ) (emit : ∀ i out, Writes body (ready i out) out (coord i out)
      (binSyms H (x i).val) (cost i)) (out : Fin T) :
    Writes body (prepared bank (rankInput x) H (rankLeafReady H x ready regs) sweepBinaryRankCode 0 out) out
      (compile (rankLeafProgram coord regs) bank sweepBinaryRankCode 0 out)
      (binSyms H (FlatCoordinateLayout.rank x).val) (time H (rankLeafCost H cost) sweepBinaryRankCode) := by
  apply sweepBinaryRank_writes body M H fits
  intro a dst
  have copy (r : Fin 4 ↪ Fin T) (y : ℕ) : Writes body (fun R => r 1 = dst ∧ R (r 0) = binSyms H y ∧
      R (r 2) = [] ∧ R (r 3) = []) dst (bcopy (r 0) (r 1) (r 2) (r 3)) (binSyms H y) (6*H+6) := by
    intro v S ⟨hd,src,h₂,h₃⟩
    obtain ⟨z,user,run⟩ := bcopy_exec body (a := r 0) (c := r 1) (t₁ := r 2) (t₂ := r 3)
      (by simp [List.nodup_cons,r.injective.eq_iff]) v S h₂ h₃
    rw [src,length_binSyms,hd] at run
    exact ⟨z,_,user,le_rfl,by simpa only [hd] using run⟩
  cases a with
  | zero | one => exact copy _ _
  | input a =>
    cases a with
    | none => exact copy _ _
    | some i =>
      have lt := (x i).val_lt.trans_le (Nat.le_self_pow (by decide : 128 ≠ 0) M)
      change Writes body (ready i dst) dst (coord i dst) (binSyms H ((rankInput x (some i)).val)) (cost i)
      simpa only [rankLeafReady,rankLeafProgram,rankLeafCost,Leaf.value,rankInput,ZMod.val_natCast,
        Nat.mod_eq_of_lt lt] using emit i dst

end IntegerMultBounds.MathlibTM2.M6.BitNode
