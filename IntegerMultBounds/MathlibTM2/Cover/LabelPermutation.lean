module

public import IntegerMultBounds.MathlibTM2.Cover.LabelColumns
public import IntegerMultBounds.MathlibTM2.Cover.LabelSchedule

/-! The physical exchange schedule acts on matrix labels by its permutation product. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Cover.LabelPermutation
noncomputable section

open IntegerMultBounds.Machine
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
open RecursiveInterchangeLayout (Descriptor index volume)
open LabelAddress (address)
open LabelColumns (column)
variable {k m w B : ℕ} {v : Descriptor}
local instance : NeZero (prime^w) := ⟨(pow_pos prime_prime.pos _).ne'⟩

/-- Transport on the caller's original addresses, for every payload and spectator prefix. -/
def Transport (v : Descriptor) (B w : ℕ) {m : ℕ}
    (f : Matrix (Fin m) (Fin m) (ZMod (prime^w)) → Matrix (Fin m) (Fin m) (ZMod (prime^w)))
    (x y : ℕ → ZMod 2) :=
  ∀ (g : Matrix (Fin m) (Fin m) (ZMod (prime^w))), ∀ a < v.beforeRows, ∀ row < v.rows,
    ∀ b < B, ∀ h < prime^v.width, ∀ mid < v.between, ∀ d < prime^v.width, ∀ after < v.afterD,
      y (index prime v a row (b*prime^(m*(w*m)) + (address (f g)).val) h mid d after) =
        x (index prime v a row (b*prime^(m*(w*m)) + (address g).val) h mid d after)

abbrev Moves (v : Descriptor) (B w : ℕ) {m : ℕ} (π : Equiv.Perm (Fin m)) :=
  Transport v B w (fun g i j => g i (π j))

private theorem radix (q w m n : ℕ) : ((q^w)^m)^n = q^(n*(w*m)) := by
  rw [← pow_mul, ← pow_mul]; congr 1; ac_rfl

abbrev RowMoves (v : Descriptor) (B w k : ℕ) {m : ℕ} (π : Equiv.Perm (Fin m))
    (x y : ℕ → ZMod 2) :=
  ∀ (g : Matrix (Fin k) (Fin m) (ZMod (prime^w))), ∀ a < v.beforeRows, ∀ row < v.rows,
    ∀ b < B, ∀ h < prime^v.width, ∀ mid < v.between, ∀ d < prime^v.width, ∀ after < v.afterD,
      y (index prime v a row (b*prime^(m*(w*k)) + (LabelColumns.rowAddress (fun i j => g i (π j))).val) h mid d after) =
        x (index prime v a row (b*prime^(m*(w*k)) + (LabelColumns.rowAddress g).val) h mid d after)

private theorem label_radix (q w k m s t lp cs gap ct ls : ℕ) :
    LabelView.label ((q^w)^k) 1 m s t lp cs gap ct ls =
    LabelView.label q (w*k) m s t lp cs gap ct ls := by
  simp only [LabelView.label, Nat.one_mul, pow_one, ← Nat.pow_mul, Nat.mul_comm, Nat.mul_assoc]

theorem swap_moves_rows (p : LabelSchedule.Pair m) (hv : v.beforeH = B*prime^(m*(w*k)))
    {x y : ℕ → ZMod 2} (hs : LabelView.Swapped prime
      (LabelView.colView prime (w*k) m p.val.1 p.val.2 B v) x y) :
    RowMoves v B w k (Equiv.swap p.val.1 p.val.2) x y := by
  intro g a ha row hr b hb h hh mid hm d hd after he
  obtain ⟨lp, gap, ls, h₁, h₂⟩ := LabelColumns.rowAddress_swap g _ _ p.property
  rw [h₁, h₂, label_radix, label_radix]
  have hcs := ZMod.val_lt (LabelColumns.rowColumn g p.val.1)
  have hct := ZMod.val_lt (LabelColumns.rowColumn g p.val.2)
  exact LabelView.swap_cols hv p.property p.val.2.isLt hs ha hr hb
    (by simpa only [radix] using lp.isLt) (lt_of_lt_of_eq hct (Nat.pow_mul ..).symm) (by simpa only [radix] using gap.isLt)
    (lt_of_lt_of_eq hcs (Nat.pow_mul ..).symm) (by simpa only [radix] using ls.isLt) hh hm hd he

theorem swaps_move_rows (hv : v.beforeH = B*prime^(m*(w*k))) (ps : List (LabelSchedule.Pair m))
    {x y : ℕ → ZMod 2} (hs : LabelSchedule.Swaps v (w*k) B ps x y) :
    RowMoves v B w k (ps.map fun p => Equiv.swap p.val.1 p.val.2).prod x y := by
  induction ps generalizing x with
  | nil => subst y; intro; intros; rfl
  | cons p ps ih =>
    obtain ⟨z, h₁, h₂⟩ := hs
    intro g a ha row hr b hb h hh mid hm d hd after he
    exact (ih h₂ (fun i j => g i (Equiv.swap p.val.1 p.val.2 j)) a ha row hr b hb h hh mid hm d hd after he).trans
      (swap_moves_rows p hv h₁ g a ha row hr b hb h hh mid hm d hd after he)

/-- One fixed schedule for the permutation, with the exact matrix action on every payload. -/
theorem realizes_rows (k : ℕ) [M8.Machine.Net] {T : ℕ} (π : Equiv.Perm (Fin m)) (io : Fin T) :
    ∃ ps : List (LabelSchedule.Pair m), ps.length ≤ m-1 ∧
      ∀ (v : Descriptor) (w B : ℕ), 0 < w*k → 0 < B →
        v.beforeH = B*prime^(m*(w*k)) → v.Positive → ∀ (roles : Tapes T prime)
        (x : Fin (volume prime v) → ZMod 2), roles.head io = 0 →
        roles.tape io = M8.Machine.ArbitraryWidthHighExchangeShared.sourceWord x →
        let d := M8.Stage2Machine.Straight.words (LabelSchedule.base v (w*k))
        ∃ y : Fin (volume prime v) → ZMod 2,
          RowMoves v B w k π (M8.RevMachine.ext x) (M8.RevMachine.ext y) ∧
          M8.RevMachine.GraphContract.Runs (LabelSchedule.schedule io ps) (LabelCall.bank roles v d)
            (LabelCall.bank (SharedPlacementAlphabet.setTape roles io
              (M8.Machine.ArbitraryWidthHighExchangeShared.sourceWord y) 0) v d)
            (LabelSchedule.countCost ps + (m-1) *
              (3808274 * volume prime v + M8.RevMachine.LeafCore.coreCost (volume prime v) (w*k))) := by
  obtain ⟨ps, rfl, hn, hr⟩ := LabelSchedule.permutation_schedule π io
  refine ⟨ps, hn, ?_⟩
  intro v w B hw hb hv hp roles x hh hx
  obtain ⟨y, hy, h⟩ := hr v (w*k) B hw hb hv hp roles x hh hx
  exact ⟨y, swaps_move_rows hv ps hy, h⟩


theorem swap_moves (p : LabelSchedule.Pair m) (hv : v.beforeH = B*prime^(m*(w*m)))
    {x y : ℕ → ZMod 2} (hs : LabelView.Swapped prime
      (LabelView.colView prime (w*m) m p.val.1 p.val.2 B v) x y) :
    Moves v B w (Equiv.swap p.val.1 p.val.2) x y := swap_moves_rows p hv hs

theorem swaps_move (hv : v.beforeH = B*prime^(m*(w*m))) (ps : List (LabelSchedule.Pair m))
    {x y : ℕ → ZMod 2} (hs : LabelSchedule.Swaps v (w*m) B ps x y) :
    Moves v B w (ps.map fun p => Equiv.swap p.val.1 p.val.2).prod x y := swaps_move_rows hv ps hs

theorem realizes [M8.Machine.Net] {T : ℕ} (π : Equiv.Perm (Fin m)) (io : Fin T) :
    ∃ ps : List (LabelSchedule.Pair m), ps.length ≤ m-1 ∧
      ∀ (v : Descriptor) (w B : ℕ), 0 < w*m → 0 < B →
        v.beforeH = B*prime^(m*(w*m)) → v.Positive → ∀ (roles : Tapes T prime)
        (x : Fin (volume prime v) → ZMod 2), roles.head io = 0 →
        roles.tape io = M8.Machine.ArbitraryWidthHighExchangeShared.sourceWord x →
        let d := M8.Stage2Machine.Straight.words (LabelSchedule.base v (w*m))
        ∃ y : Fin (volume prime v) → ZMod 2,
          Moves v B w π (M8.RevMachine.ext x) (M8.RevMachine.ext y) ∧
          M8.RevMachine.GraphContract.Runs (LabelSchedule.schedule io ps) (LabelCall.bank roles v d)
            (LabelCall.bank (SharedPlacementAlphabet.setTape roles io
              (M8.Machine.ArbitraryWidthHighExchangeShared.sourceWord y) 0) v d)
            (LabelSchedule.countCost ps + (m-1) *
              (3808274 * volume prime v + M8.RevMachine.LeafCore.coreCost (volume prime v) (w*m))) := realizes_rows m π io


end
end IntegerMultBounds.MathlibTM2.Cover.LabelPermutation
