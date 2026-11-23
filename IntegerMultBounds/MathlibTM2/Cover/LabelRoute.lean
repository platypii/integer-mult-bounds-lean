module

public import IntegerMultBounds.MathlibTM2.Cover.LabelBits
public import IntegerMultBounds.MathlibTM2.Cover.LabelWidth

/-! Column permutations between triangular passes on the atom-width descriptor bank. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Cover.LabelRoute
noncomputable section

open IntegerMultBounds.Machine IntegerMultBounds.Networks
open IntegerMultBounds.MathlibTM2.M8.RevMachine
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open M8.Stage2Machine.Straight (words)
open M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord)
open LabelWidth (program widen narrow cost)
open LabelSchedule (base Pair)
open LabelCall (bank)
open SharedPlacementAlphabet (setTape)
variable {T m : ℕ} [M8.Machine.Net]

def rowPivot (k : ℕ) (io : Fin T) (ps : List (Pair m)) :=
  Blocks.seqB (Blocks.seqB (LabelSwap.onHeaders (p := 0) (program k widen))
    (LabelSchedule.schedule io ps)) (LabelSwap.onHeaders (p := 0) (program k narrow))

def listedPivotCost (k : ℕ) (v : Descriptor) (w : ℕ) (ps : List (Pair m)) :=
  cost v w k widen + (LabelSchedule.countCost ps + ps.length *
    (3808274 * volume prime v + LeafCore.coreCost (volume prime v) (w*k))) + 1 +
    cost v (w*k) k narrow + 1

theorem listedPivot_runs (k : ℕ) (π : Equiv.Perm (Fin m)) (io : Fin T) (ps : List (Pair m))
    (order : (ps.map fun p => Equiv.swap p.val.1 p.val.2).prod = π) :
      ∀ (v : Descriptor) (w B : ℕ), 0 < w*k → 0 < B →
        v.beforeH = B*prime^(m*(w*k)) → v.Positive → ∀ (roles : Tapes T prime)
        (x : Fin (volume prime v) → ZMod 2), roles.head io = 0 → roles.tape io = sourceWord x →
        let d := words (base v w)
        ∃ y : Fin (volume prime v) → ZMod 2,
          LabelPermutation.RowMoves v B w k π (ext x) (ext y) ∧
          GraphContract.Runs (rowPivot k io ps) (bank roles v d)
            (bank (setTape roles io (sourceWord y) 0) v d) (listedPivotCost k v w ps) := by
  intro v w B hw hb hv hp roles x hh hx
  obtain ⟨y,swaps,h⟩ := LabelSchedule.schedule_runs ps hw hb hv hp roles io x hh hx
  have hy := LabelPermutation.swaps_move_rows hv ps swaps
  rw [order] at hy
  have hm : 0 < k := Nat.pos_of_mul_pos_left hw
  have h₁ := LabelSwap.onHeaders_runs (p := 0) roles v
    (d := words (base v w)) (e := words (base v (w*k)))
    (by simpa only [LabelSwap.append_zero] using LabelWidth.widen_runs v w k hm)
  have h₂ := LabelSwap.onHeaders_runs (p := 0) (setTape roles io (sourceWord y) 0) v
    (d := words (base v (w*k))) (e := words (base v w))
    (by simpa only [LabelSwap.append_zero] using LabelWidth.narrow_runs v w k hm)
  exact ⟨y, hy, Blocks.seq_runs (Blocks.seq_leading _ _) (LabelSwap.headers_leading _)
    (Blocks.seq_runs (LabelSwap.headers_leading _) (LabelSchedule.schedule_leading io ps) h₁ h) h₂⟩

def rowPivotCost (k : ℕ) (v : Descriptor) (w : ℕ) (ps : List (Pair m)) :=
  cost v w k widen + (LabelSchedule.countCost ps + (m-1) *
    (3808274 * volume prime v + LeafCore.coreCost (volume prime v) (w*k))) + 1 +
    cost v (w*k) k narrow + 1

theorem rowPivot_runs (k : ℕ) (π : Equiv.Perm (Fin m)) (io : Fin T) :
    ∃ ps : List (Pair m), ps.length ≤ m-1 ∧
      ∀ (v : Descriptor) (w B : ℕ), 0 < w*k → 0 < B →
        v.beforeH = B*prime^(m*(w*k)) → v.Positive → ∀ (roles : Tapes T prime)
        (x : Fin (volume prime v) → ZMod 2), roles.head io = 0 → roles.tape io = sourceWord x →
        let d := words (base v w)
        ∃ y : Fin (volume prime v) → ZMod 2,
          LabelPermutation.RowMoves v B w k π (ext x) (ext y) ∧
          GraphContract.Runs (rowPivot k io ps) (bank roles v d)
            (bank (setTape roles io (sourceWord y) 0) v d) (rowPivotCost k v w ps) := by
  obtain ⟨ps, hn, hr⟩ := LabelPermutation.realizes_rows k π io
  refine ⟨ps, hn, ?_⟩
  intro v w B hw hb hv hp roles x hh hx
  obtain ⟨y, hy, h⟩ := hr v w B hw hb hv hp roles x hh hx
  have hm : 0 < k := Nat.pos_of_mul_pos_left hw
  have h₁ := LabelSwap.onHeaders_runs (p := 0) roles v
    (d := words (base v w)) (e := words (base v (w*k)))
    (by simpa only [LabelSwap.append_zero] using LabelWidth.widen_runs v w k hm)
  have h₂ := LabelSwap.onHeaders_runs (p := 0) (setTape roles io (sourceWord y) 0) v
    (d := words (base v (w*k))) (e := words (base v w))
    (by simpa only [LabelSwap.append_zero] using LabelWidth.narrow_runs v w k hm)
  exact ⟨y, hy, Blocks.seq_runs (Blocks.seq_leading _ _) (LabelSwap.headers_leading _)
    (Blocks.seq_runs (LabelSwap.headers_leading _) (LabelSchedule.schedule_leading io ps) h₁ h) h₂⟩

def pivot (io : Fin T) (ps : List (Pair m)) :=
  Blocks.seqB (Blocks.seqB (LabelSwap.onHeaders (p := 0) (program m widen))
    (LabelSchedule.schedule io ps)) (LabelSwap.onHeaders (p := 0) (program m narrow))

def pivotCost (v : Descriptor) (w : ℕ) (ps : List (Pair m)) :=
  cost v w m widen + (LabelSchedule.countCost ps + (m-1) *
    (3808274 * volume prime v + LeafCore.coreCost (volume prime v) (w*m))) + 1 +
    cost v (w*m) m narrow + 1

theorem pivot_runs (π : Equiv.Perm (Fin m)) (io : Fin T) :
    ∃ ps : List (Pair m), ps.length ≤ m-1 ∧
      ∀ (v : Descriptor) (w B : ℕ), 0 < w*m → 0 < B →
        v.beforeH = B*prime^(m*(w*m)) → v.Positive → ∀ (roles : Tapes T prime)
        (x : Fin (volume prime v) → ZMod 2), roles.head io = 0 → roles.tape io = sourceWord x →
        let d := words (base v w)
        ∃ y : Fin (volume prime v) → ZMod 2,
          LabelPermutation.Moves v B w π (ext x) (ext y) ∧
          GraphContract.Runs (pivot io ps) (bank roles v d)
            (bank (setTape roles io (sourceWord y) 0) v d) (pivotCost v w ps) := rowPivot_runs m π io

open ActualAffineScaling (modulus)
open IntegerMultBounds.Swap.Modular (reduce)
open IntegerMultBounds.Swap.Shear (LowerTriangular pivotMatrix)

/-- Reverse the columns, execute the upper factor in descending index order,
and return to the caller's column order using the same permutation circuit. -/
theorem ordered_rows_runs {k : ℕ} (hkpos : 0 < k) (hk : 2 ≤ m*k) (io : Fin T) (E : Matrix (Fin m) (Fin m) ℚ)
    (π : Equiv.Perm (Fin m)) (inv : Function.Involutive π) (ps : List (Pair m))
    (order : (ps.map fun p => Equiv.swap p.val.1 p.val.2).prod = π)
    (lower : LowerTriangular (E.submatrix π π))
    (hs : ∀ op ∈ LabelAddress.rowPass k (E.submatrix π π), FlatCoordinateSchedule.Supported op) :
    let A := E.submatrix π π
    let ops := LabelProgram.rowPass hk A hs
    ∀ (v : Descriptor) (w B : ℕ),
      0 < w → 0 < B → v.beforeH = B*prime^(m*(w*k)) → v.Positive →
      IsUnit (reduce (modulus w) A) →
      ∀ (roles : Tapes T prime) (x : Fin (volume prime v) → ZMod 2),
      roles.head io = 0 → roles.tape io = sourceWord x →
      let d := words (base v w)
      ∃ y : Fin (volume prime v) → ZMod 2,
        LabelPermutation.RowTransport v B w k (fun g => g * (reduce (modulus w) E).transpose) (ext x) (ext y) ∧
        GraphContract.Runs (Blocks.seqB (Blocks.seqB (rowPivot k io ps) (LabelProgram.program io ops)) (rowPivot k io ps))
          (bank roles v d) (bank (setTape roles io (sourceWord y) 0) v d)
          (listedPivotCost k v w ps + LabelProgram.coefficient ops * volume prime v + 1 + listedPivotCost k v w ps + 1) := by
  intro A ops
  intro v w B hw hb shape pos unit roles x head tape d
  have run := listedPivot_runs k π io ps order v w B (Nat.mul_pos hw hkpos) hb shape pos
  obtain ⟨y,xy,r₁⟩ := run roles x head tape
  obtain ⟨z,r₂,yz⟩ := LabelBits.rowPass_runs hk A hs lower unit shape hw hb pos io
    (setTape roles io (sourceWord y) 0) y (by simp [setTape]) (by simp [setTape])
  obtain ⟨out,zo,r₃⟩ := run (setTape roles io (sourceWord z) 0) z (by simp [setTape]) (by simp [setTape])
  simp only [SharedPlacementAlphabet.setTape_setTape] at r₂ r₃
  refine ⟨out,?_,Blocks.seq_runs (Blocks.seq_leading _ _) (Blocks.seq_leading _ _)
    (Blocks.seq_runs (Blocks.seq_leading _ _) (LabelProgram.leading _ _) r₁ r₂) r₃⟩
  intro g a ha row hr b hB h hh mid hm d hd after he
  let R := Matrix (Fin k) (Fin m) (ZMod (modulus w))
  change Matrix (Fin k) (Fin m) (ZMod (modulus w)) at g
  let rev : R → R := fun g i j => g i (π j)
  have undo : rev ((rev g : Matrix (Fin k) (Fin m) (ZMod (modulus w))) * (reduce (modulus w) A).transpose) = g * (reduce (modulus w) E).transpose := by
    funext i j
    change (∑ k : Fin m, g i (π k) * (reduce (modulus w) E) (π (π j)) (π k)) = _
    rw [inv j]
    exact Equiv.sum_comp π (fun k => g i k * (reduce (modulus w) E) j k)
  have back := zo ((rev g : Matrix (Fin k) (Fin m) (ZMod (modulus w))) * (reduce (modulus w) A).transpose) a ha row hr b hB h hh mid hm d hd after he
  let : NeZero (prime^w) := ⟨pow_ne_zero _ Shared50ModularControl.prime_prime.ne_zero⟩
  let read := fun label : R => ext out (RecursiveInterchangeLayout.index prime v a row
    (b*prime^(m*(w*k))+(LabelColumns.rowAddress (Q := prime^w) label).val) h mid d after)
  apply (congrArg read undo.symm).trans
  exact back.trans ((yz (rev g) a ha row hr b hB h hh mid hm d hd after he).trans
    (xy g a ha row hr b hB h hh mid hm d hd after he))

theorem upper_rows_runs {k : ℕ} (hkpos : 0 < k) (hk : 2 ≤ m*k) (io : Fin T) (E : Matrix (Fin m) (Fin m) ℚ)
    (upper : ∀ i j, j < i → E i j = 0)
    (hs : ∀ op ∈ LabelAddress.rowPass k (E.submatrix Fin.rev Fin.rev), FlatCoordinateSchedule.Supported op) :
    let A := E.submatrix Fin.rev Fin.rev
    let ops := LabelProgram.rowPass hk A hs
    ∃ ps : List (Pair m), ps.length ≤ m-1 ∧ ∀ (v : Descriptor) (w B : ℕ),
      0 < w → 0 < B → v.beforeH = B*prime^(m*(w*k)) → v.Positive →
      IsUnit (reduce (modulus w) A) →
      ∀ (roles : Tapes T prime) (x : Fin (volume prime v) → ZMod 2),
      roles.head io = 0 → roles.tape io = sourceWord x →
      let d := words (base v w)
      ∃ y : Fin (volume prime v) → ZMod 2,
        LabelPermutation.RowTransport v B w k (fun g => g * (reduce (modulus w) E).transpose) (ext x) (ext y) ∧
        GraphContract.Runs (Blocks.seqB (Blocks.seqB (rowPivot k io ps) (LabelProgram.program io ops)) (rowPivot k io ps))
          (bank roles v d) (bank (setTape roles io (sourceWord y) 0) v d)
          (rowPivotCost k v w ps + LabelProgram.coefficient ops * volume prime v + 1 + rowPivotCost k v w ps + 1) := by
  intro A ops
  obtain ⟨ps,len,reverse⟩ := rowPivot_runs (m := m) k Fin.revPerm io
  refine ⟨ps,len,?_⟩
  intro v w B hw hb shape pos unit roles x head tape d
  have run := reverse v w B (Nat.mul_pos hw hkpos) hb shape pos
  have lower : LowerTriangular A := fun i j lt => upper _ _ (Fin.rev_lt_rev.mpr lt)
  obtain ⟨y,xy,r₁⟩ := run roles x head tape
  obtain ⟨z,r₂,yz⟩ := LabelBits.rowPass_runs hk A hs lower unit shape hw hb pos io
    (setTape roles io (sourceWord y) 0) y (by simp [setTape]) (by simp [setTape])
  obtain ⟨out,zo,r₃⟩ := run (setTape roles io (sourceWord z) 0) z (by simp [setTape]) (by simp [setTape])
  simp only [SharedPlacementAlphabet.setTape_setTape] at r₂ r₃
  refine ⟨out,?_,Blocks.seq_runs (Blocks.seq_leading _ _) (Blocks.seq_leading _ _)
    (Blocks.seq_runs (Blocks.seq_leading _ _) (LabelProgram.leading _ _) r₁ r₂) r₃⟩
  intro g a ha row hr b hB h hh mid hm d hd after he
  let R := Matrix (Fin k) (Fin m) (ZMod (modulus w))
  change Matrix (Fin k) (Fin m) (ZMod (modulus w)) at g
  let rev : R → R := fun g i j => g i (Fin.rev j)
  have order : rev ((rev g : Matrix (Fin k) (Fin m) (ZMod (modulus w))) * (reduce (modulus w) A).transpose) = g * (reduce (modulus w) E).transpose := by
    funext i j
    change (∑ k : Fin m, g i k.rev * (reduce (modulus w) E) j.rev.rev k.rev) = _
    rw [Fin.rev_rev]
    exact Equiv.sum_comp Fin.revPerm (fun k => g i k * (reduce (modulus w) E) j k)
  have back := zo ((rev g : Matrix (Fin k) (Fin m) (ZMod (modulus w))) * (reduce (modulus w) A).transpose) a ha row hr b hB h hh mid hm d hd after he
  let : NeZero (prime^w) := ⟨pow_ne_zero _ Shared50ModularControl.prime_prime.ne_zero⟩
  let read := fun label : R => ext out (RecursiveInterchangeLayout.index prime v a row
    (b*prime^(m*(w*k))+(LabelColumns.rowAddress (Q := prime^w) label).val) h mid d after)
  apply (congrArg read order.symm).trans
  exact back.trans ((yz (rev g) a ha row hr b hB h hh mid hm d hd after he).trans
    (xy g a ha row hr b hB h hh mid hm d hd after he))

theorem upper_runs (hk : 2 ≤ m*m) (io : Fin T) (E : Matrix (Fin m) (Fin m) ℚ)
    (upper : ∀ i j, j < i → E i j = 0)
    (hs : ∀ op ∈ LabelAddress.pass (E.submatrix Fin.rev Fin.rev), FlatCoordinateSchedule.Supported op) :
    let A := E.submatrix Fin.rev Fin.rev
    let ops := LabelProgram.pass hk A hs
    ∃ ps : List (Pair m), ps.length ≤ m-1 ∧ ∀ (v : Descriptor) (w B : ℕ),
      0 < w → 0 < B → v.beforeH = B*prime^(m*(w*m)) → v.Positive →
      IsUnit (reduce (modulus w) A) →
      ∀ (roles : Tapes T prime) (x : Fin (volume prime v) → ZMod 2),
      roles.head io = 0 → roles.tape io = sourceWord x →
      let d := words (base v w)
      ∃ y : Fin (volume prime v) → ZMod 2,
        LabelPermutation.Transport v B w (fun g => g * (reduce (modulus w) E).transpose) (ext x) (ext y) ∧
        GraphContract.Runs (Blocks.seqB (Blocks.seqB (pivot io ps) (LabelProgram.program io ops)) (pivot io ps))
          (bank roles v d) (bank (setTape roles io (sourceWord y) 0) v d)
          (pivotCost v w ps + LabelProgram.coefficient ops * volume prime v + 1 + pivotCost v w ps + 1) :=
  upper_rows_runs (by by_contra! h; interval_cases m; contradiction) hk io E upper hs

/-- A fixed right-multiplication circuit for a supported triangular–permutation factorization. -/
theorem realizes_rows {k : ℕ} (hkpos : 0 < k) (hk : 2 ≤ m*k) (io : Fin T) (π : Equiv.Perm (Fin m))
    (E₁ E₂ : Matrix (Fin m) (Fin m) ℚ)
    (hs₁ : ∀ op ∈ LabelAddress.rowPass k E₁, FlatCoordinateSchedule.Supported op)
    (hs₂ : ∀ op ∈ LabelAddress.rowPass k E₂, FlatCoordinateSchedule.Supported op)
    (ht₁ : LowerTriangular E₁) (ht₂ : LowerTriangular E₂) :
    let a := LabelProgram.rowPass hk E₂ hs₂
    let b := LabelProgram.rowPass hk E₁ hs₁
    ∃ ps : List (Pair m), ps.length ≤ m-1 ∧
      ∀ (v : Descriptor) (w B : ℕ), 0 < w → 0 < B →
        v.beforeH = B*prime^(m*(w*k)) → v.Positive →
        IsUnit (reduce (modulus w) E₁) → IsUnit (reduce (modulus w) E₂) →
        ∀ (σ : Matrix (Fin m) (Fin m) (ZMod (modulus w))) (L : List (Fin m × Fin m)),
        L.Nodup → (∀ j k, (j,k) ∈ L ↔ k = π j) →
        σ.transpose = reduce (modulus w) E₁ * pivotMatrix L * reduce (modulus w) E₂ →
        ∀ (roles : Tapes T prime) (x : Fin (volume prime v) → ZMod 2),
        roles.head io = 0 → roles.tape io = sourceWord x →
        let d := words (base v w)
        ∃ y : Fin (volume prime v) → ZMod 2,
          LabelPermutation.RowTransport v B w k (fun g => g * σ) (ext x) (ext y) ∧
          GraphContract.Runs (Blocks.seqB (Blocks.seqB (LabelProgram.program io a) (rowPivot k io ps))
            (LabelProgram.program io b)) (bank roles v d) (bank (setTape roles io (sourceWord y) 0) v d)
            (LabelProgram.coefficient a * volume prime v + rowPivotCost k v w ps + 1 +
              LabelProgram.coefficient b * volume prime v + 1) := by
  obtain ⟨ps, hn, hperm⟩ := rowPivot_runs k π io
  refine ⟨ps, hn, ?_⟩
  intro v w B hw hb hv hp hu₁ hu₂ σ L hL hπ hσ roles x hh hx
  obtain ⟨y, hr₂, hy⟩ := LabelBits.rowPass_runs hk E₂ hs₂ ht₂ hu₂ hv hw hb hp io roles x hh hx
  obtain ⟨z, hz, hrp⟩ := hperm v w B (Nat.mul_pos hw hkpos) hb hv hp
    (setTape roles io (sourceWord y) 0) y (by simp [setTape]) (by simp [setTape])
  obtain ⟨out, hr₁, hout⟩ := LabelBits.rowPass_runs hk E₁ hs₁ ht₁ hu₁ hv hw hb hp io
    (setTape roles io (sourceWord z) 0) z (by simp [setTape]) (by simp [setTape])
  simp only [SharedPlacementAlphabet.setTape_setTape] at hrp hr₁
  exact ⟨out, LabelTransport.route_rows hL π hπ hσ hy hz hout,
    Blocks.seq_runs (Blocks.seq_leading _ _) (LabelProgram.leading _ _)
      (Blocks.seq_runs (LabelProgram.leading _ _) (Blocks.seq_leading _ _) hr₂ hrp) hr₁⟩

theorem realizes (hk : 2 ≤ m*m) (io : Fin T) (π : Equiv.Perm (Fin m))
    (E₁ E₂ : Matrix (Fin m) (Fin m) ℚ)
    (hs₁ : ∀ op ∈ LabelAddress.pass E₁, FlatCoordinateSchedule.Supported op)
    (hs₂ : ∀ op ∈ LabelAddress.pass E₂, FlatCoordinateSchedule.Supported op)
    (ht₁ : LowerTriangular E₁) (ht₂ : LowerTriangular E₂) :
    let a := LabelProgram.pass hk E₂ hs₂
    let b := LabelProgram.pass hk E₁ hs₁
    ∃ ps : List (Pair m), ps.length ≤ m-1 ∧
      ∀ (v : Descriptor) (w B : ℕ), 0 < w → 0 < B →
        v.beforeH = B*prime^(m*(w*m)) → v.Positive →
        IsUnit (reduce (modulus w) E₁) → IsUnit (reduce (modulus w) E₂) →
        ∀ (σ : Matrix (Fin m) (Fin m) (ZMod (modulus w))) (L : List (Fin m × Fin m)),
        L.Nodup → (∀ j k, (j,k) ∈ L ↔ k = π j) →
        σ.transpose = reduce (modulus w) E₁ * pivotMatrix L * reduce (modulus w) E₂ →
        ∀ (roles : Tapes T prime) (x : Fin (volume prime v) → ZMod 2),
        roles.head io = 0 → roles.tape io = sourceWord x →
        let d := words (base v w)
        ∃ y : Fin (volume prime v) → ZMod 2,
          LabelPermutation.Transport v B w (fun g => g * σ) (ext x) (ext y) ∧
          GraphContract.Runs (Blocks.seqB (Blocks.seqB (LabelProgram.program io a) (pivot io ps))
            (LabelProgram.program io b)) (bank roles v d) (bank (setTape roles io (sourceWord y) 0) v d)
            (LabelProgram.coefficient a * volume prime v + pivotCost v w ps + 1 +
              LabelProgram.coefficient b * volume prime v + 1) :=
  realizes_rows (by by_contra! h; interval_cases m; contradiction) hk io π E₁ E₂ hs₁ hs₂ ht₁ ht₂

end
end IntegerMultBounds.MathlibTM2.Cover.LabelRoute
