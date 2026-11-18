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
            (bank (setTape roles io (sourceWord y) 0) v d) (pivotCost v w ps) := by
  obtain ⟨ps, hn, hr⟩ := LabelPermutation.realizes π io
  refine ⟨ps, hn, ?_⟩
  intro v w B hw hb hv hp roles x hh hx
  obtain ⟨y, hy, h⟩ := hr v w B hw hb hv hp roles x hh hx
  have hm : 0 < m := Nat.pos_of_mul_pos_left hw
  have h₁ := LabelSwap.onHeaders_runs (p := 0) roles v
    (d := words (base v w)) (e := words (base v (w*m)))
    (by simpa only [LabelSwap.append_zero] using LabelWidth.widen_runs v w m hm)
  have h₂ := LabelSwap.onHeaders_runs (p := 0) (setTape roles io (sourceWord y) 0) v
    (d := words (base v (w*m))) (e := words (base v w))
    (by simpa only [LabelSwap.append_zero] using LabelWidth.narrow_runs v w m hm)
  exact ⟨y, hy, Blocks.seq_runs (Blocks.seq_leading _ _) (LabelSwap.headers_leading _)
    (Blocks.seq_runs (LabelSwap.headers_leading _) (LabelSchedule.schedule_leading io ps) h₁ h) h₂⟩

open ActualAffineScaling (modulus)
open IntegerMultBounds.Swap.Modular (reduce)
open IntegerMultBounds.Swap.Shear (LowerTriangular pivotMatrix)

/-- A fixed right-multiplication circuit for a supported triangular–permutation factorization. -/
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
              LabelProgram.coefficient b * volume prime v + 1) := by
  obtain ⟨ps, hn, hperm⟩ := pivot_runs π io
  refine ⟨ps, hn, ?_⟩
  intro v w B hw hb hv hp hu₁ hu₂ σ L hL hπ hσ roles x hh hx
  obtain ⟨y, hr₂, hy⟩ := LabelBits.pass_runs hk E₂ hs₂ ht₂ hu₂ hv hw hb hp io roles x hh hx
  have hm : 0 < m := by by_contra! h; interval_cases m; contradiction
  obtain ⟨z, hz, hrp⟩ := hperm v w B (Nat.mul_pos hw hm) hb hv hp
    (setTape roles io (sourceWord y) 0) y (by simp [setTape]) (by simp [setTape])
  obtain ⟨out, hr₁, hout⟩ := LabelBits.pass_runs hk E₁ hs₁ ht₁ hu₁ hv hw hb hp io
    (setTape roles io (sourceWord z) 0) z (by simp [setTape]) (by simp [setTape])
  simp only [SharedPlacementAlphabet.setTape_setTape] at hrp hr₁
  exact ⟨out, LabelTransport.route hL π hπ hσ hy hz hout,
    Blocks.seq_runs (Blocks.seq_leading _ _) (LabelProgram.leading _ _)
      (Blocks.seq_runs (LabelProgram.leading _ _) (Blocks.seq_leading _ _) hr₂ hrp) hr₁⟩

end
end IntegerMultBounds.MathlibTM2.Cover.LabelRoute
