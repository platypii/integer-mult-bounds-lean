module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingPassOutputSpec
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGuardedPackedCouplingRow

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {A : ℕ}

theorem couplingPass_packed_output_error
    {p q w s t u band a b rhsExp inputExp countExp : ℕ} [NeZero s] {α d : ℝ}
    (boundary : Bool) (hA : 96 ≤ A) (hp : 0 < p) (hst : s < t)
    (hαu : α^2 = (u : ℝ)) (hθ : 0 < (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hw : q+couplingRowExponent rhsExp inputExp (8*p+1) countExp+2 ≤ w)
    (hbS : b ≤ s) (hband : band = PhaseCellBand.width p u)
    (C B : ZMod s → GaussianInt) (x b₀ : ZMod s → ℝ) (K ε rhsError : ℝ) (hε : 0 ≤ ε)
    (hcount : 2*band+1 ≤ 2^countExp)
    (hB : ∀ j, ‖value q (B j)‖ ≤ (2 : ℝ)^rhsExp)
    (hC : ∀ j ∈ (if boundary then haloBoundary s t band a b else haloInterior s t band a b),
      ‖value q (C j)‖ ≤ (2 : ℝ)^inputExp)
    (hx : ∀ j ∈ (if boundary then haloBoundary s t band a b else haloInterior s t band a b),
      |(value q (C j)).re-x j| ≤ ε)
    (hmass : ∀ i < s, (((couplingOffsets band).reverse).map (fun δ =>
      |(PhaseCellCrossCell.entry (2^15*p) s t u band i (i+δ) : ℝ)|)).sum ≤ K)
    (hBError : ∀ j, |(value q (B j)).re-b₀ j| ≤ rhsError)
    (origin N : ℕ) (hfit : origin+N ≤ s)
    (suffix : List (Fin (A+4))) :
    let ys := guardedCouplingRowWords (2^15*p) q t u band a b boundary C origin (packedInterval origin N B)
      ∀ j < N, (boundary = true ∨ ((origin+j) : ZMod s) ∈ haloBoundary s t band a b) → |(value q (decodeWord (((cstream A w ys++suffix).drop (j*w)).take w))).re-
        (b₀ ((origin+j) : ZMod s)-SchurDominance.couple (realMatrix s t p u)
          (if boundary then haloBoundary s t band a b else haloInterior s t band a b) x ((origin+j) : ZMod s))| ≤
          (2*band+1)*(2/(2 : ℝ)^q)+rhsError+(2*band+1)*((2 : ℝ)^inputExp*(1/(2 : ℝ)^q))+K*ε := by
  obtain ⟨hys,_,_,herr⟩ := couplingPass_output_spec boundary hA hp hst hαu hθ hgap hbudget hw hbS hband
    C B x b₀ K ε rhsError hε hcount hB hC hx hmass hBError suffix
  rw [hys] at herr
  dsimp only
  rw [guardedCouplingRowWords_packed _ _ _ _ _ _ _ _ _ _ _ _ hfit]
  intro j hj hobserved
  rw [packedInterval_decodeWord w origin N j _ hfit hj suffix suffix]
  simpa only [Nat.cast_add] using herr (origin+j) (by omega) (by simpa only [Nat.cast_add] using hobserved)

theorem couplingPass_packed_reverse_output_error
    {p q w s t u band a b rhsExp inputExp countExp : ℕ} [NeZero s] {α d : ℝ}
    (boundary : Bool) (hA : 96 ≤ A) (hp : 0 < p) (hst : s < t)
    (hαu : α^2 = (u : ℝ)) (hθ : 0 < (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hw : q+couplingRowExponent rhsExp inputExp (8*p+1) countExp+2 ≤ w)
    (hbS : b ≤ s) (hband : band = PhaseCellBand.width p u)
    (C B : ZMod s → GaussianInt) (x b₀ : ZMod s → ℝ) (K ε rhsError : ℝ) (hε : 0 ≤ ε)
    (hcount : 2*band+1 ≤ 2^countExp)
    (hB : ∀ j, ‖value q (B j)‖ ≤ (2 : ℝ)^rhsExp)
    (hC : ∀ j ∈ (if boundary then haloBoundary s t band a b else haloInterior s t band a b),
      ‖value q (C j)‖ ≤ (2 : ℝ)^inputExp)
    (hx : ∀ j ∈ (if boundary then haloBoundary s t band a b else haloInterior s t band a b),
      |(value q (C j)).re-x j| ≤ ε)
    (hmass : ∀ i < s, (((couplingOffsets band).reverse).map (fun δ =>
      |(PhaseCellCrossCell.entry (2^15*p) s t u band i (i+δ) : ℝ)|)).sum ≤ K)
    (hBError : ∀ j, |(value q (B j)).re-b₀ j| ≤ rhsError)
    (origin N : ℕ) (hfit : origin+N ≤ s)
    (suffix : List (Fin (A+4))) :
    let ys := guardedCouplingRowWords (2^15*p) q t u band a b boundary C origin (packedInterval origin N B)
      ∀ j < N, (boundary = true ∨ ((origin+j) : ZMod s) ∈ haloBoundary s t band a b) → |(value q (decodeWord (((cstream A w ys.reverse++suffix).drop ((N-1-j)*w)).take w))).re-
        (b₀ ((origin+j) : ZMod s)-SchurDominance.couple (realMatrix s t p u)
          (if boundary then haloBoundary s t band a b else haloInterior s t band a b) x ((origin+j) : ZMod s))| ≤
          (2*band+1)*(2/(2 : ℝ)^q)+rhsError+(2*band+1)*((2 : ℝ)^inputExp*(1/(2 : ℝ)^q))+K*ε := by
  have herr := couplingPass_packed_output_error boundary hA hp hst hαu hθ hgap hbudget hw hbS hband
    C B x b₀ K ε rhsError hε hcount hB hC hx hmass hBError origin N hfit suffix
  dsimp only at herr ⊢
  intro j hj hobserved
  let ys := guardedCouplingRowWords (2^15*p) q t u band a b boundary C origin (packedInterval origin N B)
  have hlen : ys.length = N := by simp [ys,packedInterval_length B hfit]
  have hd := cstream_reverse_decodeWord w ys j (by rw [hlen]; exact hj) suffix suffix
  rw [hlen] at hd
  rw [hd]
  exact herr j hj hobserved

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
