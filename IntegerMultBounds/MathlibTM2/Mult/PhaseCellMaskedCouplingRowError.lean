module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOffsetCouplingRow
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingInputAccuracy

/-! Accuracy of the actual masked input and selected coefficient row. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem couplingInputWords_norm {s q inputExp : ℕ} [NeZero s] (boundary : Bool)
    (t band a b i : ℕ) (C : ZMod s → GaussianInt)
    (hC : ∀ j ∈ (if boundary then haloBoundary s t band a b else haloInterior s t band a b),
      ‖value q (C j)‖ ≤ (2 : ℝ)^inputExp) :
    ∀ z ∈ couplingInputWords boundary t band a b i C, ‖value q z‖ ≤ (2 : ℝ)^inputExp := by
  intro z hz
  obtain ⟨δ,_,rfl⟩ := List.mem_map.mp hz
  let T := if boundary then haloBoundary s t band a b else haloInterior s t band a b
  let j : ZMod s := (i : ZMod s)+(δ : ZMod s)
  change ‖value q (if j ∈ T then C j else 0)‖ ≤ (2 : ℝ)^inputExp
  by_cases h : j ∈ T
  · simpa only [if_pos h] using hC j h
  · simp only [if_neg h]
    have hz : value q (0 : GaussianInt) = 0 := by apply Complex.ext <;> simp [value]
    rw [hz,norm_zero]
    positivity

theorem maskedCouplingRow_error {A s t p u q w rhsExp inputExp countExp a b i : ℕ}
    [NeZero s] {α d : ℝ} (boundary : Bool) (hA : 96 ≤ A)
    (hp : 0 < p) (hst : s < t) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hw : q+couplingRowExponent rhsExp inputExp (8*p+1) countExp+2 ≤ w)
    (hi : i < s) (C : ZMod s → GaussianInt) (x : ZMod s → ℝ) (rhs : GaussianInt)
    (b₀ K ε rhsError : ℝ) (hε : 0 ≤ ε)
    (hcount : 2*PhaseCellBand.width p u+1 ≤ 2^countExp)
    (hrhs : ‖value q rhs‖ ≤ (2 : ℝ)^rhsExp)
    (hC : ∀ j ∈ (if boundary then haloBoundary s t (PhaseCellBand.width p u) a b
        else haloInterior s t (PhaseCellBand.width p u) a b), ‖value q (C j)‖ ≤ (2 : ℝ)^inputExp)
    (hx : ∀ j ∈ (if boundary then haloBoundary s t (PhaseCellBand.width p u) a b
        else haloInterior s t (PhaseCellBand.width p u) a b), |(value q (C j)).re-x j| ≤ ε)
    (hmass : (((couplingOffsets (PhaseCellBand.width p u)).reverse).map (fun δ =>
      |(PhaseCellCrossCell.entry (2^15*p) s t u (PhaseCellBand.width p u) i (i+δ) : ℝ)|)).sum ≤ K)
    (hrhsError : |(value q rhs).re-b₀| ≤ rhsError) (tail : List (Fin (A+4))) :
    let band := PhaseCellBand.width p u
    let T := if boundary then haloBoundary s t band a b else haloInterior s t band a b
    let z := rhs-(List.zipWith (fun x c => tdivN q (x*c))
      (couplingInputWords boundary t band a b i C) (couplingCoefficientWords (2^15*p) q s t u band i)).sum
    |(value q (decodeWord ((csyms A w z++tail).take w))).re-
      (b₀-SchurDominance.couple (realMatrix s t p u) T x (i : ZMod s))| ≤
        (2*band+1)*(2/(2 : ℝ)^q)+rhsError+(2*band+1)*((2 : ℝ)^inputExp*(1/(2 : ℝ)^q))+K*ε := by
  dsimp only
  let band := PhaseCellBand.width p u
  let T := if boundary then haloBoundary s t band a b else haloInterior s t band a b
  let entries := (couplingOffsets band).reverse
  let input := fun δ : ℤ => if (i : ZMod s)+(δ : ZMod s) ∈ T then C ((i : ZMod s)+(δ : ZMod s)) else 0
  let coeff := fun δ : ℤ => rationalWord q (PhaseCellCrossCell.entry (2^15*p) s t u band i (i+δ))
  let a₀ := fun δ : ℤ => (PhaseCellCrossCell.entry (2^15*p) s t u band i (i+δ) : ℝ)
  let y := fun δ : ℤ => if (i : ZMod s)+(δ : ZMod s) ∈ T then x ((i : ZMod s)+(δ : ZMod s)) else 0
  let xs := couplingInputWords boundary t band a b i C
  let as := couplingCoefficientWords (2^15*p) q s t u band i
  let z := rhs-(List.zipWith (fun x c => tdivN q (x*c)) xs as).sum
  have hxs : ∀ z ∈ xs, ‖value q z‖ ≤ (2 : ℝ)^inputExp := couplingInputWords_norm boundary t band a b i C hC
  have has := couplingCoefficientWords_bounds (q := q) (band := band) (i := i)
    hp (NeZero.pos s) hst hαu hθ hgap hbudget
  have hfit : Fits w z := fixedPointRow_fits hw rhs xs as (by simp [xs,as])
    (by simpa [xs] using hcount) hrhs hxs (fun c hc => (has c hc).1)
  have hword : (csyms A w z++tail).take w = csyms A w z := by
    have hlen : (csyms A w z).length = w := by simp
    simp only [List.take_append,hlen,Nat.sub_self,List.take_zero,List.append_nil]
    simpa only [hlen] using (show (csyms A w z).take (csyms A w z).length = csyms A w z from List.take_length)
  rw [show rhs-(List.zipWith (fun x c => tdivN q (x*c))
      (couplingInputWords boundary t band a b i C) (couplingCoefficientWords (2^15*p) q s t u band i)).sum = z from rfl,
    hword,decodeWord_of_fits (by omega) (by dsimp [couplingRowExponent] at hw; omega) z hfit]
  have hrow := fixedPointRow_error q rhs xs as (by simp [xs,as]) (fun c hc => (has c hc).2)
  have hxsEq : xs = entries.map input := rfl
  have hasEq : as = entries.map coeff := rfl
  rw [hxsEq,hasEq,supportRow_zipWith] at hrow
  have hz : z = rhs-(entries.map (fun δ => tdivN q (input δ*coeff δ))).sum := by
    dsimp only [z]
    rw [hxsEq,hasEq,supportRow_zipWith]
  have hrow' : |(value q z).re-((value q rhs).re-
      (entries.map (fun δ => (value q (input δ)).re*(value q (coeff δ)).re)).sum)| ≤
      entries.length*(2/(2 : ℝ)^q) := by
    simpa only [hz,supportRow_zipWith,List.length_map] using hrow
  have hcouple : (entries.map (fun δ => y δ*a₀ δ)).sum =
      SchurDominance.couple (realMatrix s t p u) T x (i : ZMod s) := by
    have hh := (couple_eq_offsetList (t := t) p u T x (i : ZMod s)).symm
    simpa only [entries,band,a₀,y,List.map_reverse,List.sum_reverse,ite_mul,mul_ite,zero_mul,mul_zero,mul_comm,
      ZMod.val_natCast_of_lt hi] using hh
  have herror := coupling_residual_perturb entries a₀ (fun δ => (value q (coeff δ)).re)
    (fun δ => (value q (input δ)).re) y (value q rhs).re b₀ (value q z).re ((2 : ℝ)^inputExp)
    (1/(2 : ℝ)^q) ε K (entries.length*(2/(2 : ℝ)^q)) rhsError (by positivity) hε
    (by intro δ hδ
        apply (Complex.abs_re_le_norm _).trans
        apply hxs
        rw [hxsEq]
        exact List.mem_map.mpr ⟨δ,hδ,rfl⟩)
    (by intro δ _; exact rationalWord_error q _)
    (by intro δ _
        dsimp only [input,y]
        split_ifs with h
        · exact hx _ h
        · simpa [value] using hε)
    hmass hrow' hrhsError
  simpa only [hcouple,entries,band,List.length_reverse,couplingOffsets_length,
    Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using herror

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
