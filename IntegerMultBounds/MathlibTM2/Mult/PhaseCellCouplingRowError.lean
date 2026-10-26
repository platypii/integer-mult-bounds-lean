module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightStream
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellMergeWord

/-! Fixed-point coupling rows subtract the actual rounded products of their
computed inputs. Arithmetic error is charged by row support, not ambient size. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

theorem supportRow_zipWith {ι α β γ : Type*} (entries : List ι)
    (f : α → β → γ) (x : ι → α) (c : ι → β) :
    List.zipWith f (entries.map x) (entries.map c) = entries.map (fun j => f (x j) (c j)) := by
  induction entries with
  | nil => rfl
  | cons j entries ih => simp only [List.map_cons,List.zipWith_cons_cons,ih]

/-- Each real-weight product spends the output-grid tolerance once. -/
theorem fixedPointRow_sum_error (q : ℕ) (xs as : List GaussianInt)
    (hlen : xs.length = as.length) (has : ∀ a ∈ as, a.im = 0) :
    |(value q (List.zipWith (fun x a => tdivN q (x*a)) xs as).sum).re-
      (List.zipWith (fun x a => (value q x).re*(value q a).re) xs as).sum| ≤
        xs.length*(2/(2 : ℝ)^q) := by
  induction xs generalizing as with
  | nil => simp [value_eq_grid]
  | cons x xs ih =>
    cases as with
    | nil => simp at hlen
    | cons a as =>
      have ht := ih as (by simpa using hlen) (fun a ha => has a (by simp [ha]))
      have hh := normalized_product_real_error q 0 x a (has a (by simp))
      simp only [pow_zero,one_mul,Nat.add_zero] at hh
      have hv (z : GaussianInt) (zs : List GaussianInt) :
          (value q (z+zs.sum)).re = (value q z).re+(value q zs.sum).re := by
        simp [value,add_div]
      simp only [List.zipWith_cons_cons,List.sum_cons,hv]
      calc
        _ = |((value q (tdivN q (x*a))).re-(value q x).re*(value q a).re)+
            ((value q (List.zipWith (fun x a => tdivN q (x*a)) xs as).sum).re-
              (List.zipWith (fun x a => (value q x).re*(value q a).re) xs as).sum)| := by
          congr 1; ring
        _ ≤ _ := abs_add_le _ _
        _ ≤ 2/(2 : ℝ)^q+xs.length*(2/(2 : ℝ)^q) := add_le_add hh ht
        _ = (x::xs).length*(2/(2 : ℝ)^q) := by simp only [List.length_cons,Nat.cast_add,Nat.cast_one]; ring

/-- The subtraction accumulator is exact on numerators; all arithmetic error
comes from the individually rounded products. -/
theorem fixedPointRow_error (q : ℕ) (rhs : GaussianInt) (xs as : List GaussianInt)
    (hlen : xs.length = as.length) (has : ∀ a ∈ as, a.im = 0) :
    |(value q (rhs-(List.zipWith (fun x a => tdivN q (x*a)) xs as).sum)).re-
      ((value q rhs).re-(List.zipWith (fun x a => (value q x).re*(value q a).re) xs as).sum)| ≤
        xs.length*(2/(2 : ℝ)^q) := by
  rw [value_sub,Complex.sub_re]
  have hh := fixedPointRow_sum_error q xs as hlen has
  have he : ((value q rhs).re-(value q (List.zipWith (fun x a => tdivN q (x*a)) xs as).sum).re)-
      ((value q rhs).re-(List.zipWith (fun x a => (value q x).re*(value q a).re) xs as).sum) =
      -((value q (List.zipWith (fun x a => tdivN q (x*a)) xs as).sum).re-
        (List.zipWith (fun x a => (value q x).re*(value q a).re) xs as).sum) := by ring
  rw [he,abs_neg]
  exact hh

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
