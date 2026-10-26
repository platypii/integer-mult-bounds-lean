module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRealPrefix
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingRowField

/-! Real projection preserves the executed coupling arithmetic with real coefficients. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN

@[simp] theorem realPartWord_re (z : GaussianInt) : (realPartWord z).re = z.re := rfl
@[simp] theorem realPartWord_im (z : GaussianInt) : (realPartWord z).im = 0 := rfl

@[simp] theorem value_realPartWord_re (q : ℕ) (z : GaussianInt) :
    (value q (realPartWord z)).re = (value q z).re := by
  simp [value,realPartWord]

@[simp] theorem value_realPartWord_norm (q : ℕ) (z : GaussianInt) :
    ‖value q (realPartWord z)‖ = |(value q z).re| := by
  have h : value q (realPartWord z) = ((value q z).re : ℂ) := by
    apply Complex.ext <;> simp only [value,realPartWord,Int.cast_zero,zero_div,Complex.ofReal_re,Complex.ofReal_im]
  rw [h,Complex.norm_real,Real.norm_eq_abs]

theorem realPartWord_row (q : ℕ) (rhs : GaussianInt) (xs as : List GaussianInt)
    (has : ∀ a ∈ as, a.im = 0) :
    realPartWord (rhs-(List.zipWith (fun x a => tdivN q (x*a)) xs as).sum) =
      realPartWord rhs-(List.zipWith (fun x a => tdivN q (x*a)) (xs.map realPartWord) as).sum := by
  have hsum : realPartWord ((List.zipWith (fun x a => tdivN q (x*a)) xs as).sum) =
      (List.zipWith (fun x a => tdivN q (x*a)) (xs.map realPartWord) as).sum := by
    induction xs generalizing as with
    | nil => simp only [List.zipWith_nil_left,List.map_nil,List.sum_nil]; rfl
    | cons x xs ih =>
      cases as with
      | nil => simp only [List.zipWith_nil_right,List.sum_nil]; rfl
      | cons a as =>
        have ha := has a (by simp)
        have ht := ih as (fun a ha => has a (by simp [ha]))
        have hp : realPartWord (tdivN q (x*a)) = tdivN q (realPartWord x*a) := by
          ext <;> simp [realPartWord,tdivN,Zsqrtd.re_mul,Zsqrtd.im_mul,ha]
        have hadd (x y : GaussianInt) : realPartWord (x+y) = realPartWord x+realPartWord y := by
          ext <;> simp [realPartWord]
        simpa only [List.zipWith_cons_cons,List.map_cons,List.sum_cons,hadd,hp] using
          congrArg (fun z => tdivN q (realPartWord x*a)+z) ht
  have hsub (x y : GaussianInt) : realPartWord (x-y) = realPartWord x-realPartWord y := by
    ext <;> simp [realPartWord]
  rw [hsub,hsum]

theorem couplingInputWords_realPart {s : ℕ} [NeZero s] (boundary : Bool)
    (t band a b i : ℕ) (C : ZMod s → GaussianInt) :
    (couplingInputWords boundary t band a b i C).map realPartWord =
      couplingInputWords boundary t band a b i (fun j => realPartWord (C j)) := by
  simp only [couplingInputWords,List.map_map]
  apply List.map_congr_left
  intro δ hδ
  dsimp only [Function.comp_def]
  split_ifs <;> rfl

theorem couplingRowField_realPart {s : ℕ} [NeZero s] (P q t u band a b : ℕ)
    (boundary : Bool) (C B : ZMod s → GaussianInt) (i : ZMod s) :
    realPartWord (couplingRowField P q t u band a b boundary C B i) =
      couplingRowField P q t u band a b boundary
        (fun j => realPartWord (C j)) (fun j => realPartWord (B j)) i := by
  unfold couplingRowField couplingRowWord
  rw [realPartWord_row q _ _ _ (by
    intro z hz
    obtain ⟨δ,hδ,rfl⟩ := List.mem_map.mp hz
    rfl),couplingInputWords_realPart]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
