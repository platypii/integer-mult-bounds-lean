module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackDiagonal

/-! Exchange two fields or scale them by reciprocal units using reversed children on a flat bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open Matrix M8.ReversedExchange
variable {R : Type*}

/-- Apply the two atom maps as the reversed slices arrive at their destinations. -/
def mapChildAt (f g : R → R) (start width gap : ℕ) (bank : List R) : List R :=
  let rest := bank.drop start
  let later := rest.drop (width + gap)
  bank.take start ++ (later.take width).reverse.map f ++ (rest.drop width).take gap ++
    (rest.take width).reverse.map g ++ later.drop width

def childAt := @mapChildAt R id id

theorem mapChildAt_fields (f g : R → R) (pre x gap y post : List R) (h : y.length = x.length) :
    mapChildAt f g pre.length x.length gap.length (pre ++ x ++ gap ++ y ++ post) =
      pre ++ y.reverse.map f ++ gap ++ x.reverse.map g ++ post := by
  simp [mapChildAt,List.append_assoc,← List.drop_drop,h]

theorem childAt_fields (pre x gap y post : List R) (h : y.length = x.length) :
    childAt pre.length x.length gap.length (pre ++ x ++ gap ++ y ++ post) =
      pre ++ y.reverse ++ gap ++ x.reverse ++ post := by
  simpa [childAt] using mapChildAt_fields id id pre x gap y post h

theorem childAt_weighted [CommRing R] {n : ℕ} (pre gap post : List R) (x y : Fin n → R) :
    let s := Weighted.weighted (rev n) 1 1 (x,y)
    childAt pre.length n gap.length (pre ++ List.ofFn x ++ gap ++ List.ofFn y ++ post) =
      pre ++ List.ofFn s.1 ++ gap ++ List.ofFn s.2 ++ post := by
  have h := childAt_fields pre (List.ofFn x) gap (List.ofFn y) post (by simp)
  simpa [Weighted.weighted,reversed_word] using h

/-- Reverse one field by exchanging its halves around its possible middle atom. -/
def reverseAt (start width : ℕ) := childAt (R := R) start (width/2) (width%2)

theorem reverseAt_field (pre x post : List R) :
    reverseAt pre.length x.length (pre ++ x ++ post) = pre ++ x.reverse ++ post := by
  let k := x.length / 2
  let a := x.take k
  let mid := (x.drop k).take (x.length % 2)
  let b := (x.drop k).drop (x.length % 2)
  have ha : a.length = k := by simp [a,k]; omega
  have hm : mid.length = x.length % 2 := by simp [mid,k]; omega
  have hb : b.length = k := by simp [b,k]; omega
  have decomp : a ++ mid ++ b = x := by simp [a,mid,b]
  have pal : mid.reverse = mid := by
    have short : mid.length ≤ 1 := by omega
    revert short
    generalize mid = l
    intro short
    cases l with
    | nil => rfl
    | cons z zs =>
      cases zs with
      | nil => rfl
      | cons t ts => simp at short
  unfold reverseAt
  change childAt pre.length k (x.length % 2) _ = _
  rw [← ha,← hm,← decomp]
  simpa [List.append_assoc,List.reverse_append,pal] using
    childAt_fields pre a mid b post (hb.trans ha.symm)

/-- The first and third children reverse the later slice. The middle child
exchanges the two slices, reversing each. -/
def exchangeAt (start width gap : ℕ) (bank : List R) : List R :=
  let later := start + width + gap
  reverseAt later width (childAt start width gap (reverseAt later width bank))

theorem exchangeAt_fields (pre x gap y post : List R) (h : y.length = x.length) :
    exchangeAt pre.length x.length gap.length (pre ++ x ++ gap ++ y ++ post) =
      pre ++ y ++ gap ++ x ++ post := by
  dsimp only [exchangeAt]
  have first := reverseAt_field (pre ++ x ++ gap) y post
  simp only [List.length_append,h] at first
  rw [first,childAt_fields _ _ _ _ _ (by simpa using h),List.reverse_reverse]
  have last := reverseAt_field (pre ++ y ++ gap) x.reverse post
  simpa only [List.length_append,List.length_reverse,h,List.reverse_reverse] using last

variable [CommRing R]

/-- A uniformly weighted reversed child on the same two slices. -/
def unitChildAt (u : Rˣ) := mapChildAt (fun t => (u : R) * t) (fun t => (↑u⁻¹ : R) * t)

theorem unitChildAt_weighted {n : ℕ} (u : Rˣ) (pre gap post : List R) (x y : Fin n → R) :
    let s := Weighted.weighted (rev n) (diagonal fun _ => (u : R))
      (diagonal fun _ => (↑u⁻¹ : R)) (x,y)
    unitChildAt u pre.length n gap.length (pre ++ List.ofFn x ++ gap ++ List.ofFn y ++ post) =
      pre ++ List.ofFn s.1 ++ gap ++ List.ofFn s.2 ++ post := by
  have h := mapChildAt_fields (fun t => (u : R) * t) (fun t => (↑u⁻¹ : R) * t)
    pre (List.ofFn x) gap (List.ofFn y) post (by simp)
  simp only [List.length_ofFn] at h
  rw [unitChildAt,h]
  simp only [Weighted.weighted,← reversed_word,List.map_ofFn,Function.comp_def]
  have scale (a : R) (z : Fin n → R) :
      (diagonal fun _ => a) *ᵥ z = fun i => a * z i := funext (mulVec_diagonal _ _)
  simp only [rev_mulVec,scale]

/-- Two reversed children suffice for a reciprocal pair: the uniform weights commute
with reversal, so the second exchange restores the order within each field. -/
theorem pairAt_fields (u : Rˣ) (pre x gap y post : List R) (h : y.length = x.length) :
    unitChildAt u⁻¹ pre.length x.length gap.length
      (childAt pre.length x.length gap.length (pre ++ x ++ gap ++ y ++ post)) =
      pre ++ x.map (fun t => (↑u⁻¹ : R) * t) ++ gap ++ y.map (fun t => (u : R) * t) ++ post := by
  rw [childAt_fields _ _ _ _ _ h]
  have step := mapChildAt_fields (fun t => (↑u⁻¹ : R) * t) (fun t => (u : R) * t)
    pre y.reverse gap x.reverse post (by simp [h])
  simpa [unitChildAt,h] using step

end IntegerMultBounds.MathlibTM2.Cover.Fallback
