module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntegerRowConsume

/-! # Stable context for the executed integer row loop -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

structure IntegerRowContext {A : ℕ} (L w : ℕ) (xs : List GaussianInt)
    (tailX : List (Fin (A + 4))) (S : Stacks 117 A) : Prop where
  width_pos : 1 ≤ w
  length : xs.length = L
  fits : ∀ x ∈ xs, Fits w x
  rows : (S.R 102).length = L
  width : (S.R 94).length = w
  column : S.R 110 = cstream A w xs ++ tailX
  clean : CClean mul S
  ready : Ready (fun r => S.R (cr r)) w 0
  work : ∀ k ∈ integerRowWork, S.R k = []

/-- Reading the stored column gives the actual signed entry, not merely its residue. -/
theorem IntegerRowContext.decode {A L w : ℕ} {xs : List GaussianInt}
    {tailX : List (Fin (A + 4))} {S : Stacks 117 A}
    (h : IntegerRowContext L w xs tailX S) (hA : 4 ≤ A) (i : ℕ) (hi : i < L) :
    decodeWord (((S.R 110).drop (i * w)).take w) = xs.getD i 0 := by
  have hi' : i < xs.length := by rw [h.length]; exact hi
  rw [h.column, cstream_word w xs tailX i hi',
    decodeWord_of_fits hA h.width_pos _ (h.fits _ (List.getElem_mem hi'))]
  exact (List.getD_eq_getElem _ _ hi').symm

/-- Loop control, consumed row sources and publication are outside the stable
column/readiness/workspace footprint. -/
theorem IntegerRowContext.update {A L w : ℕ} {xs : List GaussianInt}
    {tailX : List (Fin (A + 4))} {S : Stacks 117 A}
    (h : IntegerRowContext L w xs tailX S) (k : Fin 117)
    (hk : k ∈ [(100 : Fin 117), 101, 103, 108, 111, 112, 113, 116]) (zs : List (Fin (A + 4))) :
    IntegerRowContext L w xs tailX { S with R := Function.update S.R k zs } := by
  have hhigh : 96 ≤ k.val := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hsmall (j : Fin 117) (hj : j.val < 96) : j ≠ k := by
    intro he
    have hv := congrArg Fin.val he
    omega
  have hoff : (102 : Fin 117) ≠ k ∧ (110 : Fin 117) ≠ k := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  refine ⟨h.width_pos, h.length, h.fits, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hoff.1] using h.rows
  · simpa [hsmall 94 (by decide)] using h.width
  · simpa [hoff.2] using h.column
  · intro i
    refine ⟨(h.clean i).1, ?_⟩
    simpa [hsmall (mul i) (by have hi := i.isLt; simp [mul]; omega)] using (h.clean i).2
  · have hrho : (fun r => Function.update S.R k zs (cr r)) = fun r => S.R (cr r) := by
      funext r
      simp [hsmall (cr r) (by have hr := (cr_range r).2.1; omega)]
    change Ready (fun r => Function.update S.R k zs (cr r)) w 0
    rw [hrho]
    exact h.ready
  · intro j hj
    have hd : integerRowWork.Disjoint [(100 : Fin 117), 101, 103, 108, 111, 112, 113, 116] := by
      simp [integerRowWork, cr, OutputPlacement.code]
    have hne : j ≠ k := by
      intro he
      subst j
      exact List.disjoint_left.mp hd hj hk
    simpa [hne] using h.work j hj

/-- Replacing the owned column prefix retains the same row-call context once
the new vector's length and signed fits have been proved. -/
theorem IntegerRowContext.replaceColumn {A L w : ℕ} {xs ys : List GaussianInt}
    {tailX : List (Fin (A + 4))} {S : Stacks 117 A}
    (h : IntegerRowContext L w xs tailX S) (hlen : ys.length = L) (hfits : ∀ y ∈ ys, Fits w y) :
    IntegerRowContext L w ys tailX { S with R := Function.update S.R 110 (cstream A w ys ++ tailX) } := by
  refine ⟨h.width_pos, hlen, hfits, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using h.rows
  · simpa using h.width
  · simp
  · intro i
    refine ⟨(h.clean i).1, ?_⟩
    have hi : mul i ≠ 110 := by
      intro he
      have hv := congrArg Fin.val he
      have hil := i.isLt
      simp only [mul] at hv
      omega
    simpa [hi] using (h.clean i).2
  · have hrho : (fun r => Function.update S.R 110 (cstream A w ys ++ tailX) (cr r)) =
        fun r => S.R (cr r) := by
      funext r
      have hr : cr r ≠ 110 := by
        have hh := (cr_range r).2.1
        intro he
        have hv := congrArg Fin.val he
        omega
      simp [hr]
    change Ready (fun r => Function.update S.R 110 (cstream A w ys ++ tailX) (cr r)) w 0
    rw [hrho]
    exact h.ready
  · intro k hk
    have hd : integerRowWork.Disjoint [(110 : Fin 117)] := by simp [integerRowWork, cr, OutputPlacement.code]
    have hne : k ≠ 110 := by
      intro he
      subst k
      exact List.disjoint_left.mp hd hk (by simp)
    simpa [hne] using h.work k hk

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
