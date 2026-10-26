module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightArgument

/-! Reuse the similarity argument program at either retained coordinate,
keeping both stored samples and the q/P powers outside its scratch registers. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellRationalArgs

def similarityArgumentEquiv (target : Bool) : Equiv.Perm (Fin 48) :=
  ((((Equiv.swap 38 47).trans (Equiv.swap 39 44)).trans (Equiv.swap 40 45)).trans
    (Equiv.swap 41 46)).trans (if target then Equiv.swap 37 38 else Equiv.refl _)

def similarityArgumentAt (target : Bool) : TblCode 48 :=
  weightArgument.rename (similarityArgumentEquiv target)

theorem similarityArgumentAt_do {A V w s t u j : ℕ} (target : Bool) (st : TblSt 48 A)
    (hs : st.val 34 = s) (ht : st.val 35 = t) (hu : st.val 36 = u)
    (hj : st.val (if target then 38 else 37) = j)
    (hdouble : st.val 47 = 2*s) (hden : st.val 44 = similarityDenominator s t)
    (hs0 : 0 < s) (hindex : 2*t*j+s < 2^V) (hsV : 2*s < 2^V)
    (hsq : s^2 < 2^V) (huV : u*s^2 < 2^V) :
    TblDo A V w (similarityArgumentAt target) st (fun st' =>
      st'.val 20 = similarityNumerator s t u j ∧ st'.val 21 = similarityDenominator s t ∧
      st'.acc = st.acc ∧ ∀ r, r ∉ [(20 : Fin 48),21,45,46] → st'.val r = st.val r) 8 := by
  let e := similarityArgumentEquiv target
  have hargs := (weightArgument_do (A := A) (V := V) (w := w) (st.restrict e)
    (by cases target <;> simpa [TblSt.restrict,e,similarityArgumentEquiv,Equiv.swap_apply_def] using hs)
    (by cases target <;> simpa [TblSt.restrict,e,similarityArgumentEquiv,Equiv.swap_apply_def] using ht)
    (by cases target <;> simpa [TblSt.restrict,e,similarityArgumentEquiv,Equiv.swap_apply_def] using hu)
    (by cases target <;> simpa [TblSt.restrict,e,similarityArgumentEquiv,Equiv.swap_apply_def] using hj)
    (by cases target <;> simpa [TblSt.restrict,e,similarityArgumentEquiv,Equiv.swap_apply_def] using hdouble)
    (by cases target <;> simpa [TblSt.restrict,e,similarityArgumentEquiv,Equiv.swap_apply_def] using hden)
    hs0 hindex hsV hsq huV).rename e.injective
  refine hargs.mono (fun st' h => ?_) le_rfl
  refine ⟨?_,?_,h.1.2.2.1,?_⟩
  · cases target <;> simpa [TblSt.restrict,e,similarityArgumentEquiv,Equiv.swap_apply_def] using h.1.1
  · cases target <;> simpa [TblSt.restrict,e,similarityArgumentEquiv,Equiv.swap_apply_def] using h.1.2.1
  · intro r hr
    have he : e (e.symm r) = r := e.apply_symm_apply r
    have hnot : e.symm r ∉ [(20 : Fin 48),21,40,41] := by
      intro hn
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
      rcases hn with hn | hn | hn | hn
      all_goals have hh := congrArg e hn
      all_goals rw [he] at hh
      all_goals cases target <;> simp [e,similarityArgumentEquiv,Equiv.swap_apply_def] at hh
      all_goals subst r; simp at hr
    have hh := h.1.2.2.2 (e.symm r) hnot
    simpa only [TblSt.restrict,Function.comp_apply,he] using hh

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
