module

public import IntegerMultBounds.MathlibTM2.Fast.CMulStream
public import IntegerMultBounds.MathlibTM2.Layer.GaussStream

/-! # Shared word subtraction with exact stack framing -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node

variable {T Q A : ℕ} {U P : Type}

/-- The Gaussian linear map `(x, y) ↦ x - y`. -/
def rsbSubG : Fin 1 → Fin 2 → ℤ × ℤ := ![![(1, 0), (-1, 0)]]

/-- `glin rsbSubG` subtracts. -/
lemma glin_rsbSubG {W : ℕ} (x y : GaussianInt) :
    glin rsbSubG ![red W x, red W y] 0 = red W (x - y) := by
  rw [glin_eq_sum_mulG, Fin.sum_univ_two, sub_eq_add_neg, red_add, red_neg]
  simp [rsbSubG, GR.mulG, Prod.ext_iff]

/-- One word of the subtraction automaton on the tops of `a` and `b`, the result reversed onto
`o`; the state lives in scan slot `o`, the word length is `|ctr|`, `tmp` is a spare. -/
def rsbSubWord (a b o ctr tmp : Fin T) : Pr P T Q A U :=
  .seq (.act (.load (fun v => { v with
      scan := Function.update v.scan o (gaussAuto A rsbSubG 2 false).init }) .done))
    (autoWord 0 ![a, b] ![o] o ctr tmp (gaussAuto A rsbSubG 2 false))

/-- The first `w` columns of two registers topped by coefficient symbols. -/
lemma cols_csyms {A w : ℕ} (x y : GaussianInt) (rx ry : List (Fin (A + 4))) :
    Auto.cols (fun i : Fin 2 => (![csyms A w x ++ rx, csyms A w y ++ ry] : Fin 2 → _) i) w 0 =
      symCols A ![red w x, red w y] := by
  simp only [Auto.cols, symCols, ← List.map_coe_finRange_eq_range, List.map_map, List.ofFn_eq_map]
  apply List.map_congr_left
  intro t _
  funext i
  fin_cases i
  · simp [List.getD_eq_getElem?_getD, csyms, List.getElem?_append, t.isLt]
  · simp [List.getD_eq_getElem?_getD, csyms, List.getElem?_append, t.isLt]

/-- Subtract one Gaussian word, consume both inputs, preserve arbitrary suffixes,
and restore the exact count and temporary stack. No multiplier bank is used. -/
theorem subWord_exec {body : P → Pr P T Q A U} {a b o ctr tmp : Fin T}
    (hreg : [a, b, o, ctr, tmp].Nodup) (hA : 96 ≤ A) (w : ℕ)
    (v : HS T Q A U) (S : Stacks T A) (x y : GaussianInt)
    (rx ry : List (Fin (A + 4)))
    (hx : S.R a = csyms A w x ++ rx) (hy : S.R b = csyms A w y ++ ry)
    (hc : (S.R ctr).length = w) (ht : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (rsbSubWord a b o ctr tmp) (mk v S) (5 * w + 6)
        (mk v' { S with R := (Function.update (Function.update (Function.update S.R a rx) b ry) o
          ((csyms A w (x - y)).reverse ++ S.R o)) }) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hreg
  obtain ⟨⟨hab, hao, hac, hat⟩, ⟨hbo, hbc, hbt⟩, ⟨hoc, hot⟩, hct, _⟩ := hreg
  have hlay : AutoLayout ![a, b] ![o] o ctr tmp :=
    { ins_inj := by
        intro i j h
        fin_cases i <;> fin_cases j <;> simp_all
      outs_inj := by intro i j _; exact Subsingleton.elim i j
      ins_outs := by intro i j; fin_cases i <;> fin_cases j <;> simp_all
      ins_ctr := by intro i; fin_cases i <;> simp_all
      ins_tmp := by intro i; fin_cases i <;> simp_all
      outs_ctr := by intro j; fin_cases j; simp_all
      outs_tmp := by intro j; fin_cases j; simp_all
      ctr_tmp := ‹ctr ≠ tmp›
      ins_st := by intro i; fin_cases i <;> simp_all }
  let v₁ : HS T Q A U := { v with scan := Function.update v.scan o (gaussAuto A rsbSubG 2 false).init }
  have he₁ : Exec body (.act (.load (fun v => { v with
      scan := Function.update v.scan o (gaussAuto A rsbSubG 2 false).init }) .done))
      (mk v S) 1 (mk v₁ S) := Exec.act _ _
  obtain ⟨v₂, S₂, hu₂, he₂, _, _, hfr, hctr₂, htmp₂, hins, houts⟩ :=
    autoWord_exec body hlay (gaussAuto A rsbSubG 2 false) 0 (cs := S.R ctr) v₁ S rfl ht (by simp [v₁])
  have hcols : Auto.cols (fun i => S.R ((![a, b] : Fin 2 → Fin T) i)) (S.R ctr).length 0 =
      symCols A ![red w x, red w y] := by
    rw [hc, ← cols_csyms x y rx ry]
    congr 1
    funext i
    fin_cases i <;> simp [hx, hy]
  have hrun := gaussAuto_runWord_gen (A := A) (B := 2) (g := rsbSubG) (by omega)
    (by intro j; fin_cases j; simp [rsbSubG, Fin.sum_univ_two])
    (by norm_num; omega) false ![red w x, red w y]
  simp only [swapGR_false] at hrun
  have hout : S₂.R o = (csyms A w (x - y)).reverse ++ S.R o := by
    have hh := houts 0
    simp only [Matrix.cons_val_fin_one] at hh
    rw [hh, hcols, hrun, symCols_map, glin_rsbSubG]
  have hframe : S₂ = { S with R := (Function.update (Function.update (Function.update S.R a rx) b ry) o
      ((csyms A w (x - y)).reverse ++ S.R o)) } := by
    ext1
    · exact hfr.1
    · exact hfr.2.1
    · exact hfr.2.2.1
    funext k
    by_cases ho : k = o
    · subst k; simpa using hout
    by_cases hb : k = b
    · subst k
      have hh := hins 1
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at hh
      rw [hh, hy, hc]
      simp [ho, csyms]
    by_cases ha : k = a
    · subst k
      have hh := hins 0
      simp only [Matrix.cons_val_zero] at hh
      rw [hh, hx, hc]
      simp [ho, hb, csyms]
    simp only [Function.update_of_ne ho, Function.update_of_ne hb, Function.update_of_ne ha]
    by_cases hct : k = ctr
    · subst k; exact hctr₂
    by_cases htm : k = tmp
    · subst k; exact htmp₂.trans ht.symm
    apply hfr.2.2.2 k _ _ hct htm
    · rintro ⟨i, hi⟩
      fin_cases i
      · exact ha (by simpa using hi.symm)
      · exact hb (by simpa using hi.symm)
    · rintro ⟨j, hj⟩
      fin_cases j
      exact ho (by simpa using hj.symm)
  refine ⟨v₂, hu₂, (Exec.seq he₁ he₂).cast (by rw [hc]; omega) ?_⟩
  exact congrArg (mk v₂) hframe

end IntegerMultBounds.MathlibTM2.Fast
