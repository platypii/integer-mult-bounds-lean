module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellMaskedIndexedWord
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedInterval

/-! Consume a unary mask bit and gather either the indexed word or an encoded zero. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ T Q A U}

theorem maskedPackedWord_exec {mask index width src dst skip savedSkip saved tmp work₁ work₂ : Fin T}
    (hreg : [mask,index,width,src,dst,skip,savedSkip,saved,tmp,work₁,work₂].Nodup)
    (flag : Bool) (w a L j : ℕ) {s : ℕ} (F : ZMod s → GaussianInt)
    (hfit : a+L ≤ s) (hj : j < L)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hmask : S.R mask = if flag then [tick] else [])
    (hindex : (S.R index).length = j) (hwidth : (S.R width).length = w)
    (hsrc : S.R src = cstream A w (packedInterval a L F)++tail)
    (hfresh : ∀ r ∈ [skip,savedSkip,saved,tmp,work₁,work₂], S.R r = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ j*(12*w+9)+10*w+28 ∧
      Exec body (maskedIndexedWord mask index width src dst skip savedSkip saved tmp work₁ work₂) (mk v S) m
        (mk v' {S with R := Function.update (Function.update S.R dst
          (csyms A w (if flag then F ((a+j : ℕ) : ZMod s) else 0)++S.R dst)) mask []}) := by
  have he := maskedIndexedWord_exec (body := body) hreg flag w j (packedInterval a L F)
    (by simpa only [packedInterval_length F hfit] using hj) tail v S hmask hindex hwidth hsrc hfresh
  simpa only [packedInterval_get F hfit hj] using he


/-- An unselected lookup never reads the source or index, including empty halos. -/
theorem maskedIndexedWord_false_exec {mask index width src dst skip savedSkip saved tmp work₁ work₂ : Fin T}
    (hreg : [mask,index,width,src,dst,skip,savedSkip,saved,tmp,work₁,work₂].Nodup)
    (v : HS T Q A U) (S : Stacks T A) (hmask : S.R mask = [])
    (hsaved : S.R saved = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (maskedIndexedWord mask index width src dst skip savedSkip saved tmp work₁ work₂)
        (mk v S) (4*(S.R width).length+8)
        (mk v' {S with R := (Function.update S.R dst
          (csyms A (S.R width).length 0++S.R dst))}) := by
  have hr := hreg
  regs_ne hr
  have hp := Exec.act (body := body) (peekR mask) (mk v S)
  rw [peekR_run,hmask] at hp
  obtain ⟨v₁,hu₁,he₁⟩ := copyR_exec body width dst saved
    ‹width ≠ dst› ‹width ≠ saved› ‹dst ≠ saved› (fun _ => pairSym A false false)
    {v with flag := false} S hsaved
  let S₁ : Stacks T A := {S with R := (Function.update S.R dst
    (csyms A (S.R width).length 0++S.R dst))}
  have he₁' : Exec body (copyR width dst saved (fun _ => pairSym A false false))
      (mk {v with flag := false} S) (4*(S.R width).length+4) (mk v₁ S₁) := by
    simpa [S₁,csyms_zero,List.map_const'] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := uclear_exec body mask v₁ S₁
  have hm : S₁.R mask = [] := by simp [S₁,‹mask ≠ dst›,hmask]
  refine ⟨v₂,hu₂.trans hu₁,?_⟩
  have hc : Exec body (.cond (·.flag)
      (copyIndexedWord index width src dst skip savedSkip saved tmp work₁ work₂)
      (copyR width dst saved (fun _ => pairSym A false false)))
      (mk {v with flag := false} S) (4*(S.R width).length+5) (mk v₁ S₁) :=
    Exec.cond_false rfl he₁'
  have he := Exec.seq hp (Exec.seq hc he₂)
  have hclear : Function.update S₁.R mask [] = S₁.R := by
    rw [← hm]
    exact Function.update_eq_self _ _
  exact he.cast (by simp [hm]; omega) (by simp only [hclear]; rfl)

theorem maskedPackedWord_guarded_exec {mask index width src dst skip savedSkip saved tmp work₁ work₂ : Fin T}
    (hreg : [mask,index,width,src,dst,skip,savedSkip,saved,tmp,work₁,work₂].Nodup)
    (flag : Bool) (w a L j : ℕ) {s : ℕ} (F : ZMod s → GaussianInt)
    (hfit : a+L ≤ s) (hj : flag = true → j < L)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hmask : S.R mask = if flag then [tick] else [])
    (hindex : (S.R index).length = j) (hwidth : (S.R width).length = w)
    (hsrc : S.R src = cstream A w (packedInterval a L F)++tail)
    (hfresh : ∀ r ∈ [skip,savedSkip,saved,tmp,work₁,work₂], S.R r = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ j*(12*w+9)+10*w+28 ∧
      Exec body (maskedIndexedWord mask index width src dst skip savedSkip saved tmp work₁ work₂) (mk v S) m
        (mk v' {S with R := Function.update (Function.update S.R dst
          (csyms A w (if flag then F ((a+j : ℕ) : ZMod s) else 0)++S.R dst)) mask []}) := by
  cases flag with
  | true =>
    exact maskedPackedWord_exec (body := body) hreg true w a L j F hfit (hj rfl)
      tail v S hmask hindex hwidth hsrc hfresh
  | false =>
    obtain ⟨v',hu,he⟩ := maskedIndexedWord_false_exec (body := body) hreg v S
      (by simpa using hmask) (hfresh saved (by simp))
    refine ⟨v',4*w+8,hu,by omega,?_⟩
    have hr := hreg
    regs_ne hr
    have hz : S.R mask = [] := by simpa using hmask
    have hclear : Function.update (Function.update S.R dst (csyms A w 0++S.R dst)) mask [] =
        Function.update S.R dst (csyms A w 0++S.R dst) := by
      funext k
      by_cases hk : k = mask
      · subst k; simp [‹mask ≠ dst›,hz]
      · simp [Function.update_of_ne hk]
    simpa only [hwidth,Bool.false_eq_true,ite_false,hclear] using he

theorem maskedPackedAmbientWord_exec {mask index width src dst skip savedSkip saved tmp work₁ work₂ : Fin T}
    (hreg : [mask,index,width,src,dst,skip,savedSkip,saved,tmp,work₁,work₂].Nodup)
    (flag : Bool) (w a L k : ℕ) {s : ℕ} (F : ZMod s → GaussianInt)
    (hfit : a+L ≤ s) (hk : flag = true → a ≤ k ∧ k < a+L)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hmask : S.R mask = if flag then [tick] else [])
    (hindex : (S.R index).length = k-a) (hwidth : (S.R width).length = w)
    (hsrc : S.R src = cstream A w (packedInterval a L F)++tail)
    (hfresh : ∀ r ∈ [skip,savedSkip,saved,tmp,work₁,work₂], S.R r = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ (k-a)*(12*w+9)+10*w+28 ∧
      Exec body (maskedIndexedWord mask index width src dst skip savedSkip saved tmp work₁ work₂) (mk v S) m
        (mk v' {S with R := Function.update (Function.update S.R dst
          (csyms A w (if flag then F (k : ZMod s) else 0)++S.R dst)) mask []}) := by
  obtain ⟨v',m,hu,hm,he⟩ := maskedPackedWord_guarded_exec (body := body) hreg flag w a L (k-a) F
    hfit (by intro hf; have hh := hk hf; omega) tail v S hmask hindex hwidth hsrc hfresh
  refine ⟨v',m,hu,hm,?_⟩
  have hz : (if flag then F ((a+(k-a) : ℕ) : ZMod s) else 0) =
      (if flag then F (k : ZMod s) else 0) := by
    cases flag
    · rfl
    · simp only [ite_true,Nat.add_sub_of_le (hk rfl).1]
  simpa only [hz] using he

theorem maskedPackedAmbientWord_selected_index_exec {mask index width src dst skip savedSkip saved tmp work₁ work₂ : Fin T}
    (hreg : [mask,index,width,src,dst,skip,savedSkip,saved,tmp,work₁,work₂].Nodup)
    (flag : Bool) (w a L k : ℕ) {s : ℕ} (F : ZMod s → GaussianInt)
    (hfit : a+L ≤ s) (hk : flag = true → a ≤ k ∧ k < a+L)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hmask : S.R mask = if flag then [tick] else [])
    (hindex : flag = true → (S.R index).length = k-a) (hwidth : (S.R width).length = w)
    (hsrc : S.R src = cstream A w (packedInterval a L F)++tail)
    (hfresh : ∀ r ∈ [skip,savedSkip,saved,tmp,work₁,work₂], S.R r = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ (if flag then k-a else 0)*(12*w+9)+10*w+28 ∧
      Exec body (maskedIndexedWord mask index width src dst skip savedSkip saved tmp work₁ work₂) (mk v S) m
        (mk v' {S with R := Function.update (Function.update S.R dst
          (csyms A w (if flag then F (k : ZMod s) else 0)++S.R dst)) mask []}) := by
  cases flag with
  | true =>
    exact maskedPackedAmbientWord_exec (body := body) hreg true w a L k F hfit hk
      tail v S hmask (hindex rfl) hwidth hsrc hfresh
  | false =>
    obtain ⟨v',hu,he⟩ := maskedIndexedWord_false_exec (body := body) hreg v S
      (by simpa using hmask) (hfresh saved (by simp))
    refine ⟨v',4*w+8,hu,by omega,?_⟩
    have hr := hreg
    regs_ne hr
    have hz : S.R mask = [] := by simpa using hmask
    have hclear : Function.update (Function.update S.R dst (csyms A w 0++S.R dst)) mask [] =
        Function.update S.R dst (csyms A w 0++S.R dst) := by
      funext k
      by_cases hk : k = mask
      · subst k; simp [‹mask ≠ dst›,hz]
      · simp [Function.update_of_ne hk]
    simpa only [hwidth,Bool.false_eq_true,ite_false,hclear] using he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
