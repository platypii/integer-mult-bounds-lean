module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackModularPower
public import IntegerMultBounds.MathlibTM2.Cover.FallbackReciprocal
public import IntegerMultBounds.MathlibTM2.Host.OrderedMove
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedLoop

/-! The reciprocal iteration keeps the fixed factor x^(p-1) alongside its accumulator. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open Mult.PhaseCellToeplitz (countedLoop countedLoop_exec)
variable {T Q A M : ℕ} {P U : Type}

def reciprocalUpdate (p : ℕ) (r : Fin 14 ↪ Fin T) : Pr P T Q A U :=
  .seq (modularPower r p) (.seq (bclear (r 0)) (moveRightOrdered (r 2) (r 3) (r 0)))

theorem reciprocalUpdate_exec [NeZero M] (body : P → Pr P T Q A U) (p : ℕ) (r : Fin 14 ↪ Fin T)
    (H : ℕ) (hm : M < 2^H) (y b : ZMod M) (v : HS T Q A U) (S : Stacks T A)
    (acc : S.R (r 0) = binSyms H y.val) (factor : S.R (r 1) = binSyms H b.val)
    (modulus : S.R (r 4) = binSyms H M)
    (free : ∀ i : Fin 14, 2 ≤ i → i ≠ 4 → i < 13 → S.R (r i) = []) :
    ∃ z t, z.user = v.user ∧ t ≤ 12*H+12+p*(48*H*H+152*H+66) ∧
      Exec body (reciprocalUpdate p r) (mk v S) t
        (mk z {S with R := Function.update S.R (r 0) (binSyms H (y^p*b).val)}) := by
  obtain ⟨u,t,hu,ht,power⟩ := modularPower_exec body p r H hm y b v S acc factor modulus free
  let word := binSyms (A := A) H (y^p*b).val
  let D : Stacks T A := {S with R := Function.update S.R (r 2) word}
  obtain ⟨w,hw,_,clear⟩ := bclear_exec body (r 0) u D
  let E : Stacks T A := {D with R := Function.update D.R (r 0) []}
  obtain ⟨z,hz,move⟩ := moveRightOrdered_exec (body := body) (r 2) (r 3) (r 0)
    (r.injective.ne (by decide)) (r.injective.ne (by decide)) (r.injective.ne (by decide))
    w E (by simp [E,D,r.injective.eq_iff,free 3 (by decide) (by decide) (by decide)])
  have len : (D.R (r 0)).length = H := by simp [D,r.injective.eq_iff,acc,length_binSyms]
  rw [len] at clear
  have val : E.R (r 2) = word := by simp [E,D,r.injective.eq_iff]
  have final : Function.update (Function.update E.R (r 2) []) (r 0) (word++E.R (r 0)) =
      Function.update S.R (r 0) word := by
    funext i
    by_cases h : i = r 0 <;> by_cases h' : i = r 2 <;>
      simp_all [E,D,r.injective.eq_iff,free 2 (by decide) (by decide) (by decide)]
  rw [val,final,show word.length = H from length_binSyms _ _] at move
  exact ⟨z,t+((2*H+2)+(4*H+4)),hz.trans (hw.trans hu),by omega,Exec.seq power (Exec.seq clear move)⟩

theorem reciprocalLoop_exec (body : P → Pr P T Q A U) (p w : ℕ) (hp : p.Prime)
    [NeZero (p^(w+1))] (x : ZMod (p^(w+1))) (hx : IsUnit x) (r : Fin 14 ↪ Fin T)
    (count : Fin T) (outside : ∀ i, r i ≠ count) (H : ℕ) (hm : p^(w+1) < 2^H)
    (v : HS T Q A U) (S : Stacks T A) (ticks : (S.R count).length = w)
    (acc : S.R (r 0) = binSyms H (x^(p-2)).val)
    (factor : S.R (r 1) = binSyms H (x^(p-1)).val)
    (modulus : S.R (r 4) = binSyms H (p^(w+1)))
    (free : ∀ i : Fin 14, 2 ≤ i → i ≠ 4 → i < 13 → S.R (r i) = []) :
    ∃ z F t, z.user = v.user ∧ t ≤ w*(12*H+12+p*(48*H*H+152*H+66)+3)+2 ∧
      Exec body (countedLoop count (reciprocalUpdate p r)) (mk v S) t (mk z F) ∧
      F.R count = [] ∧ F.R (r 0) = binSyms H (Ring.inverse x).val ∧
      F.L = S.L ∧ F.inp = S.inp ∧ F.out = S.out ∧
      ∀ i, i ≠ r 0 → i ≠ count → F.R i = S.R i := by
  let Inv (i : ℕ) (D : Stacks T A) := D.R (r 0) = binSyms H (pivotReciprocal p x i).val ∧
    D.L = S.L ∧ D.inp = S.inp ∧ D.out = S.out ∧ ∀ j, j ≠ r 0 → j ≠ count → D.R j = S.R j
  rw [← pivotReciprocal_eq hp w x hx]
  apply countedLoop_exec (body := body) count _ w _ Inv _ _ v S ticks
    ⟨acc,rfl,rfl,rfl,fun _ _ _ => rfl⟩
  · rintro i D xs ⟨ha,hl,hin,hout,fr⟩
    exact ⟨by simpa [Function.update_of_ne (outside 0)] using ha,hl,hin,hout,
      fun j h h' => (Function.update_of_ne h' _ _).trans (fr j h h')⟩
  · rintro i _ u D ⟨ha,hl,hin,hout,fr⟩
    have keep (j : Fin 14) (hj : j ≠ 0) := fr (r j) (r.injective.ne hj) (outside j)
    obtain ⟨z,t,hu,ht,step⟩ := reciprocalUpdate_exec body p r H hm _ _ u D ha
      ((keep 1 (by decide)).trans factor) ((keep 4 (by decide)).trans modulus)
      (fun j hlo h4 hhi => (keep j (by omega)).trans (free j hlo h4 hhi))
    have eqn : (pivotReciprocal p x i)^p * x^(p-1) = pivotReciprocal p x (i+1) := by
      have split (a : ZMod (p^(w+1))) : a^p = a^(p-1)*a := by
        exact (congrArg (fun n : ℕ => a^n) (show p = (p-1)+1 by have := hp.two_le; omega)).trans (pow_succ _ _)
      rw [pivotReciprocal,mul_pow,split]
      ac_rfl
    refine ⟨z,_,t,hu,ht,step,Function.update_of_ne (outside 0).symm _ _,?_,hl,hin,hout,?_⟩
    · simp [eqn]
    · exact fun j h h' => (Function.update_of_ne h _ _).trans (fr j h h')

end IntegerMultBounds.MathlibTM2.Cover.Fallback
