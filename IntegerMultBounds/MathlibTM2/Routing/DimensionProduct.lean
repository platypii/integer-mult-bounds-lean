module

public import IntegerMultBounds.MathlibTM2.Routing.DimensionProductStep
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedLoop

/-! One fixed counted loop computes a product from binary dimension metadata.
The queue advances exactly once per factor and every step restores its scratch. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.DimensionProduct
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A : ℕ} {J U : Type} {body : J → Pr J T Q A U}

def run (r : Fin 11 → Fin T) (count : Fin T) : Pr J T Q A U := countedLoop count (DimensionProductStep.run r)

def cost (V a : ℕ) (xs : List ℕ) := xs.length*(31*(a*xs.prod)+19*V+39)+2

theorem step_bound (V a x M : ℕ) (ha : 0 < a) (hx : 0 < x) (hm : a*x ≤ M) :
    DimensionProductStep.cost V a x ≤ 31*M+19*V+36 := by
  have hax := Nat.le_mul_of_pos_right a hx
  have hxa := Nat.le_mul_of_pos_left x ha
  dsimp only [DimensionProductStep.cost]
  omega

theorem run_exec (r : Fin 11 → Fin T) (hr : Function.Injective r) (count : Fin T)
    (hc : ∀ j, count ≠ r j) (V a : ℕ) (ha : 0 < a) (xs : List ℕ)
    (hpos : ∀ x ∈ xs, 0 < x) (hfit : ∀ x ∈ xs, x < 2^V)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hV : (S.R (r 0)).length = V) (hz : S.R (r 1) = [])
    (hacc : S.R (r 3) = List.replicate a tick) (hcount : (S.R count).length = xs.length)
    (hqueue : S.R (r 2) = xs.flatMap (binSyms V)++tail)
    (hf : ∀ j ∈ [(4 : Fin 11),5,6,7,8,9,10], S.R (r j) = []) :
    ∃ vf n, vf.user = v.user ∧ n ≤ cost V a xs ∧
      Exec body (run r count) (mk v S) n
        (mk vf {S with R := (Function.update (Function.update (Function.update S.R
          (r 2) tail) (r 3) (List.replicate (a*xs.prod) tick)) count [])}) := by
  let Inv (j : ℕ) (F : Stacks T A) : Prop :=
    F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
    (∀ t, t ≠ r 2 → t ≠ r 3 → t ≠ count → F.R t = S.R t) ∧
    F.R (r 2) = (xs.drop j).flatMap (binSyms V)++tail ∧
    F.R (r 3) = List.replicate (a*(xs.take j).prod) tick
  have hstable : ∀ j F clock, Inv j F → Inv j {F with R := Function.update F.R count clock} := by
    intro j F clock h
    rcases h with ⟨hin,hout,hleft,hframe,hq,hh⟩
    exact ⟨hin,hout,hleft,fun t ht2 ht3 htc => by simpa [htc] using hframe t ht2 ht3 htc,
      by simpa [(hc 2).symm] using hq,by simpa [(hc 3).symm] using hh⟩
  have hstep : ∀ j < xs.length, ∀ (vi : HS T Q A U) F, Inv j F →
      ∃ vf G n, vf.user = vi.user ∧ n ≤ 31*(a*xs.prod)+19*V+36 ∧
        Exec body (DimensionProductStep.run r) (mk vi F) n (mk vf G) ∧
        G.R count = F.R count ∧ Inv (j+1) G := by
    intro j hj vi F hI
    rcases hI with ⟨hin,hout,hleft,hframe,hq,hh⟩
    have keep (t : Fin 11) (h2 : t ≠ 2) (h3 : t ≠ 3) : F.R (r t) = S.R (r t) :=
      hframe _ (hr.ne h2) (hr.ne h3) (hc t).symm
    cases hd : xs.drop j with
    | nil => have he : (xs.drop j).length = xs.length-j := List.length_drop; rw [hd] at he; simp only [List.length_nil] at he; omega
    | cons x rest =>
      have hx : x ∈ xs := List.mem_of_mem_drop (by rw [hd]; simp)
      have hpref : 0 < (xs.take j).prod := List.prod_pos (fun y hy => hpos y (List.mem_of_mem_take hy))
      have hrest : 0 < rest.prod := List.prod_pos (fun y hy => hpos y (List.mem_of_mem_drop (by rw [hd]; simp [hy])))
      have hprod : (xs.take j).prod*(x*rest.prod) = xs.prod := by
        rw [←List.prod_cons,←hd,←List.prod_append,List.take_append_drop]
      have hbound : (a*(xs.take j).prod)*x ≤ a*xs.prod := by
        have hb := Nat.le_mul_of_pos_right ((a*(xs.take j).prod)*x) hrest
        calc
          _ ≤ ((a*(xs.take j).prod)*x)*rest.prod := hb
          _ = _ := by rw [Nat.mul_assoc,Nat.mul_assoc,hprod]
      obtain ⟨vf,n,hu,hn,he⟩ := DimensionProductStep.run_exec (body := body) r hr V
        (a*(xs.take j).prod) x (hfit x hx) (rest.flatMap (binSyms V)++tail) vi F
        (by rw [keep 0 (by decide) (by decide)]; exact hV)
        (by rw [keep 1 (by decide) (by decide)]; exact hz) (by simp [hh])
        (by simpa [hd,List.flatMap_cons,List.append_assoc] using hq)
        (fun t ht => by
          have h2 : t ≠ 2 := by intro he; subst t; simp at ht
          have h3 : t ≠ 3 := by intro he; subst t; simp at ht
          rw [keep t h2 h3]; exact hf t ht)
      have hd' : xs.drop (j+1) = rest := by
        simpa [List.drop_drop,Nat.add_comm] using congrArg (List.drop 1) hd
      have ht' : xs.take (j+1) = xs.take j++[x] := by rw [List.take_add,hd]; simp
      refine ⟨vf,DimensionProductStep.result r F (a*(xs.take j).prod) x (rest.flatMap (binSyms V)++tail),n,
        hu,hn.trans (step_bound V _ x _ (Nat.mul_pos ha hpref) (hpos x hx) hbound),he,?_,?_⟩
      · simp [DimensionProductStep.result,hc]
      · refine ⟨hin,hout,hleft,?_,?_,?_⟩
        · intro t ht2 ht3 htc
          simpa [DimensionProductStep.result,ht2,ht3] using hframe t ht2 ht3 htc
        · simp [DimensionProductStep.result,hr.eq_iff,hd']
        · simp [DimensionProductStep.result,ht',List.prod_append,Nat.mul_assoc]
  obtain ⟨vf,F,n,hu,hn,he,hclock,hI⟩ := countedLoop_exec (body := body) count (DimensionProductStep.run r)
    xs.length (31*(a*xs.prod)+19*V+36) Inv hstable hstep v S hcount
    ⟨rfl,rfl,rfl,fun _ _ _ _ => rfl,by simpa using hqueue,by simpa using hacc⟩
  rcases hI with ⟨hin,hout,hleft,hframe,hq,hh⟩
  have hfinal : F = {S with R := (Function.update (Function.update (Function.update S.R
      (r 2) tail) (r 3) (List.replicate (a*xs.prod) tick)) count [])} := by
    refine Stacks.ext hin hout hleft ?_
    funext t
    by_cases ht : t = count
    · subst t; simp [hclock]
    by_cases ht2 : t = r 2
    · subst t; simpa [ht,hr.eq_iff] using hq
    by_cases ht3 : t = r 3
    · subst t; simpa [ht] using hh
    · simp [ht,ht2,ht3,hframe t ht2 ht3 ht]
  refine ⟨vf,n,hu,?_,he.cast rfl (congrArg (mk vf) hfinal)⟩
  dsimp only [cost]; omega

theorem run_native (r : Fin 11 → Fin T) (count : Fin T) :
    mnNativePushBound 3 (run (J := J) (Q := Q) (A := A) (U := U) r count) := by
  simp only [run,countedLoop,countedLoopBody,mnNativePushBound]
  exact ⟨by simp [peekR,mnActPush],by simp [mnActPush],DimensionProductStep.run_native r,
    by simp [peekR,mnActPush]⟩

end IntegerMultBounds.MathlibTM2.Routing.DimensionProduct
