module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackColumn

/-! Execute a pivot itinerary, retaining successive packed matrices on alternating stacks. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
variable {T Q A d : ℕ} {P U : Type}

def stageBank (r : Fin 23 ↪ Fin T) : ℕ → Fin 23 ↪ Fin T
  | 0 => r
  | n+1 => (Equiv.swap 15 16).toEmbedding.trans (stageBank r n)

theorem stageBank_fixed (r : Fin 23 ↪ Fin T) (n : ℕ) (i : Fin 23) (h : i ≠ 15) (h' : i ≠ 16) :
    stageBank r n i = r i := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [stageBank,Equiv.swap_apply_of_ne_of_ne h h'] using ih

def itineraryProgram (p : ℕ) (pivot : Fin d → Fin d) (r : Fin 23 ↪ Fin T) : ℕ → Pr P T Q A U
  | 0 => .act .done
  | n+1 => if h : n < d then .seq (itineraryProgram p pivot r n)
      (itineraryColumn p ⟨n,h⟩ (pivot ⟨n,h⟩) (stageBank r n)) else itineraryProgram p pivot r n

theorem itineraryProgram_exec (body : P → Pr P T Q A U) (r : Fin 23 ↪ Fin T) (p w H : ℕ) (hp : p.Prime)
    [NeZero (p^(w+1))] (m : Matrix (Fin d) (Fin d) (ZMod (p^(w+1)))) (pivot : Fin d → Fin d)
    (hm : p^(w+1) < 2^H) (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A+4)))
    (matrix : S.R (r 15) = matrixWords A H m ++ tail) (modulus : S.R (r 2) = binSyms H (p^(w+1)))
    (one : S.R (r 20) = binSyms H (1 : ZMod (p^(w+1))).val) (ticks : (S.R (r 22)).length = w)
    (free : ∀ i : Fin 23, (i < 15 ∧ i ≠ 2) ∨ (17 ≤ i ∧ i ≤ 19) ∨ i = 21 → S.R (r i) = [])
    (n : ℕ) (hn : n ≤ d) (valid : Itinerary.Valid pivot m n) :
    ∃ z F l suffix, z.user = v.user ∧ l ≤ n*(4*w+4+columnTime d p w H)+1 ∧
      Exec body (itineraryProgram p pivot r n) (mk v S) l (mk z F) ∧
      F.R (stageBank r n 15) = matrixWords A H (Itinerary.run pivot m n) ++ suffix ∧
      F.L = S.L ∧ F.inp = S.inp ∧ F.out = S.out ∧
      ∀ i, i ≠ stageBank r n 15 → i ≠ stageBank r n 16 → F.R i = S.R i := by
  induction n with
  | zero => exact ⟨v,S,1,tail,rfl,by simp,Exec.act (body := body) .done _,matrix,rfl,rfl,rfl,fun _ _ _ => rfl⟩
  | succ n ih =>
    have h : n < d := hn
    let k : Fin d := ⟨n,h⟩
    let b := stageBank r n
    obtain ⟨prev,unit⟩ := (Itinerary.valid_succ pivot m n).mp valid
    obtain ⟨u,D,l,suffix,hu,hl,run,packed,hL,hin,hout,frame⟩ := ih h.le prev
    have keep (i : Fin 23) (hi : i ≠ 15) (hj : i ≠ 16) : D.R (b i) = S.R (r i) :=
      (frame _ (b.injective.ne hi) (b.injective.ne hj)).trans (congrArg S.R (stageBank_fixed r n i hi hj))
    obtain ⟨z,t,hz,ht,col⟩ := itineraryColumn_exec body b p w H hp (Itinerary.run pivot m n) k (pivot k)
      (unit h).2 hm u D suffix packed ((keep 2 (by decide) (by decide)).trans modulus)
      ((keep 20 (by decide) (by decide)).trans one) (by rw [keep 22 (by decide) (by decide),ticks])
      (fun i hi => (keep i (by omega) (by omega)).trans (free i hi))
    have next := (clearColumn_eq p w hp k (pivot k) (Itinerary.run pivot m n) (unit h).2).trans
      (Itinerary.run_succ pivot m n h).symm
    rw [next] at col
    have src : stageBank r (n+1) 15 = b 16 := by simp [stageBank,b]
    have dst : stageBank r (n+1) 16 = b 15 := by simp [stageBank,b]
    refine ⟨z,{D with R := Function.update D.R (b 16) (matrixWords A H (Itinerary.run pivot m (n+1)) ++ D.R (b 16))},l+t,D.R (b 16),hz.trans hu,?_,?_,?_,hL,hin,hout,?_⟩
    · rw [Nat.succ_mul]; omega
    · simpa only [itineraryProgram,dite_eq_left h] using Exec.seq run col
    · simp [src]
    · intro i hi hj
      rw [src] at hi
      rw [dst] at hj
      exact (Function.update_of_ne hi _ _).trans (frame _ hj hi)

/-- The full machine run outputs the diagonal normal form of the original matrix. -/
theorem diagonalize_exec (body : P → Pr P T Q A U) (r : Fin 23 ↪ Fin T) (p w H : ℕ) (hp : p.Prime)
    [NeZero (p^(w+1))] (m : Matrix (Fin d) (Fin d) (ZMod (p^(w+1)))) (pivot : Fin d → Fin d)
    (hm : p^(w+1) < 2^H) (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A+4)))
    (matrix : S.R (r 15) = matrixWords A H m ++ tail) (modulus : S.R (r 2) = binSyms H (p^(w+1)))
    (one : S.R (r 20) = binSyms H (1 : ZMod (p^(w+1))).val) (ticks : (S.R (r 22)).length = w)
    (free : ∀ i : Fin 23, (i < 15 ∧ i ≠ 2) ∨ (17 ≤ i ∧ i ≤ 19) ∨ i = 21 → S.R (r i) = [])
    (valid : Itinerary.Valid pivot m d) :
    ∃ z F l suffix E a, z.user = v.user ∧ l ≤ d*(4*w+4+columnTime d p w H)+1 ∧
      Exec body (itineraryProgram p pivot r d) (mk v S) l (mk z F) ∧
      F.R (stageBank r d 15) = matrixWords A H (Matrix.diagonal a) ++ suffix ∧
      Elim (d*(d-1)) d E ∧ E*m = Matrix.diagonal a ∧ ∀ i, IsUnit (a i) := by
  obtain ⟨z,F,l,suffix,hz,hl,run,packed,_⟩ := itineraryProgram_exec body r p w H hp m pivot hm v S tail
    matrix modulus one ticks free d le_rfl valid
  obtain ⟨E,elim,product,cleared,units⟩ := Itinerary.run_spec pivot m d le_rfl valid
  let a := fun i => Itinerary.run pivot m d i i
  have diagonal : Itinerary.run pivot m d = Matrix.diagonal a := by
    ext i j
    by_cases h : i = j
    · subst j; simp [a]
    · rw [Matrix.diagonal_apply_ne _ h]; exact cleared i j j.isLt h
  exact ⟨z,F,l,suffix,E,a,hz,hl,run,diagonal ▸ packed,elim,product.trans diagonal,fun i => units i i.isLt⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
