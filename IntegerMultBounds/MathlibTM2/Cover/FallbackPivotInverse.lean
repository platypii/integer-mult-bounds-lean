module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackReciprocalLoop

/-! Compute a unit pivot's reciprocal directly from its fixed-width binary word. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open Mult.PhaseCellToeplitz (countedLoop)
variable {T Q A : ℕ} {P U : Type}

def initialPowerPorts : Fin 14 ↪ Fin 16 := ⟨![14,15,0,3,4,5,6,7,8,9,10,11,12,13],by decide⟩
def factorPorts : Fin 14 ↪ Fin 16 := ⟨![14,0,1,3,4,5,6,7,8,9,10,11,12,13],by decide⟩
def iterationPorts : Fin 14 ↪ Fin 16 := Fin.castLEEmb (by decide)

def pivotInverse (p : ℕ) (r : Fin 16 ↪ Fin T) (count : Fin T) : Pr P T Q A U :=
  .seq (modularPower (initialPowerPorts.trans r) (p-2))
    (.seq (modularPower (factorPorts.trans r) 1)
      (.seq (countedLoop count (reciprocalUpdate p (iterationPorts.trans r))) (bclear (r 1))))

theorem pivotInverse_exec (body : P → Pr P T Q A U) (p w : ℕ) (hp : p.Prime)
    [NeZero (p^(w+1))] (x : ZMod (p^(w+1))) (hx : IsUnit x) (r : Fin 16 ↪ Fin T)
    (count : Fin T) (outside : ∀ i, r i ≠ count) (H : ℕ) (hm : p^(w+1) < 2^H)
    (v : HS T Q A U) (S : Stacks T A) (ticks : (S.R count).length = w)
    (pivot : S.R (r 14) = binSyms H x.val)
    (one : S.R (r 15) = binSyms H (1 : ZMod (p^(w+1))).val)
    (modulus : S.R (r 4) = binSyms H (p^(w+1)))
    (free : ∀ i : Fin 16, i ≠ 4 → i < 13 → S.R (r i) = []) :
    let C := 48*H*H+152*H+66
    ∃ z F t, z.user = v.user ∧ t ≤ 14*H+16+(p-2)*C+C+w*(12*H+15+p*C) ∧
      Exec body (pivotInverse p r count) (mk v S) t (mk z F) ∧
      F.R count = [] ∧ F.R (r 0) = binSyms H (Ring.inverse x).val ∧
      F.L = S.L ∧ F.inp = S.inp ∧ F.out = S.out ∧
      ∀ i, i ≠ r 0 → i ≠ count → F.R i = S.R i := by
  have ini : ∀ i : Fin 14, 2 ≤ i → i ≠ 4 → i < 13 →
      initialPowerPorts i ≠ 4 ∧ initialPowerPorts i < 13 := by decide
  obtain ⟨u,n,hu,hn,start⟩ := modularPower_exec body (p-2) (initialPowerPorts.trans r) H hm x 1
    v S pivot one modulus (fun i hi hj hk => free _ (ini i hi hj hk).1 (ini i hi hj hk).2)
  simp only [mul_one] at start
  let D : Stacks T A := {S with R := Function.update S.R (r 0) (binSyms H (x^(p-2)).val)}
  have keep (i : Fin 16) (hi : i ≠ 0) : D.R (r i) = S.R (r i) :=
    Function.update_of_ne (r.injective.ne hi) _ _
  have fac : ∀ i : Fin 14, 2 ≤ i → i ≠ 4 → i < 13 →
      factorPorts i ≠ 0 ∧ factorPorts i ≠ 4 ∧ factorPorts i < 13 := by decide
  obtain ⟨u',m,hu',hm',factor⟩ := modularPower_exec body 1 (factorPorts.trans r) H hm x (x^(p-2))
    u D ((keep 14 (by decide)).trans pivot) (by change D.R (r 0) = _; simp [D])
    ((keep 4 (by decide)).trans modulus)
    (fun i hi hj hk => (keep _ (fac i hi hj hk).1).trans (free _ (fac i hi hj hk).2.1 (fac i hi hj hk).2.2))
  rw [pow_one,← pow_succ',show p-2+1 = p-1 by have := hp.two_le; omega] at factor
  let E : Stacks T A := {D with R := Function.update D.R (r 1) (binSyms H (x^(p-1)).val)}
  have kept (i : Fin 16) (hi : i ≠ 0) (hj : i ≠ 1) : E.R (r i) = S.R (r i) :=
    (Function.update_of_ne (r.injective.ne hj) _ _).trans (keep i hi)
  have it : ∀ i : Fin 14, 2 ≤ i → i ≠ 4 → i < 13 →
      iterationPorts i ≠ 0 ∧ iterationPorts i ≠ 1 ∧ iterationPorts i ≠ 4 ∧ iterationPorts i < 13 := by decide
  obtain ⟨z,F,l,hz,hl,loop,empty,acc,left,hin,hout,frame⟩ := reciprocalLoop_exec body p w hp x hx
    (iterationPorts.trans r) count (fun i => outside _) H hm u' E
    (by simpa [E,D,Function.update_of_ne (outside 0).symm,Function.update_of_ne (outside 1).symm] using ticks)
    (by change E.R (r 0) = _; simp [E,D,r.injective.eq_iff]) (by change E.R (r 1) = _; simp [E])
    ((kept 4 (by decide) (by decide)).trans modulus)
    (fun i hi hj hk => (kept _ (it i hi hj hk).1 (it i hi hj hk).2.1).trans
      (free _ (it i hi hj hk).2.2.1 (it i hi hj hk).2.2.2))
  have factorWord := frame (r 1) (r.injective.ne (by decide)) (outside 1)
  obtain ⟨z',hz',_,clear⟩ := bclear_exec body (r 1) z F
  have len : (F.R (r 1)).length = H := by simp [factorWord,E,length_binSyms]
  rw [len] at clear
  refine ⟨z',_,_,hz'.trans (hz.trans (hu'.trans hu)),?_,Exec.seq start (Exec.seq factor (Exec.seq loop clear)),
    ?_,?_,left,hin,hout,?_⟩
  · simp only [one_mul] at hm'
    rw [show 12*H+15+p*(48*H*H+152*H+66) = 12*H+12+p*(48*H*H+152*H+66)+3 by omega]
    omega
  · simpa [Function.update_of_ne (outside 1).symm] using empty
  · change Function.update F.R (r 1) [] (r 0) = _
    rw [Function.update_of_ne (r.injective.ne (by decide : (0 : Fin 16) ≠ 1))]
    exact acc
  · intro i hi hc
    by_cases h : i = r 1
    · subst i; simp [free 1 (by decide) (by decide)]
    · simpa [D,E,Function.update_of_ne h,Function.update_of_ne hi] using frame i hi hc

/-- Run the reciprocal loop on a copy so subsequent rows can reuse the clock. -/
def reusablePivotInverse (p : ℕ) (r : Fin 16 ↪ Fin T) (clock count : Fin T) : Pr P T Q A U :=
  .seq (bcopy clock count (r 2) (r 3)) (pivotInverse p r count)

theorem reusablePivotInverse_exec (body : P → Pr P T Q A U) (p w : ℕ) (hp : p.Prime)
    [NeZero (p^(w+1))] (x : ZMod (p^(w+1))) (hx : IsUnit x) (r : Fin 16 ↪ Fin T)
    (clock count : Fin T) (copyPorts : [clock, count, r 2, r 3].Nodup)
    (outside : ∀ i, r i ≠ count) (H : ℕ) (hm : p^(w+1) < 2^H)
    (v : HS T Q A U) (S : Stacks T A) (ticks : (S.R clock).length = w) (empty : S.R count = [])
    (pivot : S.R (r 14) = binSyms H x.val)
    (one : S.R (r 15) = binSyms H (1 : ZMod (p^(w+1))).val)
    (modulus : S.R (r 4) = binSyms H (p^(w+1)))
    (free : ∀ i : Fin 16, i ≠ 4 → i < 13 → S.R (r i) = []) :
    let C := 48*H*H+152*H+66
    ∃ z F t, z.user = v.user ∧ t ≤ 6*w+6+(14*H+16+(p-2)*C+C+w*(12*H+15+p*C)) ∧
      Exec body (reusablePivotInverse p r clock count) (mk v S) t (mk z F) ∧
      F.R count = [] ∧ F.R (r 0) = binSyms H (Ring.inverse x).val ∧
      F.L = S.L ∧ F.inp = S.inp ∧ F.out = S.out ∧
      ∀ i, i ≠ r 0 → F.R i = S.R i := by
  obtain ⟨u,hu,copy⟩ := bcopy_exec body copyPorts v S
    (free 2 (by decide) (by decide)) (free 3 (by decide) (by decide))
  rw [empty,List.append_nil,ticks] at copy
  let D : Stacks T A := {S with R := Function.update S.R count (S.R clock)}
  have keep (i : Fin 16) : D.R (r i) = S.R (r i) := Function.update_of_ne (outside i) _ _
  obtain ⟨z,F,n,hz,hn,run,cleared,result,left,inp,out,frame⟩ := pivotInverse_exec body p w hp x hx r count outside H hm u D
    (by simpa [D] using ticks) ((keep 14).trans pivot) ((keep 15).trans one) ((keep 4).trans modulus)
    (fun i hi hj => (keep i).trans (free i hi hj))
  refine ⟨z,F,_,hz.trans hu,Nat.add_le_add_left hn _,Exec.seq copy run,cleared,result,left,inp,out,?_⟩
  intro i hi
  by_cases eq : i = count
  · subst i; exact cleared.trans empty.symm
  · exact (frame i hi eq).trans (Function.update_of_ne eq _ _)

end IntegerMultBounds.MathlibTM2.Cover.Fallback
