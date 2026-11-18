module

public import IntegerMultBounds.MathlibTM2.Host.BinArithMul

/-! Binary dimensions of a scheduled row shear, from a live modulus and suffix width. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
variable {T Q A : ℕ} {P U : Type}

/-- Accumulate n factors of the modulus on the seed, alternating two result registers. -/
def dimensionPower (r : Fin 10 ↪ Fin T) : ℕ → Pr P T Q A U
  | 0 => bcopy (r 1) (r 2) (r 4) (r 5)
  | n+1 => .seq (dimensionPower ((Equiv.swap 2 3).toEmbedding.trans r) n)
      (.seq (bmul (r 0) (r 3) (r 2) (r 4) (r 5) (r 6) (r 7) (r 8) (r 9)) (bclear (r 3)))

def dimensionTime (H W : ℕ) : ℕ → ℕ
  | 0 => 6*W+6
  | n+1 => let w := n*H+W
    dimensionTime H W n + H*(12*(H+w)+20)+16*(H+w)+2*w+26

theorem dimensionTime_le (H W n : ℕ) :
    dimensionTime H W n ≤ 6*W+6 + n*((12*H+18)*(n*H+W)+20*H+26) := by
  induction n with
  | zero => simp [dimensionTime]
  | succ n ih =>
    let cost (i : ℕ) := (12*H+18)*(i*H+W)+20*H+26
    have mono : cost n ≤ cost (n+1) := by
      dsimp [cost]
      gcongr; omega
    have bound := Nat.mul_le_mul_left n mono
    dsimp [cost] at bound
    rw [dimensionTime]
    nlinarith only [ih,bound]

theorem dimensionPower_exec (body : P → Pr P T Q A U) (n : ℕ) (r : Fin 10 ↪ Fin T)
    (H W M b : ℕ) (hm : M < 2^H) (hb : b < 2^W)
    (v : HS T Q A U) (S : Stacks T A) (base : S.R (r 0) = binSyms H M)
    (seed : S.R (r 1) = binSyms W b) (free : ∀ i : Fin 10, 2 ≤ i → i < 9 → S.R (r i) = []) :
    ∃ z t, z.user = v.user ∧ t ≤ dimensionTime H W n ∧
      Exec body (dimensionPower r n) (mk v S) t
        (mk z {S with R := Function.update S.R (r 2) (binSyms (n*H+W) (M^n*b))}) := by
  induction n generalizing r v S with
  | zero =>
    obtain ⟨z,hu,he⟩ := bcopy_exec body (a := r 1) (c := r 2) (t₁ := r 4) (t₂ := r 5)
      (by simp [List.nodup_cons,r.injective.eq_iff]) v S (free 4 (by decide) (by decide))
      (free 5 (by decide) (by decide))
    rw [seed,free 2 (by decide) (by decide),List.append_nil,length_binSyms] at he
    exact ⟨z,_,hu,le_rfl,by simpa [dimensionPower,dimensionTime] using he⟩
  | succ n ih =>
    let swap := (Equiv.swap (2 : Fin 10) 3).toEmbedding
    have range : ∀ i : Fin 10, 2 ≤ i → i < 9 → 2 ≤ swap i ∧ swap i < 9 := by decide
    obtain ⟨u,t,hu,ht,rec⟩ := ih (swap.trans r) v S base seed
      (fun i hi hj => free (swap i) (range i hi hj).1 (range i hi hj).2)
    let w := n*H+W
    let D : Stacks T A := {S with R := Function.update S.R (r 3) (binSyms w (M^n*b))}
    have bound : M^n*b < 2^w := by
      rw [show 2^w = (2^H)^n * 2^W by simp [w,pow_add,← pow_mul,Nat.mul_comm H n]]
      exact (Nat.mul_le_mul_right b (Nat.pow_le_pow_left hm.le n)).trans_lt
        (Nat.mul_lt_mul_of_pos_left hb (by positivity))
    have keep (i : Fin 10) (h : i ≠ 3) : D.R (r i) = S.R (r i) :=
      Function.update_of_ne (r.injective.ne h) _ _
    have blank (i : Fin 10) (h : i ≠ 3) (hi : 2 ≤ i) (hj : i < 9) := (keep i h).trans (free i hi hj)
    obtain ⟨z,m,hz,hmul,mul⟩ := bmul_exec body (a := r 0) (b := r 3) (c := r 2)
      (s := r 4) (t := r 5) (tx := r 6) (ty := r 7) (tz := r 8) (cy := r 9)
      (by simp [List.nodup_cons,r.injective.eq_iff]) (r.injective.ne (by decide)) (r.injective.ne (by decide))
      hm bound u D ((keep 0 (by decide)).trans base) (by simp [D])
      (blank 2 (by decide) (by decide) (by decide)) (blank 4 (by decide) (by decide) (by decide))
      (blank 5 (by decide) (by decide) (by decide)) (blank 6 (by decide) (by decide) (by decide))
      (blank 7 (by decide) (by decide) (by decide)) (blank 8 (by decide) (by decide) (by decide))
    let E : Stacks T A := {D with R := Function.update D.R (r 2) (binSyms (H+w) (M*(M^n*b)))}
    obtain ⟨z',h',_,clear⟩ := bclear_exec body (r 3) z E
    have len : (E.R (r 3)).length = w := by simp [E,D,r.injective.eq_iff,length_binSyms]
    have final : Function.update E.R (r 3) [] = Function.update S.R (r 2)
        (binSyms ((n+1)*H+W) (M^(n+1)*b)) := by
      funext j
      by_cases h : j = r 2 <;> by_cases h' : j = r 3 <;>
        simp_all [E,D,w,Nat.add_mul,pow_succ',Nat.mul_assoc,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]
    rw [len,final] at clear
    refine ⟨z',t+(m+(2*w+2)),h'.trans (hz.trans hu),?_,Exec.seq rec (Exec.seq mul clear)⟩
    unfold dimensionTime
    dsimp only [w] at *
    omega

end IntegerMultBounds.MathlibTM2.Cover.Fallback
