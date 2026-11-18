module

public import IntegerMultBounds.MathlibTM2.Host.BinArithDiv
public import Mathlib.Data.ZMod.Basic

/-! Fixed powers of a live residue, with every intermediate reduced to the input width. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
variable {T Q A M : ℕ} [NeZero M] {P U : Type}

def modularPower (r : Fin 14 ↪ Fin T) : ℕ → Pr P T Q A U
  | 0 => bcopy (r 1) (r 2) (r 5) (r 6)
  | n+1 => .seq (modularPower ((Equiv.swap 2 3).toEmbedding.trans r) n)
      (.seq (bmodmul (r 0) (r 3) (r 4) (r 2) (r 5) (r 6) (r 7) (r 8)
        (r 9) (r 10) (r 11) (r 12) (r 13)) (bclear (r 3)))

theorem modularPower_exec (body : P → Pr P T Q A U) (n : ℕ) (r : Fin 14 ↪ Fin T)
    (H : ℕ) (hm : M < 2^H) (x b : ZMod M) (v : HS T Q A U) (S : Stacks T A)
    (base : S.R (r 0) = binSyms H x.val) (seed : S.R (r 1) = binSyms H b.val)
    (modulus : S.R (r 4) = binSyms H M)
    (free : ∀ i : Fin 14, 2 ≤ i → i ≠ 4 → i < 13 → S.R (r i) = []) :
    ∃ z t, z.user = v.user ∧ t ≤ 6*H+6+n*(48*H*H+152*H+66) ∧
      Exec body (modularPower r n) (mk v S) t
        (mk z {S with R := Function.update S.R (r 2) (binSyms H (x^n*b).val)}) := by
  induction n generalizing r v S with
  | zero =>
    obtain ⟨z,hu,he⟩ := bcopy_exec body (a := r 1) (c := r 2) (t₁ := r 5) (t₂ := r 6)
      (by simp [List.nodup_cons,r.injective.eq_iff]) v S (free 5 (by decide) (by decide) (by decide))
      (free 6 (by decide) (by decide) (by decide))
    rw [seed,free 2 (by decide) (by decide) (by decide),List.append_nil,length_binSyms] at he
    exact ⟨z,6*H+6,hu,by simp,by simpa [modularPower] using he⟩
  | succ n ih =>
    let swap := (Equiv.swap (2 : Fin 14) 3).toEmbedding
    have range : ∀ i : Fin 14, 2 ≤ i → i ≠ 4 → i < 13 →
        2 ≤ swap i ∧ swap i ≠ 4 ∧ swap i < 13 := by decide
    obtain ⟨u,t,hu,ht,rec⟩ := ih (swap.trans r) v S base seed modulus
      (fun i hi hj hk => free _ (range i hi hj hk).1 (range i hi hj hk).2.1 (range i hi hj hk).2.2)
    let D : Stacks T A := {S with R := Function.update S.R (r 3) (binSyms H (x^n*b).val)}
    have keep (i : Fin 14) (hi : i ≠ 3) : D.R (r i) = S.R (r i) :=
      Function.update_of_ne (r.injective.ne hi) _ _
    have blank (i : Fin 14) (lo : 5 ≤ i) (hi : i < 13) := (keep i (by omega)).trans
      (free i (by omega) (by omega) hi)
    obtain ⟨z,m,hz,hn,mul⟩ := bmodmul_exec body (a := r 0) (b := r 3) (m := r 4) (c := r 2)
      (p := r 5) (qq := r 6) (s := r 7) (rr := r 8) (t := r 9) (tx := r 10) (ty := r 11)
      (tz := r 12) (cy := r 13) (by simp [List.nodup_cons,r.injective.eq_iff])
      (r.injective.ne (by decide)) (r.injective.ne (by decide)) (r.injective.ne (by decide))
      (x.val_lt.trans hm) ((x^n*b).val_lt.trans hm) hm (NeZero.pos M) u D ((keep 0 (by decide)).trans base)
      (by simp [D]) ((keep 4 (by decide)).trans modulus) (blank _ (by decide) (by decide))
      (blank _ (by decide) (by decide)) (blank _ (by decide) (by decide)) (blank _ (by decide) (by decide))
      (blank _ (by decide) (by decide)) (blank _ (by decide) (by decide)) (blank _ (by decide) (by decide))
      (blank _ (by decide) (by decide))
    rw [(keep 2 (by decide)).trans (free 2 (by decide) (by decide) (by decide)),List.append_nil,
      ← ZMod.val_mul,← mul_assoc,← pow_succ'] at mul
    let E : Stacks T A := {D with R := Function.update D.R (r 2) (binSyms H (x^(n+1)*b).val)}
    obtain ⟨z',hu',_,clear⟩ := bclear_exec body (r 3) z E
    have len : (E.R (r 3)).length = H := by simp [E,D,r.injective.eq_iff,length_binSyms]
    have final : Function.update E.R (r 3) [] = Function.update S.R (r 2) (binSyms H (x^(n+1)*b).val) := by
      funext j
      by_cases h : j = r 2 <;> by_cases h' : j = r 3 <;>
        simp_all [E,D,r.injective.eq_iff]
    rw [len,final] at clear
    exact ⟨z',t+(m+(2*H+2)),hu'.trans (hz.trans hu),by nlinarith only [hn,ht],
      Exec.seq rec (Exec.seq mul clear)⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
