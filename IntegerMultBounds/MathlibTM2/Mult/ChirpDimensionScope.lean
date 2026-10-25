module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpUnaryCopies
public import IntegerMultBounds.MathlibTM2.Fast.TableProg

/-! # Scope computed binary dimensions around their unary copies

Compute a finite bank once, copy selected values into counters, then restore the
binary bank. The execution proof is structural in the assignment list and works
for any table program satisfying the arithmetic and restoration contracts.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.TableVM

/-- All setup, conversions and restoration execute; only selected counters change. -/
theorem tblComputedUnaryCopies_exec {T Q A n W e : ℕ} {P U : Type}
    {body : P → Pr P T Q A U} {rg : TblR n → Fin T}
    (hrg : Function.Injective rg) (wl nl : List (Fin (A + 4)))
    (hwl : wl.length = W) (hnl : nl.length = e) (heW : e ≤ W)
    (setup cleanup : TblCode n) (st : TblSt n A) (τ : Fin n → ℕ) (K L : ℕ)
    (run : TblDo A W e setup st (fun z => z.val = τ ∧ z.acc = st.acc ∧
      ∀ i, z.val i < 2 ^ W) K)
    (restore : ∀ z : TblSt n A, z.val = τ →
      TblDo A W e cleanup z (fun u => u.val = st.val ∧ u.acc = z.acc) L)
    (hfit : ∀ i, st.val i < 2 ^ W)
    (ls : List (Fin n × Fin T)) (hout : ∀ p ∈ ls, ∀ r, rg r ≠ p.2)
    (v : HS T Q A U) (S : Stacks T A) (hS : tblHolds rg S (tblRho W wl nl st)) :
    ∃ v' k, v'.user = v.user ∧ k ≤ (K + L) * tblC W e + unaryCopiesCost W τ ls ∧
      Exec body (.seq (tblCompile rg setup)
        (.seq (tblUnaryCopies rg ls) (tblCompile rg cleanup))) (mk v S) k
        (mk v' { S with R := unaryCopiesR τ S.R ls }) := by
  classical
  obtain ⟨st₁, ⟨hv₁, ha₁, hfit₁⟩, hargs⟩ := run.host (body := body) hrg wl nl hwl hnl heW hfit
  obtain ⟨v₁, S₁, k₁, hu₁, hk₁, he₁, hb₁, hfr₁⟩ := hargs v S hS
  obtain ⟨v₂, k₂, hu₂, hk₂, he₂⟩ := tblUnaryCopies_exec (body := body) hrg wl nl st₁ hfit₁
    ls hout v₁ S₁ hb₁
  let S₂ : Stacks T A := { S₁ with R := unaryCopiesR st₁.val S₁.R ls }
  have hb₂ : tblHolds rg S₂ (tblRho W wl nl st₁) := by
    intro r
    change unaryCopiesR st₁.val S₁.R ls (rg r) = _
    rw [unaryCopiesR_off _ _ _ _ (fun p hp => (hout p hp r).symm)]
    exact hb₁ r
  obtain ⟨st₃, ⟨hv₃, ha₃⟩, hclear⟩ := (restore st₁ hv₁).host
    (body := body) hrg wl nl hwl hnl heW hfit₁
  have hst₃ : st₃ = st := by
    have ha : st₃.acc = st.acc := ha₃.trans ha₁
    cases st₃; cases st
    simp_all only
  subst st₃
  obtain ⟨v₃, S₃, k₃, hu₃, hk₃, he₃, hb₃, hfr₃⟩ := hclear v₂ S₂ hb₂
  rw [hv₁] at hk₂
  refine ⟨v₃, k₁ + (k₂ + k₃), hu₃.trans (hu₂.trans hu₁), ?_,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast rfl ?_⟩
  · rw [Nat.add_mul]
    omega
  · congr 1
    ext1
    · exact hfr₃.1.trans hfr₁.1
    · exact hfr₃.2.1.trans hfr₁.2.1
    · exact hfr₃.2.2.1.trans hfr₁.2.2.1
    funext k
    by_cases hbank : ∃ r, rg r = k
    · obtain ⟨r, rfl⟩ := hbank
      change S₃.R (rg r) = unaryCopiesR τ S.R ls (rg r)
      rw [unaryCopiesR_off _ _ _ _ (fun p hp => (hout p hp r).symm)]
      exact (hb₃ r).trans (hS r).symm
    · have hoff : ∀ r, rg r ≠ k := by simpa using hbank
      rw [hfr₃.2.2.2 k hoff]
      change unaryCopiesR st₁.val S₁.R ls k = _
      rw [unaryCopiesR_congr st₁.val τ S₁.R ls (fun p _ => congrFun hv₁ p.1)]
      exact unaryCopiesR_congr_base _ _ _ _ k
        (fun p hp => hfr₁.2.2.2 p.2 (hout p hp)) (hfr₁.2.2.2 k hoff)

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
