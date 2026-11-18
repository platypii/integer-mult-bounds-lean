module

public import IntegerMultBounds.MathlibTM2.Host.BinArithDiv
public import IntegerMultBounds.MathlibTM2.Routing.BinaryCanonicalExec

/-! The translation descriptor for one control fiber of a modular row addition. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host Routing
variable {T Q A : ℕ} {P U : Type}

/-- Multiply the tape coefficient by the control digit, reduce, and trim the result. -/
def offsetProgram (r : Fin 13 → Fin T) : Pr P T Q A U :=
  .seq (bmodmul (r 0) (r 1) (r 2) (r 3) (r 4) (r 5) (r 6) (r 7)
    (r 8) (r 9) (r 10) (r 11) (r 12)) (binaryCanonicalProgram (r 3) (r 4))

theorem offset_exec (body : P → Pr P T Q A U) (r : Fin 13 → Fin T)
    (hr : Function.Injective r) (L c x M : ℕ) (hc : c < M) (hx : x < M)
    (hM : M < 2 ^ L) (v : HS T Q A U) (S : Stacks T A)
    (hcoef : S.R (r 0) = binSyms L c) (hdigit : S.R (r 1) = binSyms L x)
    (hmod : S.R (r 2) = binSyms L M)
    (hblank : ∀ i : Fin 13, 3 ≤ i → i < 12 → S.R (r i) = []) :
    ∃ bs v' n, GrowingCounterData.Canonical bs ∧ Counter.value bs = c*x % M ∧
      v'.user = v.user ∧ n ≤ 48*L*L + 154*L + 70 ∧
      Exec body (offsetProgram r) (mk v S) n
        (mk v' { S with R := Function.update S.R (r 3) (bs.map bitSymbol) }) := by
  have hM0 : 0 < M := Nat.zero_lt_of_lt hx
  obtain ⟨v₁, n, hu₁, hn, he₁⟩ := bmodmul_exec body
    (p := r 4) (qq := r 5) (s := r 6) (rr := r 7) (t := r 8)
    (tx := r 9) (ty := r 10) (tz := r 11) (cy := r 12) (c := r 3)
    (by simp [List.nodup_cons, hr.eq_iff]) (hr.ne (by decide)) (hr.ne (by decide))
    (hr.ne (by decide)) (hc.trans hM) (hx.trans hM) hM hM0 v S hcoef hdigit hmod
    (hblank _ (by decide) (by decide)) (hblank _ (by decide) (by decide))
    (hblank _ (by decide) (by decide)) (hblank _ (by decide) (by decide))
    (hblank _ (by decide) (by decide)) (hblank _ (by decide) (by decide))
    (hblank _ (by decide) (by decide)) (hblank _ (by decide) (by decide))
  rw [hblank 3 (by decide) (by decide), List.append_nil] at he₁
  let S₁ : Stacks T A := { S with R := Function.update S.R (r 3) (binSyms L (c*x % M)) }
  obtain ⟨bs, v₂, hb, hv, _, hu₂, he₂⟩ := binaryCanonical_exec body (r 3) (r 4)
    (hr.ne (by decide)) L (c*x % M) ((Nat.mod_lt _ hM0).trans hM) v₁ S₁ (by simp [S₁])
    (by simp [S₁, hr.eq_iff, hblank 4 (by decide) (by decide)])
  refine ⟨bs, v₂, n + (4*L+6), hb, hv, hu₂.trans hu₁, ?_, ?_⟩
  · nlinarith only [hn]
  · simpa [S₁, offsetProgram, Function.update_self] using Exec.seq he₁ he₂

end IntegerMultBounds.MathlibTM2.Cover.Fallback
