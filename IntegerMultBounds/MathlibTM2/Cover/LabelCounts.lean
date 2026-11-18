module

public import IntegerMultBounds.MathlibTM2.Cover.LabelTraversal

/-! Unary powers for the selector high-part count and the payload radix. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.LabelCounts
noncomputable section
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
open Host Node

private theorem exp_eq (q s e : ℕ) : expSeq 0 q s e = q^e*s :=
  (eq_expSeq (e := fun i => q^i*s) (by simp) (fun i => by simp [pow_succ', Nat.mul_assoc]) e).symm

private theorem power_cost (q s : ℕ) (hq : 2 ≤ q) (hs : 0 < s) (e : ℕ) :
    4*s + 2*e + 8 + ∑ i ∈ Finset.range e, (8*(q^i*s)+12) ≤ 22*(q^e*s) := by
  induction e with
  | zero => simp; omega
  | succ e ih =>
    rw [Finset.sum_range_succ, pow_succ']
    have h := Nat.mul_le_mul_right (q^e*s) hq
    have hp := Nat.mul_pos (pow_pos (by omega : 0 < q) e) hs
    nlinarith only [ih,h,hp]

theorem scale_power_exec {T Q A : ℕ} {P U : Type} (body : P → Pr P T Q A U)
    (q : ℕ) (hq : 2 ≤ q) {seed exponent dst t₁ t₂ t₃ : Fin T}
    (hr : [seed,exponent,dst,t₁,t₂,t₃].Nodup)
    (u : HS T Q A U) (S : Stacks T A) (hs : 0 < (S.R seed).length)
    (hf : ∀ k ∈ [dst,t₁,t₂,t₃], S.R k = []) :
    let n := q^(S.R exponent).length*(S.R seed).length
    ∃ u' c, u'.user = u.user ∧ c ≤ 22*n ∧ Exec body (expProg 0 q seed exponent dst t₁ t₂ t₃)
      (mk u S) c (mk u' {S with R := Function.update S.R dst (List.replicate n tick)}) := by
  obtain ⟨v,c,hu,hc,he⟩ := expProg_exec body 0 q hr u S (hf _ (by simp)) (hf _ (by simp))
    (hf _ (by simp)) (hf _ (by simp))
  simp only [exp_eq] at he hc
  exact ⟨v,c,hu,hc.trans (power_cost q _ hq hs _),he⟩

theorem power_exec {T Q A : ℕ} {P U : Type} (body : P → Pr P T Q A U)
    {one exponent dst t₁ t₂ t₃ : Fin T} (hr : [one,exponent,dst,t₁,t₂,t₃].Nodup)
    (u : HS T Q A U) (S : Stacks T A) (h1 : (S.R one).length = 1)
    (hf : ∀ k ∈ [dst,t₁,t₂,t₃], S.R k = []) :
    let n := prime^(S.R exponent).length
    ∃ u' c, u'.user = u.user ∧ c ≤ 22*n ∧ Exec body (expProg 0 prime one exponent dst t₁ t₂ t₃)
      (mk u S) c (mk u' {S with R := Function.update S.R dst (List.replicate n tick)}) := by
  simpa only [h1, Nat.mul_one] using
    scale_power_exec body prime prime_prime.two_le hr u S (by omega) hf

/-- Drop the low digit before exponentiation and restore the width word afterwards. -/
def highCount {T Q A : ℕ} {P U : Type} (one width dst t₁ t₂ t₃ : Fin T) : Pr P T Q A U :=
  .seq (.act (dropTop width .done)) (.seq (expProg 0 prime one width dst t₁ t₂ t₃)
    (.act (.push (.rt width) (fun _ => tick) .done)))

theorem high_exec {T Q A : ℕ} {P U : Type} (body : P → Pr P T Q A U)
    {one width dst t₁ t₂ t₃ : Fin T} (hr : [one,width,dst,t₁,t₂,t₃].Nodup)
    (u : HS T Q A U) (S : Stacks T A) (w : ℕ) (hw : 0 < w)
    (hwidth : S.R width = List.replicate w tick) (h1 : (S.R one).length = 1)
    (hf : ∀ k ∈ [dst,t₁,t₂,t₃], S.R k = []) :
    ∃ u' c, u'.user = u.user ∧ c ≤ 22*prime^(w-1)+2 ∧ Exec body (highCount one width dst t₁ t₂ t₃)
      (mk u S) c (mk u' {S with R := Function.update S.R dst (List.replicate (prime^(w-1)) tick)}) := by
  obtain ⟨e,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hw.ne'
  have hregs := hr
  regs_ne hregs
  let S₁ : Stacks T A := {S with R := Function.update S.R width (List.replicate e tick)}
  have hpop := Exec.act (body := body) (dropTop width .done) (mk u S)
  have hpop' : Exec body (.act (dropTop width .done)) (mk u S) 1 (mk u S₁) := by
    simpa [S₁,dropTop,Action.run,hwidth,List.replicate_succ,update_rt] using hpop
  have fresh (k) (hk : k ∈ [dst,t₁,t₂,t₃]) : S₁.R k = [] := by
    have hne : k ≠ width := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> exact Ne.symm (by assumption)
    simpa [S₁,hne] using hf k hk
  obtain ⟨v,c,hu,hc,he⟩ := power_exec body hr u S₁ (by simpa [S₁,‹one ≠ width›] using h1) fresh
  let S₂ : Stacks T A := {S₁ with R := Function.update S₁.R dst (List.replicate (prime^e) tick)}
  have push := Exec.act (body := body) (.push (.rt width) (fun _ => tick) .done) (mk v S₂)
  simp only [S₁, Function.update_self, List.length_replicate] at he hc
  refine ⟨v, 1+(c+1), hu, by simp only [Nat.succ_sub_one]; omega, ?_⟩
  apply Exec.seq hpop'
  apply Exec.seq he
  have restore : Function.update (Function.update S.R dst (List.replicate (prime^e) tick)) width (S.R width) = Function.update S.R dst (List.replicate (prime^e) tick) := by
    rw [Function.update_comm (Ne.symm ‹width ≠ dst›), Function.update_eq_self]
  simpa [restore,S₂,S₁,Action.run,update_rt,Function.update_comm ‹width ≠ dst›,‹width ≠ dst›,
    ← List.replicate_succ, ← hwidth] using push

end
end IntegerMultBounds.MathlibTM2.Cover.LabelCounts
