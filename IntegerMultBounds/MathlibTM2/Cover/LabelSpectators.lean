module

public import IntegerMultBounds.MathlibTM2.Cover.LabelQuotient
public import IntegerMultBounds.MathlibTM2.Cover.LabelPayload

/-! Count the records, then remove the matrix-label radix to count spectator prefixes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.LabelSpectators
noncomputable section
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
open Host Node Mult.ShortConv LabelMask
open RecursiveInterchangeLayout (Descriptor)
variable {T Q A : ℕ} {P U : Type}

def countRecords (beforeRows rows beforeH tmp dst t₁ t₂ : Fin T) : Pr P T Q A U :=
  .seq (unaryProduct beforeRows rows tmp t₁ t₂)
    (.seq (unaryProduct tmp beforeH dst t₁ t₂) (uclear tmp))

theorem records_exec (body : P → Pr P T Q A U) (beforeRows rows beforeH tmp dst t₁ t₂ : Fin T)
    (hr : [beforeRows,rows,beforeH,tmp,dst,t₁,t₂].Nodup) (v : Descriptor) (hp : v.Positive)
    (u : HS T Q A U) (S : Stacks T A) (ha : (S.R beforeRows).length = v.beforeRows)
    (hb : (S.R rows).length = v.rows) (hh : (S.R beforeH).length = v.beforeH)
    (hf : ∀ k ∈ [tmp,dst,t₁,t₂], S.R k = []) :
    ∃ z c, z.user = u.user ∧ c ≤ 28*records v+10 ∧
      Exec body (countRecords beforeRows rows beforeH tmp dst t₁ t₂) (mk u S) c
        (mk z {S with R := Function.update S.R dst (List.replicate (records v) tick)}) := by
  regs_ne hr
  let n := v.beforeRows*v.rows
  let M : Stacks T A := {S with R := Function.update S.R tmp (List.replicate n tick)}
  obtain ⟨v₁,c₁,hu₁,hc₁,he₁⟩ := unaryProduct_exec (body := body)
    (a := beforeRows) (b := rows) (dst := tmp) (t₁ := t₁) (t₂ := t₂) (by simp_all)
    u S (hf _ (by simp)) (hf _ (by simp))
  simp only [ha,hb,hf tmp (by simp),List.append_nil] at he₁ hc₁
  obtain ⟨v₂,c₂,hu₂,hc₂,he₂⟩ := unaryProduct_exec (body := body)
    (a := tmp) (b := beforeH) (dst := dst) (t₁ := t₁) (t₂ := t₂) (by simp_all [ne_comm])
    v₁ M (by simp [M,ne_comm, *, hf t₁ (by simp)]) (by simp [M,ne_comm, *, hf t₂ (by simp)])
  have hlen : (M.R tmp).length = n := by simp [M]
  have hprod : (M.R tmp).length*(M.R beforeH).length = records v := by
    simp [M,‹beforeH ≠ tmp›,hh,n,records]
  have hd : M.R dst = [] := by simp [M,ne_comm, *, hf dst (by simp)]
  simp only [hprod,hd,List.append_nil] at he₂
  let N : Stacks T A := {M with R := Function.update M.R dst (List.replicate (records v) tick)}
  obtain ⟨z,hu₃,he₃⟩ := uclear_exec body tmp v₂ N
  have hclear : (N.R tmp).length = n := by simp [N,‹tmp ≠ dst›,hlen]
  have hrst : Function.update N.R tmp [] = Function.update S.R dst (List.replicate (records v) tick) := by
    dsimp [N]
    rw [Function.update_comm (Ne.symm ‹tmp ≠ dst›)]
    simp [M,← hf tmp (by simp)]
  refine ⟨z,c₁+(c₂+(2*(N.R tmp).length+2)),hu₃.trans (hu₂.trans hu₁),?_,?_⟩
  · simp only [hlen,M,Function.update_of_ne ‹beforeH ≠ tmp›,hh] at hc₂
    rw [hclear]
    have h₁ := Nat.le_mul_of_pos_right v.beforeRows hp.2.1
    have h₂ := Nat.le_mul_of_pos_right n hp.2.2.1
    dsimp [records,n] at *
    nlinarith only [hc₁,hc₂,h₁,h₂]
  · apply Exec.seq he₁
    apply Exec.seq he₂
    simpa only [hrst] using he₃

def program (m : ℕ) (beforeRows rows beforeH width tmp dst t₁ t₂ : Fin T) : Pr P T Q A U :=
  .seq (countRecords beforeRows rows beforeH tmp dst t₁ t₂)
    (scanP width tmp (LabelQuotient.divide (prime^(m*m)) dst t₁ t₂))

theorem runs (body : P → Pr P T Q A U) (m : ℕ) (hm : 0 < m)
    (beforeRows rows beforeH width tmp dst t₁ t₂ : Fin T)
    (hr : [beforeRows,rows,beforeH,width,tmp,dst,t₁,t₂].Nodup) (v : Descriptor) (hp : v.Positive)
    (w B : ℕ) (hv : v.beforeH = B*prime^(m*(w*m))) (u : HS T Q A U) (S : Stacks T A)
    (ha : (S.R beforeRows).length = v.beforeRows) (hb : (S.R rows).length = v.rows)
    (hh : (S.R beforeH).length = v.beforeH) (hw : (S.R width).length = w)
    (hf : ∀ k ∈ [tmp,dst,t₁,t₂], S.R k = []) :
    ∃ z c, z.user = u.user ∧ c ≤ 44*records v+13*w+14 ∧
      Exec body (program m beforeRows rows beforeH width tmp dst t₁ t₂) (mk u S) c
        (mk z {S with R := Function.update S.R dst (List.replicate (v.beforeRows*v.rows*B) tick)}) := by
  regs_ne hr
  obtain ⟨v₁,c₁,hu₁,hc₁,he₁⟩ := records_exec body beforeRows rows beforeH tmp dst t₁ t₂
    (by simp_all) v hp u S ha hb hh hf
  let M : Stacks T A := {S with R := Function.update S.R dst (List.replicate (records v) tick)}
  have hq := Nat.one_lt_pow (Nat.mul_pos hm hm).ne' prime_prime.one_lt
  have hf' (k) (hk : k ∈ [tmp,t₁,t₂]) : M.R k = [] := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl <;> simp [M,ne_comm, *, hf k (by simp)]
  obtain ⟨z,c₂,hu₂,hc₂,he₂⟩ := LabelQuotient.strip_exec body hq
    (width := width) (dst := dst) (scratch := tmp) (tmp := t₁) (saved := t₂) (by simp_all [ne_comm])
    v₁ M (records v) (Function.update_self ..) hf'
  have hw' : (M.R width).length = w := by simp [M,‹width ≠ dst›,hw]
  have hpow : (prime^(m*m))^w = prime^(m*(w*m)) := by rw [← pow_mul]; congr 1; ring
  have hdiv : records v / (prime^(m*m))^w = v.beforeRows*v.rows*B := by
    rw [records,hv,hpow,← Nat.mul_assoc,Nat.mul_div_cancel _ (pow_pos prime_prime.pos _)]
  rw [hw',hdiv] at he₂
  rw [hw'] at hc₂
  exact ⟨z,c₁+c₂,hu₂.trans hu₁,by omega,Exec.seq he₁ (by simpa only [M,Function.update_idem] using he₂)⟩

end
end IntegerMultBounds.MathlibTM2.Cover.LabelSpectators
