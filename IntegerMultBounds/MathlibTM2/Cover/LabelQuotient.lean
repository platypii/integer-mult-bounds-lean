module

public import IntegerMultBounds.MathlibTM2.Cover.LabelCounts

/-! Strip the radix of a label column from a unary dimension. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.LabelQuotient
noncomputable section
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open Host Node
variable {T Q A : ℕ} {P U : Type}

def divide (q : ℕ) (dst tmp saved : Fin T) : Pr P T Q A U :=
  .seq (moveR dst tmp id) (.seq (udiv q tmp dst saved) (uclear tmp))

theorem divide_exec (body : P → Pr P T Q A U) {q : ℕ} (hq : 0 < q) {dst tmp saved : Fin T}
    (hr : [dst,tmp,saved].Nodup) (u : HS T Q A U) (S : Stacks T A)
    (ht : S.R tmp = []) (hs : S.R saved = []) :
    ∃ v n, v.user = u.user ∧ n ≤ 8*(S.R dst).length+8 ∧
      Exec body (divide q dst tmp saved) (mk u S) n
        (mk v {S with R := Function.update S.R dst (List.replicate ((S.R dst).length/q) tick)}) := by
  regs_ne hr
  let M : Stacks T A := {S with R := movedR S.R dst tmp id (S.R dst)}
  obtain ⟨v₁,hu₁,he₁⟩ := moveR_exec body dst tmp ‹dst ≠ tmp› id u S
  obtain ⟨v₂,n,hu₂,hn,he₂⟩ := udiv_exec body hq (Ne.symm ‹dst ≠ tmp›) ‹tmp ≠ saved› ‹dst ≠ saved› v₁ M
    (by simp [M,movedR,ne_comm, *])
  let N : Stacks T A := {M with R := Function.update M.R dst (List.replicate ((M.R tmp).length/q) tick ++ M.R dst)}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec body tmp v₂ N
  have hm : (M.R tmp).length = (S.R dst).length := by simp [M,movedR,ht]
  have hN : (N.R tmp).length = (S.R dst).length := by simp [N,Ne.symm ‹dst ≠ tmp›,hm]
  refine ⟨v₃, _, hu₃.trans (hu₂.trans hu₁), ?_, (Exec.seq he₁ (Exec.seq he₂ he₃)).cast rfl ?_⟩
  · rw [hN]; omega
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h : k = dst
    · subst k; simp [N,M,movedR,ht,‹dst ≠ tmp›]
    by_cases h' : k = tmp
    · subst k; simp [N,h,ht]
    · simp [N,M,movedR,h,h']

theorem strip_exec (body : P → Pr P T Q A U) {q : ℕ} (hq : 2 ≤ q)
    {width dst scratch tmp saved : Fin T} (hr : [width,dst,scratch,tmp,saved].Nodup)
    (u : HS T Q A U) (S : Stacks T A) (N : ℕ) (hd : S.R dst = List.replicate N tick)
    (hf : ∀ k ∈ [scratch,tmp,saved], S.R k = []) :
    let w := (S.R width).length
    ∃ v c, v.user = u.user ∧ c ≤ 16*N+13*w+4 ∧
      Exec body (scanP width scratch (divide q dst tmp saved)) (mk u S) c
        (mk v {S with R := Function.update S.R dst (List.replicate (N/q^w) tick)}) := by
  regs_ne hr
  let a (i : ℕ) := N/q^i
  have step (i : ℕ) : a (i+1) = a i / q := by simp [a,pow_succ,Nat.div_div_eq_div_mul]
  let R (i : ℕ) := Function.update S.R dst (List.replicate (a i) tick)
  have it : IterSpec body (divide q dst tmp saved) width scratch R (fun i => 8*a i+8) (S.R width).length := by
    intro i _ v M hM
    have hdst := hM dst (Ne.symm ‹width ≠ dst›) ‹dst ≠ scratch›
    simp only [R,Function.update_self] at hdst
    obtain ⟨z,c,hu,hc,he⟩ := divide_exec body (q := q) (by omega) (dst := dst) (tmp := tmp)
      (saved := saved) (by simp_all) v M (by rw [hM tmp (Ne.symm ‹width ≠ tmp›) (Ne.symm ‹scratch ≠ tmp›)]; simp [R,ne_comm, *, hf tmp (by simp)])
      (by rw [hM saved (Ne.symm ‹width ≠ saved›) (Ne.symm ‹scratch ≠ saved›)]; simp [R,ne_comm, *, hf saved (by simp)])
    refine ⟨z,_,c,hu,by simpa [hdst] using hc,he,Function.update_of_ne ‹width ≠ dst› ..,
      Function.update_of_ne (Ne.symm ‹dst ≠ scratch›) ..,?_⟩
    intro k hk hs
    by_cases h : k = dst
    · subst k; simp [R,step,hdst]
    · simp [R,h,hM k hk hs]
  obtain ⟨z,M,c,hu,hc,he,hw,hs,hM⟩ := scanP_exec body ‹width ≠ scratch› it 0 u S (by simp)
    (fun k _ _ => by simp [R,a,← hd])
  have bound (w : ℕ) : (∑ i ∈ Finset.range w, (8*a i+11)) + 16*a w ≤ 16*N+11*w := by
    induction w with
    | zero => simp [a]
    | succ w ih =>
      rw [Finset.sum_range_succ,step]
      have h := Nat.div_mul_le_self (a w) q
      have := Nat.mul_le_mul_left (a w / q) hq
      omega
  refine ⟨z,c,hu,?_,he.cast rfl ?_⟩
  · simp only [Nat.zero_add,hf scratch (by simp),List.length_nil,Nat.mul_zero,Nat.add_zero,
      Nat.add_assoc, Nat.reduceAdd] at hc
    have := bound (S.R width).length
    omega
  · apply congrArg (mk z)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h : k = width
    · subst k; simpa [hf scratch (by simp),‹width ≠ dst›] using hw
    by_cases h' : k = scratch
    · subst k; simp [hs,Ne.symm ‹dst ≠ scratch›,hf scratch (by simp)]
    · simpa [R,a] using hM k h h'

open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
open RecursiveInterchangeLayout (Descriptor)

/-- Removing the matrix-label radix from the before-header leaves its spectator factor. -/
theorem before_exec (body : P → Pr P T Q A U) (v : Descriptor) (m w B : ℕ)
    (hm : 0 < m) (hv : v.beforeH = B*prime^(m*(w*m)))
    {width dst scratch tmp saved : Fin T} (hr : [width,dst,scratch,tmp,saved].Nodup)
    (u : HS T Q A U) (S : Stacks T A) (hw : (S.R width).length = w)
    (hd : S.R dst = List.replicate v.beforeH tick)
    (hf : ∀ k ∈ [scratch,tmp,saved], S.R k = []) :
    ∃ z c, z.user = u.user ∧ c ≤ 16*v.beforeH+13*w+4 ∧
      Exec body (scanP width scratch (divide (prime^(m*m)) dst tmp saved)) (mk u S) c
        (mk z {S with R := Function.update S.R dst (List.replicate B tick)}) := by
  have hq := Nat.one_lt_pow (Nat.mul_pos hm hm).ne' prime_prime.one_lt
  have hx : (prime^(m*m))^w = prime^(m*(w*m)) := by rw [← pow_mul]; congr 1; ring
  obtain ⟨z,c,hu,hc,he⟩ := strip_exec body hq hr u S _ hd hf
  rw [hw,hx,hv,Nat.mul_div_cancel _ (pow_pos prime_prime.pos _)] at he
  exact ⟨z,c,hu,hw ▸ hc,he⟩

end
end IntegerMultBounds.MathlibTM2.Cover.LabelQuotient
