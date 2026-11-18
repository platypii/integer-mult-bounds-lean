module

public import IntegerMultBounds.MathlibTM2.Cover.LabelCounts
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Compute the unary payload width from its three descriptor fields. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.LabelPayload
noncomputable section
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
open Host Node Mult.ShortConv LabelTransport
open RecursiveInterchangeLayout (Descriptor)
variable {T Q A : ℕ} {P U : Type}

def program (between afterD width seed dst t₁ t₂ t₃ : Fin T) : Pr P T Q A U :=
  .seq (unaryProduct between afterD seed t₁ t₂)
    (.seq (expProg 0 (prime^2) seed width dst t₁ t₂ t₃) (uclear seed))

theorem runs (body : P → Pr P T Q A U) (between afterD width seed dst t₁ t₂ t₃ : Fin T)
    (hr : [between,afterD,width,seed,dst,t₁,t₂,t₃].Nodup) (v : Descriptor) (hp : v.Positive)
    (u : HS T Q A U) (S : Stacks T A) (hb : (S.R between).length = v.between)
    (ha : (S.R afterD).length = v.afterD) (hw : (S.R width).length = v.width)
    (hf : ∀ k ∈ [seed,dst,t₁,t₂,t₃], S.R k = []) :
    ∃ u' c, u'.user = u.user ∧ c ≤ 37*payload v+6 ∧
      Exec body (program between afterD width seed dst t₁ t₂ t₃) (mk u S) c
        (mk u' {S with R := Function.update S.R dst (List.replicate (payload v) tick)}) := by
  regs_ne hr
  let n := v.between*v.afterD
  let M : Stacks T A := {S with R := Function.update S.R seed (List.replicate n tick)}
  obtain ⟨u₁,c₁,hu₁,hc₁,he₁⟩ := unaryProduct_exec (body := body)
    (a := between) (b := afterD) (dst := seed) (t₁ := t₁) (t₂ := t₂) (by simp_all)
    u S (hf _ (by simp)) (hf _ (by simp))
  simp only [hb,ha,hf seed (by simp),List.append_nil] at he₁ hc₁
  have hq : 2 ≤ prime^2 := by nlinarith [prime_prime.two_le]
  have hn : 0 < n := Nat.mul_pos hp.2.2.2.1 hp.2.2.2.2
  have fresh (k) (hk : k ∈ [dst,t₁,t₂,t₃]) : M.R k = [] := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl <;> simp [M,ne_comm, *, hf k (by simp)]
  have hsize : (prime^2)^(M.R width).length*(M.R seed).length = payload v := by
    simp only [M, Function.update_of_ne ‹width ≠ seed›, hw, Function.update_self, List.length_replicate]
    simp [payload,n,mul_pow,pow_two]; ring
  obtain ⟨u₂,c₂,hu₂,hc₂,he₂⟩ := LabelCounts.scale_power_exec body _ hq
    (seed := seed) (exponent := width) (dst := dst) (t₁ := t₁) (t₂ := t₂) (t₃ := t₃)
    (by simp_all [ne_comm]) u₁ M (by simpa [M] using hn) fresh
  rw [hsize] at hc₂ he₂
  let N : Stacks T A := {M with R := Function.update M.R dst (List.replicate (payload v) tick)}
  obtain ⟨u₃,hu₃,he₃⟩ := uclear_exec body seed u₂ N
  have hs : (N.R seed).length = n := by simp [N,M,‹seed ≠ dst›]
  have hnp : n ≤ payload v := by
    have h := Nat.le_mul_of_pos_left n (pow_pos (by omega : 0 < prime^2) v.width)
    simpa [M,‹width ≠ seed›,hw,← hsize] using h
  have hrestore : Function.update (Function.update M.R dst (List.replicate (payload v) tick)) seed [] =
      Function.update S.R dst (List.replicate (payload v) tick) := by
    rw [Function.update_comm (Ne.symm ‹seed ≠ dst›)]
    simp [M, ← hf seed (by simp)]
  refine ⟨u₃, c₁+(c₂+(2*(N.R seed).length+2)), hu₃.trans (hu₂.trans hu₁), ?_, ?_⟩
  · rw [hs]
    have hb' := Nat.le_mul_of_pos_right v.between hp.2.2.2.2
    dsimp [n] at *
    nlinarith only [hb',hnp,hc₁,hc₂]
  · apply Exec.seq he₁
    apply Exec.seq he₂
    simpa only [N,hrestore] using he₃

end
end IntegerMultBounds.MathlibTM2.Cover.LabelPayload
