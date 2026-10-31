module

public import IntegerMultBounds.MathlibTM2.Host.ForeignStock
public import IntegerMultBounds.MathlibTM2.Host.RegisterBankStock

/-! Machine head intervals supply the host simulation's stack invariant. A
caller proves bounds on machine configurations; representation and blank-stack
bookkeeping are handled here once. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U : Type}

/-- Stack storage is contained in the inclusive tape interval `[lo,hi]`. -/
def StackSpan (lo hi : Fin T → ℤ) (c : Config T Q A) (S : Stacks T A) : Prop :=
  ∀ i, ((S.L i).length : ℤ) ≤ c.head i-lo i ∧
    ((S.R i).length : ℤ) ≤ hi i+1-c.head i

theorem StackSpan.step {lo hi : Fin T → ℤ} {M : Program T Q A}
    {c c' : Config T Q A} {S : Stacks T A}
    {st' : Fin Q} {act : Fin T → Fin (A+4) × Move}
    (h : StackSpan lo hi c S)
    (hc : ∀ i, lo i ≤ c.head i ∧ c.head i ≤ hi i)
    (hc' : ∀ i, lo i ≤ c'.head i ∧ c'.head i ≤ hi i)
    (ht : M.transition c.state (fun i => c.tape i (c.head i)) = some (st',act))
    (hs : step M c = some c') :
    StackSpan lo hi c' {S with L := newL S act,R := newR S act} := by
  have he : c'.head = fun i => c.head i+(act i).2.offset := by
    simp only [Machine.step,ht,Option.some.injEq] at hs
    exact congrArg Config.head hs.symm
  intro i
  rw [he] at hc' ⊢
  exact stepStacks_interval _ _ _ _ _ _ _ (hc i) (hc' i) (h i).1 (h i).2

theorem StackSpan.stock {lo hi : Fin T → ℤ} {c : Config T Q A} {S : Stacks T A}
    (h : StackSpan lo hi c S) (v : HS T Q A U) :
    mnSize (mk v S) ≤ S.inp.length+S.out.length+∑ i, (hi i+1-lo i).toNat := by
  have hs : registerBankStock S ≤ ∑ i, (hi i+1-lo i).toNat := by
    apply Finset.sum_le_sum
    intro i _
    have hL := (h i).1
    have hR := (h i).2
    omega
  rw [mnSize_mk_registerBankStock]
  omega

/-- A preserved machine invariant and fixed head intervals yield a complete
host stock trace. No stack execution certificate is required from the caller. -/
theorem foreign_exec_within_head_bounds (M : Program T Q A) (body : P → Pr P T Q A U)
    {pre post : TapePred T A} {k : ℕ} (h : HoareTime M pre post k)
    (I : Config T Q A → Prop) (lo hi : Fin T → ℤ)
    (hheads : ∀ c, I c → ∀ i, lo i ≤ c.head i ∧ c.head i ≤ hi i)
    (hpreserve : ∀ c c', I c → step M c = some c' → I c')
    (v : HS T Q A U) (S : Stacks T A) (w : Tapes T A) (hw : pre w)
    (hrep : RepT w S.L S.R) (hI : I (w.start M))
    (hspan : StackSpan lo hi (w.start M) S) (depth : ℕ) :
    ∃ v' S' w', post w' ∧ RepT w' S'.L S'.R ∧ v'.user = v.user ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧
      ∃ m ≤ k*(T+5)+6,
        ExecWithin body (fun d z => mnSize z+d ≤
          S.inp.length+S.out.length+(∑ i, (hi i+1-lo i).toNat)+depth+2*(T+4)) depth
          (foreign M) (mk v S) m (mk v' S') := by
  let J := fun c F => I c ∧ F.inp = S.inp ∧ F.out = S.out ∧ StackSpan lo hi c F
  apply foreign_exec_within M body h J _ depth _ _ v S w hw hrep
  · exact ⟨hI,rfl,rfl,hspan⟩
  · intro c F hf vf
    simpa only [hf.2.1,hf.2.2.1] using hf.2.2.2.stock vf
  · intro c F st' act hf ht c' hs
    have hi' := hpreserve c c' hf.1 hs
    exact ⟨hi',hf.2.1,hf.2.2.1,hf.2.2.2.step (hheads c hf.1) (hheads c' hi') ht hs⟩

end IntegerMultBounds.MathlibTM2.Host
