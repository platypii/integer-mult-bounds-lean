module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Structural straight-line unary setup, with exact frames and charged arithmetic. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.UnarySetup

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

inductive Op (T : ℕ)
  | add (c : ℕ) (a dst tmp : Fin T)
  | div (c : ℕ) (a dst tmp : Fin T)
  | mul (a b dst saved tmp : Fin T)
  | push (dst : Fin T) (c : ℕ)
  | clear (dst : Fin T)

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def Op.program : Op T → Pr P T Q A U
  | .add c a dst tmp => umul c a dst tmp
  | .div c a dst tmp => udiv c a dst tmp
  | .mul a b dst saved tmp => unaryProduct a b dst saved tmp
  | .push dst c => .act (pushN dst (fun _ => tick) c .done)
  | .clear dst => uclear dst

def Op.runR (op : Op T) (R : Regs T A) : Regs T A :=
  match op with
  | .add c a dst _ => Function.update R dst (List.replicate (c*(R a).length) tick++R dst)
  | .div c a dst _ => Function.update R dst (List.replicate ((R a).length/c) tick++R dst)
  | .mul a b dst _ _ => Function.update R dst (List.replicate ((R a).length*(R b).length) tick++R dst)
  | .push dst c => Function.update R dst (List.replicate c tick++R dst)
  | .clear dst => Function.update R dst []

def Op.dst : Op T → Fin T
  | .add _ _ dst _ => dst
  | .div _ _ dst _ => dst
  | .mul _ _ dst _ _ => dst
  | .push dst _ => dst
  | .clear dst => dst

theorem Op.runR_off (op : Op T) (R : Regs T A) (i : Fin T) (hi : i ≠ op.dst) :
    op.runR R i = R i := by
  cases op <;> exact Function.update_of_ne hi _ _

def Op.cost (op : Op T) (R : Regs T A) : ℕ :=
  match op with
  | .add _ a _ _ => 4*(R a).length+4
  | .div _ a _ _ => 4*(R a).length+4
  | .mul a b _ _ _ => (R a).length*(4*(R b).length+9)+4
  | .push _ _ => 1
  | .clear dst => 2*(R dst).length+2

def Op.Ready (op : Op T) (R : Regs T A) : Prop :=
  match op with
  | .add _ a dst tmp => [a,dst,tmp].Nodup ∧ R tmp = []
  | .div c a dst tmp => 1 ≤ c ∧ [a,dst,tmp].Nodup ∧ R tmp = []
  | .mul a b dst saved tmp => [a,b,dst,saved,tmp].Nodup ∧ R saved = [] ∧ R tmp = []
  | .push _ _ => True
  | .clear _ => True

theorem Op.exec (op : Op T) (v : HS T Q A U) (S : Stacks T A) (h : op.Ready S.R) :
    ∃ v' n, v'.user = v.user ∧ n ≤ op.cost S.R ∧
      Exec body op.program (mk v S) n (mk v' {S with R := op.runR S.R}) := by
  cases op with
  | add c a dst tmp =>
    have hnd := h.1
    regs_ne hnd
    obtain ⟨v',hu,he⟩ := umul_exec body c ‹a ≠ dst› ‹a ≠ tmp› ‹dst ≠ tmp› v S h.2
    exact ⟨v',_,hu,le_rfl,he⟩
  | div c a dst tmp =>
    have hnd := h.2.1
    regs_ne hnd
    obtain ⟨v',n,hu,hn,he⟩ := udiv_exec (body := body) h.1 ‹a ≠ dst› ‹a ≠ tmp› ‹dst ≠ tmp› v S h.2.2
    exact ⟨v',n,hu,hn,he⟩
  | mul a b dst saved tmp =>
    obtain ⟨v',n,hu,hn,he⟩ := unaryProduct_exec (body := body) h.1 v S h.2.1 h.2.2
    exact ⟨v',n,hu,hn,he⟩
  | push dst c =>
    have he := Exec.act (body := body) (pushN dst (fun _ => tick) c .done) (mk v S)
    refine ⟨v,1,rfl,le_rfl,he.cast rfl ?_⟩
    rw [pushN_run]
    simp [Action.run,Op.runR]
  | clear dst =>
    obtain ⟨v',hu,he⟩ := uclear_exec body dst v S
    exact ⟨v',_,hu,le_rfl,he⟩

def program : List (Op T) → Pr P T Q A U
  | [] => .act .done
  | op::ops => .seq op.program (program ops)

def runR : List (Op T) → Regs T A → Regs T A
  | [],R => R
  | op::ops,R => runR ops (op.runR R)

theorem runR_off (ops : List (Op T)) (R : Regs T A) (i : Fin T)
    (hi : ∀ op ∈ ops, i ≠ op.dst) : runR ops R i = R i := by
  induction ops generalizing R with
  | nil => rfl
  | cons op ops ih =>
    rw [runR,ih _ (fun x hx => hi x (by simp [hx]))]
    exact op.runR_off R i (hi op (by simp))

def cost : List (Op T) → Regs T A → ℕ
  | [],_ => 1
  | op::ops,R => op.cost R+cost ops (op.runR R)

def Ready : List (Op T) → Regs T A → Prop
  | [],_ => True
  | op::ops,R => op.Ready R ∧ Ready ops (op.runR R)

theorem exec (ops : List (Op T)) (v : HS T Q A U) (S : Stacks T A) (h : Ready ops S.R) :
    ∃ v' n, v'.user = v.user ∧ n ≤ cost ops S.R ∧
      Exec body (program ops) (mk v S) n (mk v' {S with R := runR ops S.R}) := by
  induction ops generalizing v S with
  | nil =>
    exact ⟨v,1,rfl,le_rfl,by simpa [program,runR,Action.run] using Exec.act (body := body) .done (mk v S)⟩
  | cons op ops ih =>
    obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := op.exec (body := body) v S h.1
    obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := ih v₁ {S with R := op.runR S.R} h.2
    exact ⟨v₂,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,Exec.seq he₁ he₂⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.UnarySetup
