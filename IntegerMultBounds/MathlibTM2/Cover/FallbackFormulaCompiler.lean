module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackFormulaGate

/-! Compile a fixed expression from input writers and one arithmetic bank per nesting level. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback.RingFormula
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host LabelTraversal Node
variable {ι : Type} {T Q A M : ℕ} [NeZero M] {P U : Type}

inductive Leaf (ι : Type)
  | input (i : ι)
  | zero
  | one

def Leaf.value (read : ι → ZMod M) : Leaf ι → ZMod M
  | .input i => read i
  | .zero => 0
  | .one => 1

/-- The two subtrees reuse the next level of arithmetic registers, with distinct destinations. -/
def compile (leaf : Leaf ι → Fin T → Pr P T Q A U) (bank : ℕ → Fin T → Fin 13 ↪ Fin T) : RingFormula ι → ℕ → Fin T → Pr P T Q A U
  | .input i, _, out => leaf (.input i) out
  | .zero, _, out => leaf .zero out
  | .one, _, out => leaf .one out
  | .sub x y, l, out => Gate.sub.combine (bank l out)
      (compile leaf bank x (l+1) (bank l out 0)) (compile leaf bank y (l+1) (bank l out 1))
  | .mul x y, l, out => Gate.mul.combine (bank l out)
      (compile leaf bank x (l+1) (bank l out 0)) (compile leaf bank y (l+1) (bank l out 1))

def time (H : ℕ) (cost : Leaf ι → ℕ) : RingFormula ι → ℕ
  | .input i => cost (.input i)
  | .zero => cost .zero
  | .one => cost .one
  | .sub x y => time H cost x + time H cost y + Gate.sub.time H + 4*H+5
  | .mul x y => time H cost x + time H cost y + Gate.mul.time H + 4*H+5

variable (bank : ℕ → Fin T → Fin 13 ↪ Fin T) (read : ι → ZMod M) (H : ℕ)
  (ready : Leaf ι → Fin T → Regs T A → Prop)

def operandsReady (x : RingFormula ι) (left right : ℕ → Fin T → Regs T A → Prop)
    (l : ℕ) (out : Fin T) (R : Regs T A) :=
  let r := bank l out
  r 3 = out ∧ R (r 2) = binSyms H M ∧ (∀ i : Fin 13, i ≠ 2 → i < 12 → R (r i) = []) ∧
    left (l+1) (r 0) R ∧ right (l+1) (r 1) (Function.update R (r 0) (binSyms H (eval read x).val))

def prepared : RingFormula ι → ℕ → Fin T → Regs T A → Prop
  | .input i, _, out => ready (.input i) out
  | .zero, _, out => ready .zero out
  | .one, _, out => ready .one out
  | .sub x y, l, out | .mul x y, l, out =>
    operandsReady bank read H x (prepared x) (prepared y) l out

theorem compile_writes (body : P → Pr P T Q A U) (hm : M < 2^H)
    (leaf : Leaf ι → Fin T → Pr P T Q A U)
    (cost : Leaf ι → ℕ) (emit : ∀ i out, Writes body (ready i out) out (leaf i out)
      (binSyms H (i.value read).val) (cost i)) (f : RingFormula ι) (l : ℕ) (out : Fin T) :
    Writes body (prepared bank read H ready f l out) out (compile leaf bank f l out)
      (binSyms H (eval read f).val) (time H cost f) := by
  induction f generalizing l out with
  | input i => exact emit (.input i) out
  | zero => exact emit .zero out
  | one => exact emit .one out
  | sub x y ix iy | mul x y ix iy =>
    intro v S ⟨dst,modulus,free,hx,hy⟩
    let r : Fin 13 ↪ Fin T := (bank l out)
    let pre := fun R : Regs T A => prepared bank read H ready x (l+1) (r 0) R ∧
      prepared bank read H ready y (l+1) (r 1) (Function.update R (r 0) (binSyms H (eval read x).val))
    have combine (op : Gate) := op.combine_writes body r H hm (eval read x) (eval read y) _ _ _ _ pre _
      (fun u D h => ix (l+1) (r 0) u D h.1) (iy (l+1) (r 1)) (fun _ h => h.2) v S ⟨⟨hx,hy⟩,modulus,free⟩
    first
    | simpa only [compile,eval,time,Gate.apply,r,dst] using combine .sub
    | simpa only [compile,eval,time,Gate.apply,r,dst] using combine .mul

end IntegerMultBounds.MathlibTM2.Cover.Fallback.RingFormula
