module

public import IntegerMultBounds.Machine.BinaryCompareBounds
public import IntegerMultBounds.MathlibTM2.Host.ForeignHeadStock

/-! Actual binary comparison with a length-based host workspace certificate. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast.Main
variable {A : ℕ} {P U : Type}

/-- The scanned operands and one result bit occupy fixed intervals. The host
workspace bound charges those intervals once, independently of comparison time. -/
theorem binaryCompare_exec_within (body : P → Pr P 3 4 A U)
    (xs ys : List Bool) (f g out : ℤ → Fin (A+4)) (p q r : ℤ)
    (hf : f (p+xs.length) = blank) (hg : g (q+ys.length) = blank)
    (v : HS 3 4 A U) (S : Stacks 3 A)
    (hrep : RepT (BinaryCompare.cfg (putWord f p (xs.map bitSymbol))
      (putWord g q (ys.map bitSymbol)) out p q r 0).tapes S.L S.R)
    (hspan : StackSpan ![p,q,r] ![p+xs.length,q+ys.length,r+1]
      (BinaryCompare.cfg (putWord f p (xs.map bitSymbol))
        (putWord g q (ys.map bitSymbol)) out p q r 0) S) (depth : ℕ) :
    ∃ v' S' w',
      w' = (BinaryCompare.cfg (putWord f p (xs.map bitSymbol))
        (putWord g q (ys.map bitSymbol)) (putWord out r (BinaryCompare.resultWord xs ys))
        (p+xs.length) (q+ys.length) (r+1) 0).tapes ∧
      RepT w' S'.L S'.R ∧ v'.user = v.user ∧ S'.inp = S.inp ∧ S'.out = S.out ∧
      ∃ m ≤ (BinaryCompare.width xs ys+1)*8+6,
        ExecWithin body (fun d z => mnSize z+d ≤
          S.inp.length+S.out.length+(xs.length+ys.length+4)+depth+14) depth
          (foreign (BinaryCompare.program A)) (mk v S) m (mk v' S') := by
  have hfl : putWord f p (xs.map bitSymbol) (p+xs.length) = blank := by
    rw [putWord_outside _ _ _ _ (Or.inr (by simp)),hf]
  have hgl : putWord g q (ys.map bitSymbol) (q+ys.length) = blank := by
    rw [putWord_outside _ _ _ _ (Or.inr (by simp)),hg]
  have hinit := BinaryCompare.HeadBounds.of_cfg (putWord f p (xs.map bitSymbol))
    (putWord g q (ys.map bitSymbol)) out p q r xs.length ys.length hfl hgl
  have he := foreign_exec_within_head_bounds (BinaryCompare.program A) body
    (BinaryCompare.compare_hoare xs ys f g out p q r hf hg)
    (BinaryCompare.HeadBounds p (p+xs.length) q (q+ys.length) r)
    ![p,q,r] ![p+xs.length,q+ys.length,r+1]
    (fun _ h => h.heads) (fun _ _ h hs => h.step hs) v S _ rfl hrep hinit hspan depth
  have hsum : (∑ i : Fin 3, ((![p+xs.length,q+ys.length,r+1] : Fin 3 → ℤ) i+1-
      (![p,q,r] : Fin 3 → ℤ) i).toNat) = xs.length+ys.length+4 := by
    simp [Fin.sum_univ_succ]
    omega
  simpa only [hsum] using he

end IntegerMultBounds.MathlibTM2.Host
