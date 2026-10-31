module

public import IntegerMultBounds.MathlibTM2.Host.Auto
public import IntegerMultBounds.MathlibTM2.StackResources

/-! Structural push certificates for arbitrary word automata. Input arity and
controller data never need case enumeration; each output pushes one symbol. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A ni no : ℕ} {P U : Type}

theorem autoStep_push (ins : Fin ni → Fin T) (outs : Fin no → Fin T) (st : Fin T) (M : Auto A ni no) :
    mnActPush (autoStep (Q := Q) (U := U) ins outs st M) = no := by
  have hpop : ∀ (xs : List (Fin ni)) (a : Act T Q A U),
      mnActPush (xs.foldr (popIn ins) a) = mnActPush a := by
    intro xs
    induction xs with
    | nil => intro a; rfl
    | cons i xs ih => intro a; simpa only [List.foldr_cons,popIn,mnActPush] using ih a
  have hpush : ∀ (xs : List (Fin no)) (a : Act T Q A U),
      mnActPush (xs.foldr (pushOut ins outs st M) a) = xs.length+mnActPush a := by
    intro xs
    induction xs with
    | nil => intro a; simp
    | cons j xs ih =>
      intro a
      simp only [List.foldr_cons,pushOut,mnActPush,ih,List.length_cons]
      omega
  simp only [autoStep,hpop,hpush,setAutoState,mnActPush,List.length_finRange,Nat.add_zero]

theorem autoWord_native (i0 : Fin ni) (ins : Fin ni → Fin T) (outs : Fin no → Fin T)
    (st ctr tmp : Fin T) (M : Auto A ni no) {c : ℕ} (hc : 1 ≤ c) (hno : no ≤ c) :
    mnNativePushBound c (autoWord (P := P) (Q := Q) (A := A) (U := U) i0 ins outs st ctr tmp M) := by
  simp [autoWord,autoInner,autoReset,autoStep_push,moveR,moveStep,whileR,peekR,
    mnNativePushBound,mnActPush,hc,hno]

theorem autoWords_native [NeZero ni] (ins : Fin ni → Fin T) (outs : Fin no → Fin T)
    (st ctr tmp : Fin T) (M : Auto A ni no) {c : ℕ} (hc : 1 ≤ c) (hno : no ≤ c) :
    mnNativePushBound c (autoWords (P := P) (Q := Q) (A := A) (U := U) ins outs st ctr tmp M) := by
  exact ⟨by simp [autoReset,peekR,mnNativePushBound,mnActPush],
    autoWord_native 0 ins outs st ctr tmp M hc hno⟩

end IntegerMultBounds.MathlibTM2.Host
