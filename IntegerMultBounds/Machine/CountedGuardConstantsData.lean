import IntegerMultBounds.Machine.CountedGuardGadgetRecord
import IntegerMultBounds.Compact.GuardValue

/-! Exact padded guard-constant bit patterns and the correctness of the one-cell
overwrite construction. The widths are retained even when high bits are zero. -/
namespace IntegerMultBounds.Machine.CountedGuardConstantsData
noncomputable section
variable {a : ℕ}
open IntegerMultBounds.Counter (value)
open IntegerMultBounds.Compact.PowerTwo (value_replicate_false)
open ColumnTransducer (value_append)
open CountedGuardGadgetRecord (word)

def c1 (q b : ℕ) := List.replicate (b+1) false ++ [true] ++ List.replicate (q-b-3) false
def c2 (q b : ℕ) := List.replicate (b+1) true ++ [false] ++ List.replicate (q-b-3) true
def c3 (b : ℕ) := false :: List.replicate (b-1) true

theorem lengths (q b : ℕ) (hb : 1 ≤ b) (hbq : b+3 ≤ q) :
    (c1 q b).length=q-1 ∧ (c2 q b).length=q-1 ∧ (c3 b).length=b := by
  simp only [c1,c2,c3,List.length_append,List.length_replicate,List.length_cons,List.length_nil]
  omega

theorem complement_value (xs : List Bool) : value xs+value (xs.map Bool.not)+1=2^xs.length := by
  induction xs with
  | nil => simp [value]
  | cons x xs ih => cases x <;> simp [value,List.map_cons,pow_succ] <;> omega

theorem values (q b : ℕ) (hb : 1 ≤ b) (hbq : b+3 ≤ q) :
    value (c1 q b)=2^(b+1) ∧ value (c2 q b)+2^(b+1)+1=2^(q-1) ∧ value (c3 b)+2=2^b := by
  have h1 : value (c1 q b)=2^(b+1) := by
    simp [c1,value_append,value_replicate_false,value]
  have hm : (c1 q b).map Bool.not=c2 q b := by simp [c1,c2,List.map_replicate]
  have h2 := complement_value (c1 q b)
  rw [hm,h1,(lengths q b hb hbq).1] at h2
  have ht := complement_value (List.replicate (b-1) false)
  simp only [List.map_replicate,Bool.not_false,value_replicate_false,zero_add,List.length_replicate] at ht
  have h3 : value (c3 b)+2=2^b := by
    simp only [c3,value,Bool.false_eq_true,ite_false,zero_add]
    calc
      2*value (List.replicate (b-1) true)+2=2*(value (List.replicate (b-1) true)+1) := by omega
      _=2*2^(b-1) := by rw [ht]
      _=2^b := by rw [← pow_succ']; congr 1; omega
  exact ⟨h1,by omega,h3⟩

theorem overwrite_word (f : ℤ → Fin (a+4)) (p : ℤ) (xs ys : List (Fin (a+4))) (x y : Fin (a+4)) :
    Function.update (putWord f p (xs++x::ys)) (p+xs.length) y=putWord f p (xs++y::ys) := by
  induction xs generalizing p with
  | nil => simp [putWord,Function.update_idem]
  | cons z xs ih =>
    simp only [List.cons_append,putWord,List.length_cons,Nat.cast_add,Nat.cast_one]
    rw [Function.update_comm (show p ≠ p+((xs.length : ℤ)+1) by omega)]
    rw [show p+((xs.length : ℤ)+1)=p+1+xs.length by omega,ih]

theorem overwrite_replicate (q b : ℕ) (hbq : b+3 ≤ q) (x y : Bool) :
    Function.update (word (a := a) (List.replicate (q-1) x)) (b+1 : ℕ) (bitSymbol y)=
      word (List.replicate (b+1) x++[y]++List.replicate (q-b-3) x) := by
  have h : q-1=(b+1)+1+(q-b-3) := by omega
  rw [h]
  rw [List.replicate_add ((b+1)+1) (q-b-3),List.replicate_add (b+1) 1,List.replicate_one]
  simp only [word,List.map_append,List.map_replicate,List.map_singleton]
  have ho := overwrite_word (a := a) (fun _ => blank) 0 (List.replicate (b+1) (bitSymbol x))
    (List.replicate (q-b-3) (bitSymbol x)) (bitSymbol x) (bitSymbol y)
  simpa only [List.length_replicate,zero_add,List.append_assoc,List.singleton_append] using ho

theorem overwrite_c3 (b : ℕ) (hb : 1 ≤ b) :
    Function.update (word (a := a) (List.replicate b true)) 0 (bitSymbol false)=word (c3 b) := by
  conv_lhs => rw [show b=(b-1)+1 by omega,List.replicate_succ]
  simp only [word,List.map_cons,c3,List.map_replicate,putWord,Function.update_idem]

end
end IntegerMultBounds.Machine.CountedGuardConstantsData
