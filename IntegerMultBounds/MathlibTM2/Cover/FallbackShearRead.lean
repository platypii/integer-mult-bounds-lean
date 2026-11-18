module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackShear
public import IntegerMultBounds.MathlibTM2.Cover.FallbackWord
import IntegerMultBounds.Machine.BinaryDivide

/-! Read the represented shear result at the address specified by the elimination word. -/
public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine Host
variable {T A M B n : ℕ} [NeZero M]

/-- After packing the two selected fields as control and target, the destination
stacks contain the original symbol at the transformed row address. -/
theorem shear_read (call : Fin 12 ↪ Fin T) (F : Stacks T A)
    (source dest : ℤ → Fin 4) (p q : ℤ) (payload : ℕ → ℕ → List (Fin 4))
    (hw : ∀ x y, (payload x y).length = B) (bs ms : List Bool)
    (c : ZMod M) (i k : Fin n) (hik : i < k) (v : Fin n → ZMod M) (j : Fin B)
    (rep : RepT (Alphabet.mapTapes RadixToBinary.binaryEncoding
      (shearBank M B c.val source dest p q payload bs ms M)) (F.L ∘ call) (F.R ∘ call)) :
    let w := (RowOp.shear i k hik c).apply v
    let addr := (w i).val*(M*B) + ((w k).val*B + j.val)
    readAt blank (F.L (call 11)) (F.R (call 11)) ((addr : ℤ) - (M*(M*B) : ℕ)) =
      RadixToBinary.binaryEncoding.encode ((payload (v i).val (v k).val)[j.val]'(by rw [hw]; exact j.isLt)) := by
  let addr := (v i).val*(M*B) + ((((v k).val+c.val*(v i).val)%M)*B+j.val)
  have h := shear_entry c.val M B payload hw ⟨_,(v i).val_lt⟩ ⟨_,(v k).val_lt⟩ j
  have hj : j.val < (payload (v i).val (v k).val).length := by rw [hw]; exact j.isLt
  rw [List.getElem?_eq_getElem hj] at h
  obtain ⟨inside,entry⟩ := List.getElem?_eq_some_iff.mp h
  have cell := BinaryDivide.putWord_getElem dest q _ addr inside
  rw [entry] at cell
  have tape := rep 11 (q+(addr : ℤ))
  change RadixToBinary.binaryEncoding.encode (putWord dest q _ (q+(addr : ℤ))) =
    readAt blank (F.L (call 11)) (F.R (call 11)) ((q+addr)-(q+((M*(M*B) : ℕ) : ℤ))) at tape
  rw [cell] at tape
  simp only [RowOp.apply,Function.update_of_ne hik.ne,Function.update_self,ZMod.val_add,ZMod.val_mul,
    Nat.add_mod_mod]
  rw [show (q+addr)-(q+((M*(M*B) : ℕ) : ℤ)) = (addr : ℤ)-(M*(M*B) : ℕ) by omega] at tape
  exact tape.symm

end IntegerMultBounds.MathlibTM2.Cover.Fallback
