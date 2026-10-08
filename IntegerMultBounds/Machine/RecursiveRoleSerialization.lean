import IntegerMultBounds.Machine.RecursiveXorRoleBank

/-! The shift/scaling canonical four-symbol payload and the actual pointwise
XOR streams share exactly the same physical word, with no conversion step. -/
namespace IntegerMultBounds.Machine.RecursiveRoleSerialization
noncomputable section
open Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)

private theorem encoded_word (f : ℤ → Fin 4) (z : ℤ) (xs : List (Fin 4)) :
    FlatRepeatedControlNormalize.encoded (radix := prime) (putWord f z xs) =
      putWord (FlatRepeatedControlNormalize.encoded f) z
        (xs.map (RadixToBinary.binaryEncoding (q := prime)).encode) := by
  induction xs generalizing f z with
  | nil => rfl
  | cons x xs ih =>
    funext k
    by_cases hk : k = z
    · subst k; simp [FlatRepeatedControlNormalize.encoded,putWord,List.map_cons]
    · simp only [List.map_cons,putWord,FlatRepeatedControlNormalize.encoded,Function.update_of_ne hk]
      exact congrFun (ih f (z+1)) k

def encode (x : Fin 4) : Fin (prime+4) := (RadixToBinary.binaryEncoding (q := prime)).encode x

theorem source_eq_word {v : Descriptor} (a : Fin (volume prime v) → Fin 4) :
    RecursiveShiftRoleBank.source a = RecursiveXorRoleBank.word (fun i => encode (a i)) := by
  change FlatRepeatedControlNormalize.encoded (putWord (fun _ => blank) 0 (List.ofFn a)) = _
  rw [encoded_word,List.map_ofFn]
  rfl

theorem encode_xor (x y : Fin 4) :
    PointwiseBinary.xorSymbol (encode x) (encode y) = encode (PointwiseBinary.xorSymbol x y) := by
  fin_cases x <;> fin_cases y <;> rfl

variable {t : ℕ} {v : Descriptor}

def roles (data : Fin t → Fin (volume prime v) → Fin 4) : Tapes t prime :=
  ⟨fun _ => 0,fun wire => RecursiveShiftRoleBank.source (data wire)⟩

theorem roles_update (data : Fin t → Fin (volume prime v) → Fin 4) (wire : Fin t)
    (xs : Fin (volume prime v) → Fin 4) :
    RecursiveShiftRoleBank.updated (roles data) wire xs = roles (Function.update data wire xs) := by
  apply congrArg₂ Tapes.mk
  · funext i
    by_cases hi : i = wire <;> simp [roles,hi]
  · funext i
    by_cases hi : i = wire <;> simp [roles,hi]

theorem roles_xor (data : Fin t → Fin (volume prime v) → Fin 4) (g : PointwiseRoleGate.Gate t) :
    RecursiveXorRoleBank.updated (roles data) g
      (fun i => PointwiseBinary.xorSymbol (encode (data g.src i)) (encode (data g.dst i))) =
      roles (Function.update data g.dst (fun i => PointwiseBinary.xorSymbol (data g.src i) (data g.dst i))) := by
  simp only [encode_xor,RecursiveXorRoleBank.updated,← source_eq_word]
  exact roles_update data g.dst _

end
end IntegerMultBounds.Machine.RecursiveRoleSerialization
