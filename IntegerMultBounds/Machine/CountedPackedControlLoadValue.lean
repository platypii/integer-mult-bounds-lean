import IntegerMultBounds.Machine.CountedPackedControlLoadRun
import IntegerMultBounds.Compact.PackedArithValue

/-! The physically executed control loader adds or subtracts the packed
control integers in the dirty-word modulus, including one-bit radix digits. -/
namespace IntegerMultBounds.Machine.CountedPackedControlLoadRun
open Counter (value)
open Compact.PowerTwo (ctrl value_gather value_digitWord value_singleton list_eq_range addMod_value pow_blocks)
open Compact.Radix (pack)
open CountedPackedControlLoadHeaders (shape)

theorem controlWord_value (b : ℕ) (hb : 1 ≤ b) (X : List Bool) :
    (value (Gather.gather (fun _ z => z) (shape b hb) X X X.length) : ℤ) =
      pack ((2 : ℤ)^b) (X.map ctrl) := by
  rw [value_gather]
  conv_rhs => rw [list_eq_range X,List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp,value_digitWord,shape,Gather.field,List.range_one,List.map_cons,
    List.map_nil,pow_zero,one_mul,value_singleton]
  cases X.getD i false <;> simp [ctrl]

theorem load_value (b : ℕ) (hb : 1 ≤ b) (U X : List Bool) (hU : U.length = X.length*b) :
    (value (word ColumnTransducer.addRule b hb U X) : ℤ) =
      ((value U : ℤ)+pack ((2 : ℤ)^b) (X.map ctrl)) % (((2 : ℤ)^b)^X.length) := by
  have hl : U.length = (Gather.gather (fun _ z => z) (shape b hb) X X X.length).length := by
    simpa only [Gather.gather_length,shape] using hU
  rw [word,addMod_value _ _ hl,controlWord_value,hU,pow_blocks]

theorem unload_value (b : ℕ) (hb : 1 ≤ b) (U X : List Bool) (hU : U.length = X.length*b) :
    (value (word ColumnTransducer.subRule b hb U X) : ℤ) =
      ((value U : ℤ)-pack ((2 : ℤ)^b) (X.map ctrl)) % (((2 : ℤ)^b)^X.length) := by
  have hl : U.length = (Gather.gather (fun _ z => z) (shape b hb) X X X.length).length := by
    simpa only [Gather.gather_length,shape] using hU
  rw [word,ColumnTransducer.subRule_value _ _ hl,controlWord_value,hU,pow_blocks]

end IntegerMultBounds.Machine.CountedPackedControlLoadRun
