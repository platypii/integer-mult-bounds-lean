import IntegerMultBounds.Machine.BinaryParityXorOffsetPositive

namespace IntegerMultBounds.Machine.BinaryParityXorOffsetValue
open BinaryParityXorOffsetData

theorem rows_flatten (q b n : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) (hZ : Z.length=n) :
    (rows q b n Z hb hbq).flatten=positiveWord q b n Z hb hbq := by
  let blocks := rows q b n Z hb hbq
  have hu : BlockRotationData.Uniform (n*b) blocks := by
    intro xs hx; obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx; exact rowWord_length _ _ _ _ _ _ _
  have hlen : blocks.length=2^(n*q) := by simp [blocks,rows]
  apply List.ext_getElem
  · rw [BlockRotationData.uniform_volume (n*b) blocks hu,hlen,positiveWord_length]; ring
  · intro j hj hj'
    have hjv : j<(2^(n*q))*(n*b) := by
      have hjb : j<blocks.flatten.length := hj
      rw [BlockRotationData.uniform_volume (n*b) blocks hu,hlen] at hjb
      exact hjb
    have hW : 0<n*b := by nlinarith
    have hi : j/(n*b)<2^(n*q) := (Nat.div_lt_iff_lt_mul hW).mpr hjv
    have hr : j%(n*b)<n*b := Nat.mod_lt _ hW
    have he : j/(n*b)*(n*b)+j%(n*b)=j := by simpa only [Nat.mul_comm] using Nat.div_add_mod j (n*b)
    have hh := BlockRotationData.flatten_index (n*b) blocks hu (j/(n*b)) (j%(n*b)) (by omega) hr
    rw [he,List.getElem?_eq_getElem hj] at hh
    have hf := congrArg (fun xs : List Bool => xs[j%(n*b)]?)
      (BinaryParityXorOffsetPositive.field_eq q b n (j/(n*b)) Z hb hbq hZ hi)
    rw [List.getElem?_eq_getElem (by simpa using hr)] at hf
    simp only [Gather.field,List.getElem_map,List.getElem_range,List.getD_eq_getElem?_getD,he,
      List.getElem?_eq_getElem hj',Option.getD_some] at hf
    change some (blocks.flatten[j]'hj)=_ at hh
    simp only [blocks,rows,List.getElem_map,List.getElem_range] at hh
    exact Option.some.inj (hh.trans hf.symm)

theorem field_eq (q b n i : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q)
    (hi : i<2^(n*q)) :
    Gather.field (word q b n Z hb hbq) (i*(n*b)) (n*b)=TwosComplement.negWord (rowWord q b n i Z hb hbq) := by
  let blocks := (rows q b n Z hb hbq).map TwosComplement.negWord
  have hu : BlockRotationData.Uniform (n*b) blocks := by
    intro xs hx
    obtain ⟨ys,hy,rfl⟩ := List.mem_map.mp hx
    rw [TwosComplement.negWord_length]
    exact rows_uniform q b n Z hb hbq ys hy
  apply List.ext_getElem
  · simp [TwosComplement.negWord_length]
  · intro j hj hj'
    have hjW : j<n*b := by simpa only [Gather.field_length] using hj
    have hh := BlockRotationData.flatten_index (n*b) blocks hu i j (by simpa [blocks,rows] using hi) hjW
    simp only [blocks,rows,List.getElem_map,List.getElem_range] at hh
    simp only [Gather.field,List.getElem_map,List.getElem_range,List.getD_eq_getElem?_getD]
    change (blocks.flatten[i*(n*b)+j]?).getD false=_
    change blocks.flatten[i*(n*b)+j]?=(TwosComplement.negWord (rowWord q b n i Z hb hbq))[j]? at hh
    rw [hh,List.getElem?_eq_getElem hj']
    rfl

theorem negWord_value (xs : List Bool) :
    (Counter.value (TwosComplement.negWord xs) : ℤ)=(-(Counter.value xs : ℤ))%2^xs.length := by
  have h : ((Counter.value (TwosComplement.negWord xs) : ℤ)+Counter.value xs)%2^xs.length=0 := by
    exact_mod_cast TwosComplement.negWord_value xs
  have hlt : (Counter.value (TwosComplement.negWord xs) : ℤ)<2^xs.length := by
    have ht := Counter.value_lt (TwosComplement.negWord xs)
    rw [TwosComplement.negWord_length] at ht
    exact_mod_cast ht
  calc
    (Counter.value (TwosComplement.negWord xs) : ℤ) =
        (Counter.value (TwosComplement.negWord xs) : ℤ)%2^xs.length := (Int.emod_eq_of_lt (by positivity) hlt).symm
    _ = ((Counter.value (TwosComplement.negWord xs) : ℤ)+Counter.value xs-Counter.value xs)%2^xs.length := by congr 1; omega
    _ = (-(Counter.value xs : ℤ))%2^xs.length := by
      have hv : (Counter.value xs : ℤ)%2^xs.length=(Counter.value xs : ℤ) :=
        Int.emod_eq_of_lt (by positivity) (by exact_mod_cast Counter.value_lt xs)
      rw [Int.sub_emod,h,hv,zero_sub]

theorem field_value (q b n i : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q)
    (hZ : Z.length=n) (hi : i<2^(n*q)) :
    (Counter.value (Gather.field (word q b n Z hb hbq) (i*(n*b)) (n*b)) : ℤ)=
      (-Compact.Radix.pack ((2 : ℤ)^b) (List.zipWith (fun v z => (v%2+z)%2)
        (Compact.Radix.digits ((2 : ℤ)^q) n i) (Z.map Compact.PowerTwo.ctrl))) % (2 : ℤ)^(n*b) := by
  rw [field_eq q b n i Z hb hbq hi,negWord_value,rowWord_length,
    ←BinaryParityXorOffsetPositive.field_eq q b n i Z hb hbq hZ hi,
    BinaryParityXorOffsetPositive.field_value q b n i Z hb hbq hZ hi]

end IntegerMultBounds.Machine.BinaryParityXorOffsetValue
