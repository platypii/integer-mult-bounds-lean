import IntegerMultBounds.Machine.BinaryAddressOffsetRepeatBudget

/-! Exact expansion lookup, including the dirty-back and spectator coordinates.
These identities match the bytes emitted by the real counted copier. -/
namespace IntegerMultBounds.Machine.BinaryAddressOffsetRepeatValue
open BinaryAddressOffsetRepeatData

theorem copies_flatten {α : Type*} (xs : List α) (K : ℕ) : copies xs K=(List.replicate K xs).flatten := by
  induction K with
  | zero => rfl
  | succ K ih => rw [copies_succ,List.replicate_add,List.replicate_one,List.flatten_append,←ih]; simp

theorem copies_entry {α : Type*} (xs : List α) (K k j : ℕ) (hk : k<K) (hj : j<xs.length) :
    (copies xs K)[k*xs.length+j]?=xs[j]? := by
  rw [copies_flatten]
  have hh := BlockRotationData.flatten_index xs.length (List.replicate K xs)
    (by intro ys hy; rw [List.eq_of_mem_replicate hy])
    k j (by simpa using hk) hj
  simpa using hh

theorem expanded_entry {α : Type*} (blocks : List (List α)) (W L i l j : ℕ)
    (hu : BlockRotationData.Uniform W blocks) (hi : i<blocks.length) (hl : l<L) (hj : j<W) :
    (expanded blocks L)[(i*L+l)*W+j]?=blocks[i][j]? := by
  have hj' : l*W+j<L*W := by nlinarith
  have hh := BlockRotationData.flatten_index (L*W) (blocks.map (fun xs => copies xs L))
    (by intro xs hx; obtain ⟨ys,hy,rfl⟩ := List.mem_map.mp hx; rw [copies_length,hu ys hy])
    i (l*W+j) (by simpa using hi) hj'
  simp only [List.getElem_map] at hh
  have hlen := hu blocks[i] (List.getElem_mem hi)
  have hcopy := copies_entry blocks[i] L l j hl (by omega)
  rw [hlen] at hcopy
  have he : (i*L+l)*W+j=i*(L*W)+(l*W+j) := by ring
  rw [he]
  exact hh.trans hcopy

theorem repeated_entry {α : Type*} (blocks : List (List α)) (W L K k i l j : ℕ)
    (hu : BlockRotationData.Uniform W blocks) (hk : k<K) (hi : i<blocks.length) (hl : l<L) (hj : j<W) :
    (copies (expanded blocks L) K)[((k*blocks.length+i)*L+l)*W+j]?=blocks[i][j]? := by
  have hlen := expanded_length blocks W L hu
  have hlt : (i*L+l)*W+j<(expanded blocks L).length := by
    have hm := Nat.mul_le_mul_right W (show i*L+l+1≤blocks.length*L by nlinarith)
    rw [hlen]; nlinarith
  have hh := copies_entry (expanded blocks L) K k ((i*L+l)*W+j) hk hlt
  rw [hlen] at hh
  have he : ((k*blocks.length+i)*L+l)*W+j=k*(blocks.length*(L*W))+((i*L+l)*W+j) := by ring
  rw [he]
  exact hh.trans (expanded_entry blocks W L i l j hu hi hl hj)

theorem repeated_field (blocks : List (List Bool)) (W L K k i l : ℕ)
    (hu : BlockRotationData.Uniform W blocks) (hk : k<K) (hi : i<blocks.length) (hl : l<L) :
    Gather.field (copies (expanded blocks L) K) (((k*blocks.length+i)*L+l)*W) W=blocks[i] := by
  apply List.ext_getElem
  · rw [Gather.field_length,hu blocks[i] (List.getElem_mem hi)]
  · intro j hj hj'
    have hjW : j<W := by simpa only [Gather.field_length] using hj
    simp only [Gather.field,List.getElem_map,List.getElem_range,List.getD_eq_getElem?_getD]
    rw [repeated_entry blocks W L K k i l j hu hk hi hl hjW,List.getElem?_eq_getElem hj']
    rfl

/-- The base producer's literal word is precisely the concatenation of its
per-address offset fields; no alternate table representation is assumed. -/
theorem offsets_flatten (q b n : ℕ) (hb : 1≤b) (hbq : b+1≤q) :
    (offsets q b n hb hbq).flatten=BinaryAddressOffsetData.word q b n hb hbq := by
  let blocks := offsets q b n hb hbq
  have hu : BlockRotationData.Uniform (n*b) blocks := by
    intro xs hx; obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx; exact BinaryAddressOffsetValue.rowWord_length _ _ _ _ _ _
  have hlen : blocks.length=2^(n*q) := by simp [blocks,offsets]
  apply List.ext_getElem
  · rw [BlockRotationData.uniform_volume (n*b) blocks hu,hlen,BinaryAddressOffsetData.word_length]; ring
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
      (BinaryAddressOffsetValue.field_eq q b n (j/(n*b)) hb hbq hi)
    rw [List.getElem?_eq_getElem (by simpa using hr)] at hf
    simp only [Gather.field,List.getElem_map,List.getElem_range,List.getD_eq_getElem?_getD,he,
      List.getElem?_eq_getElem hj',Option.getD_some] at hf
    change some (blocks.flatten[j]'hj)=_ at hh
    simp only [blocks,offsets,List.getElem_map,List.getElem_range] at hh
    exact Option.some.inj (hh.trans hf.symm)

theorem offsets_uniform (q b n : ℕ) (hb : 1≤b) (hbq : b+1≤q) :
    BlockRotationData.Uniform (n*b) (offsets q b n hb hbq) := by
  intro xs hx; obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx; exact BinaryAddressOffsetValue.rowWord_length _ _ _ _ _ _

theorem destination_field_value (q b n L K k i l : ℕ) (hb : 1≤b) (hbq : b+1≤q)
    (hk : k<K) (hi : i<2^(n*q)) (hl : l<L) :
    (Counter.value (Gather.field (destination q b n L K hb hbq)
      (((k*2^(n*q)+i)*L+l)*(n*b)) (n*b)) : ℤ)=
      Compact.Radix.pack ((2 : ℤ)^b) ((Compact.Radix.digits ((2 : ℤ)^q) n i).map (·%2)) := by
  have he := repeated_field (offsets q b n hb hbq) (n*b) L K k i l
    (offsets_uniform q b n hb hbq) hk (by simpa [offsets] using hi) hl
  simp only [offsets,List.length_map,List.length_range,List.getElem_map,List.getElem_range] at he
  rw [destination,offsets,he]
  rw [←BinaryAddressOffsetValue.field_eq q b n i hb hbq hi]
  exact BinaryAddressOffsetValue.field_value q b n i hb hbq hi

end IntegerMultBounds.Machine.BinaryAddressOffsetRepeatValue
