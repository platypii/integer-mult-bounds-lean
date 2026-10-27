module

public import IntegerMultBounds.NLogN.PhaseCellCouplingOffsets

/-! Spatial order for an alias-preserving coupling stencil. -/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellMatrix

def spatialCouplingOffsets (band : ℕ) : List ℤ :=
  ((List.range band).map (fun n : ℕ => -((n : ℤ)+1))).reverse ++
    ([0]++(List.range band).map (fun n : ℕ => (n : ℤ)+1))

theorem spatialCouplingOffsets_perm (band : ℕ) :
    (spatialCouplingOffsets band).Perm (couplingOffsets band).reverse := by
  let pos := (List.range band).map (fun n : ℕ => (n : ℤ)+1)
  let neg := (List.range band).map (fun n : ℕ => -((n : ℤ)+1))
  change (neg.reverse++([0]++pos)).Perm (0::(pos++neg)).reverse
  rw [List.reverse_cons,List.reverse_append,List.append_assoc]
  exact (List.perm_append_comm.trans ((List.reverse_perm pos).symm.append_right [0])).append_left neg.reverse

@[simp] theorem spatialCouplingOffsets_length (band : ℕ) :
    (spatialCouplingOffsets band).length = 2*band+1 := by
  simpa only [List.length_reverse,couplingOffsets_length] using (spatialCouplingOffsets_perm band).length_eq

theorem spatialCouplingOffsets_eq_range (band : ℕ) :
    spatialCouplingOffsets band = (List.range (2*band+1)).map (fun n : ℕ => (n : ℤ)-(band : ℤ)) := by
  have hneg : ((List.range band).map (fun n : ℕ => -((n : ℤ)+1))).reverse =
      (List.range band).map (fun n : ℕ => (n : ℤ)-(band : ℤ)) := by
    apply List.ext_getElem
    · simp
    · intro n hn hn'
      have hb : n < band := by simpa using hn
      simp only [List.getElem_reverse,List.length_map,List.length_range,List.getElem_map,List.getElem_range]
      have he : ((band-1-n : ℕ) : ℤ) = (band : ℤ)-1-n := by omega
      rw [he]
      ring
  have hpos : [0]++(List.range band).map (fun n : ℕ => (n : ℤ)+1) =
      (List.range (band+1)).map (fun n : ℕ => (n : ℤ)) := by
    rw [List.range_succ_eq_map]
    simp [List.map_map,Function.comp_def]
  rw [spatialCouplingOffsets,hneg,hpos,show 2*band+1 = band+(band+1) by omega,List.range_add (n := band) (m := band+1),List.map_append]
  simp [List.map_map,Function.comp_def,Nat.cast_add]

def cyclicPaddedLine {s : ℕ} [NeZero s] {E : Type*} (F : ZMod s → E) (band : ℕ) : List E :=
  (List.range (s+2*band)).map (fun n : ℕ => F ((n : ZMod s)-(band : ZMod s)))

theorem cyclicPaddedLine_window {s : ℕ} [NeZero s] {E : Type*} (F : ZMod s → E)
    (band i : ℕ) (hi : i < s) :
    ((cyclicPaddedLine F band).drop i).take (2*band+1) =
      (spatialCouplingOffsets band).map (fun δ : ℤ => F ((i : ZMod s)+(δ : ZMod s))) := by
  rw [spatialCouplingOffsets_eq_range]
  apply List.ext_getElem
  · simp [cyclicPaddedLine]
    omega
  · intro n hn hn'
    simp only [cyclicPaddedLine,List.getElem_take,List.getElem_drop,List.getElem_map,List.getElem_range]
    congr 1
    push_cast
    ring

end IntegerMultBounds.NLogN.PhaseCellMatrix
