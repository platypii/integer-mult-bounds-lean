module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryOrderData
public import IntegerMultBounds.MathlibTM2.Fast.BandFold

/-! The existing linear tape fold produces the canonical local boundary order. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.BandFactor

theorem interleave_map {α β : Type*} (f : α → β) : ∀ xs ys : List α,
    interleave (xs.map f) (ys.map f) = (interleave xs ys).map f
  | [], [] => rfl
  | [], _::_ => rfl
  | _::_, [] => rfl
  | x::xs, y::ys => by simp only [List.map_cons,interleave,interleave_map f xs ys]

theorem foldList_map {α β : Type*} (f : α → β) (xs : List α) :
    foldList (xs.map f) = (foldList xs).map f := by
  simp only [foldList,List.length_map,← List.map_take,← List.map_drop,← List.map_reverse,interleave_map]

theorem foldList_length {α : Type*} (xs : List α) : (foldList xs).length = xs.length := by
  unfold foldList
  rw [length_interleave _ _ (by simp; omega) (by simp; omega)]
  simp only [List.length_take,List.length_reverse,List.length_drop]
  omega

theorem foldList_bOrder (s : ℕ) [NeZero s] (B : Finset (ZMod s)) :
    foldList (bOrder s B) = bFoldOrder s B := by
  have hlen : (bOrder s B).length = B.card := by
    rw [← List.toFinset_card_of_nodup (bOrder_nodup s B),bOrder_toFinset]
  apply List.ext_getElem (by simp [foldList_length,bFoldOrder,hlen])
  intro i hi hi'
  have hiB : i < B.card := by simpa only [foldList_length,hlen] using hi
  have hg := getD_foldList (0 : ZMod s) (bOrder s B) i (by omega)
  rw [List.getD_eq_getElem _ _ hi] at hg
  calc
    _ = rankAt s B (foldAtN B.card i) := by simpa only [hlen,rankAt] using hg
    _ = _ := by simp [bFoldOrder,bFoldAt,foldAtN,hiB]

def boundaryIndexWords (s t band a b : ℕ) : List GaussianInt :=
  (boundaryIndices s t band a b).map (fun k : ℕ => (⟨k,0⟩ : GaussianInt))

theorem boundaryIndexWords_order {s t : ℕ} [NeZero s] (hst : s < t)
    (band a b : ℕ) (hb : b ≤ s) :
    boundaryIndexWords s t band a b =
      (bOrder s (haloBoundary s t band a b)).map (fun j : ZMod s => (⟨(j.val : ℤ),0⟩ : GaussianInt)) := by
  rw [← boundaryIndices_order hst band a b hb]
  simp only [boundaryIndexWords,List.map_map]
  apply List.map_congr_left
  intro k hk
  have hkS : k < s := List.mem_range.mp (List.mem_filter.mp hk).1
  change (⟨(k : ℤ),0⟩ : GaussianInt) = ⟨(((k : ZMod s).val : ℕ) : ℤ),0⟩
  rw [ZMod.val_cast_of_lt hkS]

theorem boundaryOrderSymbols_cstream (A w s t band a b : ℕ) :
    boundaryOrderSymbols A w s t band a b = cstream A w (boundaryIndexWords s t band a b) := by
  rw [boundaryOrderSymbols_eq]
  simp [boundaryIndexWords,cstream,List.flatMap_map,csyms,red,tblPairs]

theorem boundaryIndexWords_fold {s t : ℕ} [NeZero s] (hst : s < t)
    (band a b : ℕ) (hb : b ≤ s) :
    foldList (boundaryIndexWords s t band a b) =
      (bFoldOrder s (haloBoundary s t band a b)).map (fun j : ZMod s => (⟨(j.val : ℤ),0⟩ : GaussianInt)) := by
  rw [boundaryIndexWords_order hst band a b hb,foldList_map,foldList_bOrder]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
