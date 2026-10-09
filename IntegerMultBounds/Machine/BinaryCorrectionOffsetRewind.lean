import IntegerMultBounds.Machine.BinaryCorrectionOffsetGather

/-! Paid prefix rewinds preserve the unread suffix of a full generated word.
This is needed because controlsAt reads one source bit per digit, rather than
the full b-bit address stride. -/
namespace IntegerMultBounds.Machine.BinaryCorrectionOffsetRewind
open SharedPlacementAlphabet (setTape)
variable {t : ℕ}
noncomputable section

def program (slot : Fin t) := Placement.placed (ReturnOrigin.program (a := 0)) (FiniteReturnStackAt.placement slot)

theorem runs (slot : Fin t) (v : Tapes t 0) (xs : List Bool) (k : ℕ) (hk : k≤xs.length)
    (ht : v.tape slot=putWord (fun _ => blank) 0 (xs.map bitSymbol)) (hh : v.head slot=k) :
    HoareTime (program slot) (fun z => z=v) (fun z => z=setTape v slot (v.tape slot) 0) (k+2) := by
  have h := ReturnOrigin.return_hoare_prefix (fun _ => (blank : Fin 4)) 0
    ((xs.take k).map bitSymbol) ((xs.drop k).map bitSymbol) (ReturnOrigin.bits_nonblank _) rfl
  rw [←List.map_append,List.take_append_drop] at h
  simp only [List.length_map,List.length_take,Nat.min_eq_left hk,zero_add] at h
  have ha : Placement.active (FiniteReturnStackAt.placement slot) v=
      (ReturnOrigin.cfg (putWord (fun _ => blank) 0 (xs.map bitSymbol)) k 0).tapes := by
    rw [FiniteReturnStackAt.active_bank,ht,hh]; rfl
  apply (Placement.hoare_at h _ v ha).consequence (fun _ h => h) _ le_rfl
  rintro z ⟨small,rfl,rfl⟩
  change Placement.replace _ _ (FiniteReturnStack.bank (putWord (fun _ => blank) 0 (xs.map bitSymbol)) 0)=_
  rw [FiniteReturnStackAt.replace_bank,←ht]

end
end IntegerMultBounds.Machine.BinaryCorrectionOffsetRewind
