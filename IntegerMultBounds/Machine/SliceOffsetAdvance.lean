import IntegerMultBounds.Machine.ArbitrarySliceCall
import IntegerMultBounds.Machine.BinaryDescriptorAdvance

/-! Physical offset advancement placed in the existing twelve-tape slice tail.
The root bank, saved frame and every other control tape remain exact. -/
namespace IntegerMultBounds.Machine.SliceOffsetAdvance
noncomputable section
variable {T q : ℕ}

def slot (i : Fin 3) : Fin (T+12) := Fin.natAdd T (![0,2,1] i : Fin 12)

private theorem slot_injective : Function.Injective (slot (T := T)) := by
  intro i j h
  have hh := congrArg Fin.val h
  fin_cases i <;> fin_cases j <;> simp_all [slot]

def placement : Fin (3+(T+9)) ≃ Fin (T+12) :=
  InjectivePlacement.placement slot slot_injective (by omega)

@[simp] theorem active_slot (i : Fin 3) :
    placement (T := T) (Fin.castAdd (T+9) i) = slot i :=
  InjectivePlacement.active_slot _ _ _ _

private theorem active_bank (v : Tapes T q) (ts bs : List Bool) (st : Tapes 1 q) :
    Placement.active placement (v.append (SliceHeaderPlacement.tail ts bs st)) =
      BinaryDescriptorAdvance.input ts bs := by
  rw [placement,InjectivePlacement.active_bank]
  apply congrArg₂ Tapes.mk
  · funext i
    fin_cases i <;> simp [slot,Tapes.append,SliceHeaderPlacement.tail] <;> rfl
  · funext i
    fin_cases i
    all_goals simp only [slot,Tapes.append,Fin.addCases_right]
    · exact (BinaryDescriptorStackRoundtrip.descriptor_encoded ts).symm
    · rfl
    · change RadixZeroFill.encodedBinary bs = CountedLoopReuseAlphabet.binary bs
      change (fun z => (RadixToBinary.binaryEncoding (q := q)).encode (CountedCopyReuse.binary bs z)) = _
      exact CountedLoopReuseAlphabet.encoding_binary (a := q) bs

private theorem extra_ne (i : Fin (T+9)) :
    placement (T := T) (Fin.natAdd 3 i) ≠ slot (0 : Fin 3) := by
  intro h
  rw [← active_slot] at h
  have hh := congrArg Fin.val (placement.injective h)
  simp only [Fin.val_natAdd,Fin.val_castAdd] at hh
  omega

private theorem extra_bank (v : Tapes T q) (ts us bs : List Bool) (st : Tapes 1 q) :
    Placement.extra placement (v.append (SliceHeaderPlacement.tail ts bs st)) =
      Placement.extra placement (v.append (SliceHeaderPlacement.tail us bs st)) := by
  have hf (i : Fin (T+9)) :
      (v.append (SliceHeaderPlacement.tail ts bs st)).head (placement (Fin.natAdd 3 i)) =
        (v.append (SliceHeaderPlacement.tail us bs st)).head (placement (Fin.natAdd 3 i)) ∧
      (v.append (SliceHeaderPlacement.tail ts bs st)).tape (placement (Fin.natAdd 3 i)) =
        (v.append (SliceHeaderPlacement.tail us bs st)).tape (placement (Fin.natAdd 3 i)) := by
    let z := placement (T := T) (Fin.natAdd 3 i)
    by_cases hz : z.val < T
    · let j : Fin T := ⟨z.val,hz⟩
      have he : z = Fin.castAdd 12 j := rfl
      change (v.append _).head z = (v.append _).head z ∧ (v.append _).tape z = (v.append _).tape z
      rw [he]
      simp only [Tapes.append,Fin.addCases_left]
      exact ⟨trivial,trivial⟩
    · let j : Fin 12 := ⟨z.val-T,by have := z.isLt; omega⟩
      have he : z = Fin.natAdd T j := by apply Fin.ext; simp only [Fin.val_natAdd,j]; omega
      have hn : j ≠ 0 := by
        intro h
        apply extra_ne i
        change z = slot 0
        simpa only [h,slot,Matrix.cons_val_zero] using he
      change (v.append _).head z = (v.append _).head z ∧ (v.append _).tape z = (v.append _).tape z
      rw [he]
      simp only [Tapes.append,Fin.addCases_right]
      generalize hj : j = k at hn ⊢
      fin_cases k <;> first | exact False.elim (hn rfl) | exact ⟨rfl,rfl⟩
  apply congrArg₂ Tapes.mk
  · funext i; exact (hf i).1
  · funext i; exact (hf i).2

def program := Placement.placed (BinaryDescriptorAdvance.program (q := q)) (placement (T := T))

theorem advances_hoare (v : Tapes T q) (ts bs : List Bool) (st : Tapes 1 q)
    (b : ℕ) (hb : Counter.value bs = b) :
    HoareTime program (fun w => w = v.append (SliceHeaderPlacement.tail ts bs st))
      (fun w => w = v.append (SliceHeaderPlacement.tail (GrowingCounterData.advance b ts) bs st))
      (10*b+2*ts.length+7*bs.length+28) := by
  have h := Placement.hoare_at (BinaryDescriptorAdvance.advances_hoare ts bs b hb)
    placement (v.append (SliceHeaderPlacement.tail ts bs st)) (active_bank v ts bs st)
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro w ⟨z,rfl,rfl⟩
  rw [Placement.replace,extra_bank v ts (GrowingCounterData.advance b ts) bs st,
    ← active_bank v (GrowingCounterData.advance b ts) bs st]
  exact Placement.view _ _

end
end IntegerMultBounds.Machine.SliceOffsetAdvance
