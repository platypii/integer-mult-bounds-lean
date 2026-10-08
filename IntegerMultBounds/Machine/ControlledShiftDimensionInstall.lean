import IntegerMultBounds.Machine.FlatControlledShiftLayout
import IntegerMultBounds.Machine.BinaryDescriptorInstall

/-! Physically install the B/Q/P words of a controlled shift from the retained
nine-tape dimension bank. Every destination starts wholly blank. -/
namespace IntegerMultBounds.Machine.ControlledShiftDimensionInstall
open SharedPlacementAlphabet (setTape)
open FlatControlledShiftLayout (suffix)
variable {q : ℕ}

private theorem setTape_append_right {l r : ℕ} (v : Tapes l q) (w : Tapes r q) (i : Fin r)
    (f : ℤ → Fin (q+4)) (p : ℤ) :
    setTape (v.append w) (Fin.natAdd l i) f p = v.append (setTape w i f p) := by
  unfold setTape Tapes.append
  congr 1 <;> funext j <;> induction j using Fin.addCases <;> simp [Function.update_apply,Fin.ext_iff]
  all_goals rename_i k; intro h; have hk := k.isLt; omega

private theorem set_b (source dest : ℤ → Fin 4) (p r : ℤ)
    (bs qs ns : Option (List Bool)) (xs : List Bool) :
    setTape (suffix q source dest p r bs qs ns) 5 (RadixZeroFill.encodedBinary xs) 1 =
      suffix q source dest p r (some xs) qs ns := by
  unfold setTape suffix
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> simp [FlatControlledShiftLayout.descriptorHead,FlatControlledShiftLayout.descriptorTape]

private theorem set_q (source dest : ℤ → Fin 4) (p r : ℤ)
    (bs qs ns : Option (List Bool)) (xs : List Bool) :
    setTape (suffix q source dest p r bs qs ns) 7 (RadixZeroFill.encodedBinary xs) 1 =
      suffix q source dest p r bs (some xs) ns := by
  unfold setTape suffix
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> simp [FlatControlledShiftLayout.descriptorHead,FlatControlledShiftLayout.descriptorTape]

private theorem set_p (source dest : ℤ → Fin 4) (p r : ℤ)
    (bs qs ns : Option (List Bool)) (xs : List Bool) :
    setTape (suffix q source dest p r bs qs ns) 16 (RadixZeroFill.encodedBinary xs) 1 =
      suffix q source dest p r bs qs (some xs) := by
  unfold setTape suffix
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> simp [FlatControlledShiftLayout.descriptorHead,FlatControlledShiftLayout.descriptorTape]

private def sourceSlot (i : Fin 9) : Fin (9+17) := Fin.castAdd 17 i
private def destSlot (i : Fin 17) : Fin (9+17) := Fin.natAdd 9 i
private theorem separate (i : Fin 9) (j : Fin 17) : sourceSlot i ≠ destSlot j := by
  intro h
  have hv := congrArg Fin.val h
  have hi := i.isLt
  simp only [sourceSlot,destSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

noncomputable def program (q : ℕ) : Program (9+17) 15 q :=
  seq (seq (BinaryDescriptorInstall.program q (sourceSlot 7) (destSlot 5) (separate 7 5))
    (BinaryDescriptorInstall.program q (sourceSlot 4) (destSlot 7) (separate 4 7)))
    (BinaryDescriptorInstall.program q (sourceSlot 5) (destSlot 16) (separate 5 16))

/-- Complete physical installation preserves the dimension bank and both
payloads, and gives the literal raw suffix required by the shift bootstrap. -/
theorem install_hoare (dim : Tapes 9 q) (bs qs ns : List Bool)
    (hb : dim.tape 7 = RadixZeroFill.encodedBinary bs) (hb' : dim.head 7 = 1)
    (hq : dim.tape 4 = RadixZeroFill.encodedBinary qs) (hq' : dim.head 4 = 1)
    (hn : dim.tape 5 = RadixZeroFill.encodedBinary ns) (hn' : dim.head 5 = 1)
    (source dest : ℤ → Fin 4) (p r : ℤ) :
    HoareTime (program q)
      (fun v => v = dim.append (suffix q source dest p r none none none))
      (fun v => v = dim.append (suffix q source dest p r (some bs) (some qs) (some ns)))
      (2*(bs.length+qs.length+ns.length)+17) := by
  have h1 := BinaryDescriptorInstall.install_hoare (sourceSlot 7) (destSlot 5) (separate 7 5)
    (dim.append (suffix q source dest p r none none none)) bs
    (by simpa only [sourceSlot,Tapes.append,Fin.addCases_left] using hb) (by simpa only [sourceSlot,Tapes.append,Fin.addCases_left] using hb')
    (by rfl) (by rfl)
  simp only [destSlot,setTape_append_right,set_b] at h1
  have h2 := BinaryDescriptorInstall.install_hoare (sourceSlot 4) (destSlot 7) (separate 4 7)
    (dim.append (suffix q source dest p r (some bs) none none)) qs
    (by simpa only [sourceSlot,Tapes.append,Fin.addCases_left] using hq) (by simpa only [sourceSlot,Tapes.append,Fin.addCases_left] using hq')
    (by rfl) (by rfl)
  simp only [destSlot,setTape_append_right,set_q] at h2
  have h3 := BinaryDescriptorInstall.install_hoare (sourceSlot 5) (destSlot 16) (separate 5 16)
    (dim.append (suffix q source dest p r (some bs) (some qs) none)) ns
    (by simpa only [sourceSlot,Tapes.append,Fin.addCases_left] using hn) (by simpa only [sourceSlot,Tapes.append,Fin.addCases_left] using hn')
    (by rfl) (by rfl)
  simp only [destSlot,setTape_append_right,set_p] at h3
  exact ((h1.seq h2).seq h3).consequence (fun _ h => h) (fun _ h => h) (by omega)

end IntegerMultBounds.Machine.ControlledShiftDimensionInstall
