import IntegerMultBounds.Machine.ArbitraryWidthHighExchangeControls

/-! Static regrouping of the shared root bank and the sixteen physical
high-exchange controls. This changes only compile-time tape placement. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthHighExchangePlacement
noncomputable section
variable {T a : ℕ}
open RecursiveChildQuotientsConstant (bits)

def aux (rs : List Bool) : Tapes 2 a :=
  ⟨fun _ => 1,![BinaryDescriptorStack.descriptor rs,BinaryDescriptorStack.descriptor (bits 0)]⟩

private theorem binary_descriptor (xs : List Bool) :
    CountedLoopReuseAlphabet.binary (a := a) xs = BinaryDescriptorStack.descriptor xs := by
  rw [BinaryDescriptorStackRoundtrip.descriptor_encoded]
  exact (CountedLoopReuseAlphabet.encoding_binary xs).symm

private theorem reassociate (v : Tapes T a) (w : Tapes 12 a) (u z : Tapes 2 a) :
    ((v.append w).append u).append z = v.append (w.append (u.append z)) := by
  unfold Tapes.append
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals
    change Fin.append (Fin.append (Fin.append _ _) _) _ i = _
    rw [Fin.append_assoc,Fin.append_assoc]
    rfl

theorem prepared_bank (v : Tapes T a) (rs : List Bool) :
    (((v.append (SliceHeaderPlacement.tail (bits 0) (bits 1) (SharedBank.empty 1 a))).append
      (CountedLoopReuseAlphabet.controls (fun _ => blank) (CountedLoopReuseAlphabet.binary rs) 0 1)).append (aux rs)) =
      v.append (ArbitraryWidthHighExchangeControls.prepared rs) := by
  rw [reassociate]
  apply congrArg (v.append)
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> try rfl
  all_goals first
    | exact (BinaryDescriptorStackRoundtrip.descriptor_encoded _).symm
    | exact binary_descriptor _

theorem returned_bank (v : Tapes T a) (rs ts : List Bool) :
    (((v.append (SliceHeaderPlacement.tail ts (bits 1) (SharedBank.empty 1 a))).append
      (SharedBank.empty 2 a)).append (aux rs)) = v.append (ArbitraryWidthHighExchangeControls.returned rs ts) := by
  rw [reassociate]
  apply congrArg (v.append)
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> try rfl
  all_goals exact (BinaryDescriptorStackRoundtrip.descriptor_encoded _).symm

theorem left_frame {n s q k : ℕ} {M : Program n s a} {x y : Tapes n a}
    (h : HoareTime M (fun v => v = x) (fun v => v = y) k) (v : Tapes q a) :
    HoareTime (Placement.placed M (finAddFlip : Fin (n+q) ≃ Fin (q+n)))
      (fun w => w = v.append x) (fun w => w = v.append y) k := by
  have he (z : Tapes n a) : Placement.combine finAddFlip z v = v.append z := by
    apply congrArg₂ Tapes.mk <;> funext i <;> induction i using Fin.addCases <;>
      simp [Tapes.append,finAddFlip]
  have hh := Placement.hoare_at h finAddFlip (Placement.combine finAddFlip x v)
    (Placement.active_combine _ _ _)
  apply hh.consequence (fun w hw => hw.trans (he x).symm) _ le_rfl
  rintro w ⟨z,hz,rfl⟩
  subst z
  simpa only [Placement.replace,Placement.extra_combine] using he y

end
end IntegerMultBounds.Machine.ArbitraryWidthHighExchangePlacement
