import IntegerMultBounds.Machine.FixedBasePowerDescriptor
import IntegerMultBounds.Machine.BoundedProductDescriptor
import IntegerMultBounds.Machine.InjectivePlacement

/-! Descriptor constructors may share input tapes with a larger bank. Exact
single-output framing preserves every original tape outside the output slot. -/
namespace IntegerMultBounds.Machine.PlacedDescriptorConstruction
noncomputable section
open SharedPlacementAlphabet (setTape)
variable {s u t a : ℕ}

theorem replace_setTape (e : Fin (s+u) ≃ Fin t) (v : Tapes t a) (i : Fin s)
    (f : ℤ → Fin (a+4)) (p : ℤ) :
    Placement.replace e v (setTape (Placement.active e v) i f p) =
      setTape v (e (Fin.castAdd u i)) f p := by
  apply congrArg₂ Tapes.mk
  · funext z
    obtain ⟨z,rfl⟩ := e.surjective z
    induction z using Fin.addCases with
    | left j =>
      change (Placement.combine e (setTape (Placement.active e v) i f p) (Placement.extra e v)).head (e (Fin.castAdd u j)) = _
      rw [Placement.combine_head_active]
      simp only [setTape,Placement.active,Function.update_apply]
      simp [e.injective.eq_iff]
    | right j =>
      change (Placement.combine e (setTape (Placement.active e v) i f p) (Placement.extra e v)).head (e (Fin.natAdd s j)) = _
      rw [Placement.combine_head_extra]
      have hn : e (Fin.natAdd s j) ≠ e (Fin.castAdd u i) := by
        intro h
        have hv := congrArg Fin.val (e.injective h)
        simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
        omega
      simp [Placement.extra,hn]
  · funext z
    obtain ⟨z,rfl⟩ := e.surjective z
    induction z using Fin.addCases with
    | left j =>
      change (Placement.combine e (setTape (Placement.active e v) i f p) (Placement.extra e v)).tape (e (Fin.castAdd u j)) = _
      rw [Placement.combine_tape_active]
      simp only [setTape,Placement.active,Function.update_apply]
      simp [e.injective.eq_iff]
    | right j =>
      change (Placement.combine e (setTape (Placement.active e v) i f p) (Placement.extra e v)).tape (e (Fin.natAdd s j)) = _
      rw [Placement.combine_tape_extra]
      have hn : e (Fin.natAdd s j) ≠ e (Fin.castAdd u i) := by
        intro h
        have hv := congrArg Fin.val (e.injective h)
        simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
        omega
      simp [Placement.extra,hn]

theorem power_hoare (e : Fin (8+u) ≃ Fin t) (v : Tapes t a)
    (B k : ℕ) (hB : 2 ≤ B) (ks : List Bool) (hk : Counter.value ks = k)
    (ck : GrowingCounterData.Canonical ks)
    (ha : Placement.active e v = FixedBasePowerDescriptor.input ks) :
    HoareTime (Placement.placed (FixedBasePowerDescriptor.program (q := a) B) e)
      (fun w => w = v)
      (fun w => w = setTape v (e (Fin.castAdd u (5 : Fin 8)))
        (RadixZeroFill.encodedBinary (FixedBasePowerStep.bits B k)) 1)
      (FixedBasePowerDescriptor.constant B*B^k) := by
  have h := Placement.hoare_at (FixedBasePowerDescriptor.constructs_linear B k hB ks hk ck) e v ha
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro w ⟨z,rfl,rfl⟩
  rw [FixedBasePowerDescriptor.output,← ha,replace_setTape]

theorem product_hoare (e : Fin (6+u) ≃ Fin t) (v : Tapes t a)
    (ws ns : List Bool) (N W Q : ℕ) (hW : 0 < W)
    (hw : Counter.value ws = W) (hn : Counter.value ns = N)
    (hN : N ≤ Q) (ww : ws.length ≤ W+1) (wn : ns.length ≤ Q+1)
    (ha : Placement.active e v = BoundedProductDescriptor.input ws ns) :
    HoareTime (Placement.placed (BoundedProductDescriptor.program (q := a)) e)
      (fun w => w = v)
      (fun w => w = setTape v (e (Fin.castAdd u (1 : Fin 6)))
        (RadixZeroFill.encodedBinary (BoundedProductDescriptor.bits N W)) 1)
      (53*(Q*W)+28) := by
  have h := Placement.hoare_at (BoundedProductDescriptor.construct_hoare ws ns N W Q hW hw hn hN ww wn) e v ha
  have he : BoundedProductDescriptor.output (q := a) ws ns N W =
      setTape (BoundedProductDescriptor.input ws ns) (1 : Fin 6)
        (RadixZeroFill.encodedBinary (BoundedProductDescriptor.bits N W)) 1 := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro w ⟨z,rfl,rfl⟩
  rw [he,← ha,replace_setTape]

end
end IntegerMultBounds.Machine.PlacedDescriptorConstruction
