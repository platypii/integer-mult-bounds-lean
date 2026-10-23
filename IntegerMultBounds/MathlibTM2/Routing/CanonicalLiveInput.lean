module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalRepairInput
public import IntegerMultBounds.MathlibTM2.Routing.LiveInactiveProfileLayout
public import IntegerMultBounds.MathlibTM2.Routing.RepairLiveDescriptorBank

/-! Canonical live-profile bank: eleven profile streams start empty, while
scalar operands come from dimensions. Seven external tapes hold the count and
blank scratch. The core can be the constructed canonical repair bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget IntegerMultBounds.MathlibTM2.Layer.CompactDigits
noncomputable section
variable {A : ℕ}
local notation "T₀" => liveInactiveProfileT repairT 11
local notation "e₀" => liveInactiveProfileCore (N := repairT) (J := 11)

variable (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (source : Fin p.n → SlotSource p X) (w : LiveDescriptorWidths)

def canonicalDescriptorOperands (r : LiveDescriptorRole 11) : List (Fin (A + 4)) :=
  match r with
  | .input _ => []
  | _ => liveDescriptorData p X hG hK active source repairLiveMode w r

/-- Canonical profile inputs are empty; the remaining descriptor words are scalars. -/
theorem canonicalDescriptorOperands_length_le (r : LiveDescriptorRole 11) :
    (canonicalDescriptorOperands (A := A) p X hG hK active source w r).length ≤
      w.indexBits + w.strideBits + w.coordinateBits + w.selectorBits + w.widthBits + w.groupBits := by
  cases r with
  | profile r =>
    cases r with
    | coordinate r =>
      cases r with
      | arithmetic r => cases r <;> simp [canonicalDescriptorOperands, liveDescriptorData] <;> omega
      | _ => simp [canonicalDescriptorOperands, liveDescriptorData] <;> omega
    | _ => simp [canonicalDescriptorOperands, liveDescriptorData]
  | coordinate r => cases r <;> simp [canonicalDescriptorOperands, liveDescriptorData] <;> omega
  | _ => simp [canonicalDescriptorOperands, liveDescriptorData] <;> omega

def canonicalLiveInputBank (core : Fin repairT → List (Fin (A + 4))) : Fin T₀ → List (Fin (A + 4)) :=
  Fin.addCases (liveDescriptorBank core (canonicalDescriptorOperands p X hG hK active source w))
    (fun i : Fin 7 => if i = 0 then binSyms w.indexBits p.n else [])

theorem canonicalLiveInputBank_length_le (core : Fin repairT → List (Fin (A + 4)))
    (C : ℕ) (hcore : ∀ j, j ≠ repairHost.src → (core j).length ≤ C)
    (j : Fin T₀) (hj : j ≠ e₀ (liveDescriptorCore repairHost.src)) :
    (canonicalLiveInputBank p X hG hK active source w core j).length ≤
      C + w.indexBits + w.strideBits + w.coordinateBits + w.selectorBits + w.widthBits + w.groupBits := by
  revert hj
  refine Fin.addCases ?_ ?_ j
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro q hq
      have hne : q ≠ repairHost.src := by intro he; subst q; exact hq rfl
      simp only [canonicalLiveInputBank, Fin.addCases_left, liveDescriptorBank]

      have hc := hcore q hne
      omega
    · intro r _
      simp only [canonicalLiveInputBank, Fin.addCases_left, liveDescriptorBank]
      rw [Fin.addCases_right]
      have hr := canonicalDescriptorOperands_length_le (A := A) p X hG hK active source w
        ((Fintype.equivFin (LiveDescriptorRole 11)).symm r)
      omega
  · intro i _
    simp only [canonicalLiveInputBank, Fin.addCases_right]
    split <;> simp only [length_binSyms, List.length_nil] <;> omega

theorem canonicalLiveInputBank_core (core : Fin repairT → List (Fin (A + 4))) (j : Fin repairT) :
    canonicalLiveInputBank p X hG hK active source w core (e₀ (liveDescriptorCore j)) = core j := by
  unfold canonicalLiveInputBank liveInactiveProfileCore
  rw [Fin.addCases_left, liveDescriptorBank_core]

theorem canonicalLiveInputBank_descriptor (core : Fin repairT → List (Fin (A + 4))) (r : LiveDescriptorRole 11) :
    canonicalLiveInputBank p X hG hK active source w core (e₀ (liveDescriptorAux r)) =
      canonicalDescriptorOperands p X hG hK active source w r := by
  unfold canonicalLiveInputBank liveInactiveProfileCore
  rw [Fin.addCases_left, liveDescriptorBank_aux]

theorem canonicalLiveInputBank_inputs (core : Fin repairT → List (Fin (A + 4))) (j : Fin 11) :
    canonicalLiveInputBank p X hG hK active source w core (e₀ (liveDescriptorAux (.input j))) = [] := by
  rw [canonicalLiveInputBank_descriptor]
  rfl

theorem canonicalLiveInputBank_operands (core : Fin repairT → List (Fin (A + 4)))
    (r : LiveDescriptorRole 11) (hr : ∀ j, r ≠ .input j) :
    canonicalLiveInputBank p X hG hK active source w core (e₀ (liveDescriptorAux r)) =
      liveDescriptorData p X hG hK active source repairLiveMode w r := by
  rw [canonicalLiveInputBank_descriptor]
  cases r <;> first | rfl | exact (hr _ rfl).elim

theorem canonicalLiveInputBank_aux (core : Fin repairT → List (Fin (A + 4))) (j : Fin 7) :
    canonicalLiveInputBank p X hG hK active source w core (liveInactiveProfileAux j) =
      if j = 0 then binSyms w.indexBits p.n else [] := by
  unfold canonicalLiveInputBank liveInactiveProfileAux
  rw [Fin.addCases_right]

/-- The constructed raw core and live bank already discharge the data and
empty-destination contracts used by the generated pipeline. -/
theorem canonicalLiveInputBank_data (rb wb wm wp wk R B : ℕ)
    (records coordinates : List (Fin (A + 4)))
    (hblock : fieldsLen (selectiveKeyLen p X rb) + B < 2 ^ wb)
    (hrecords : R * 2 ^ fieldsLen (selectiveLen p X) < 2 ^ wm)
    (hpayload : B < 2 ^ wp) (hkey : fieldsLen (selectiveKeyLen p X rb) < 2 ^ wk) :
    RepairPendingMaskData p X rb wb wm wp wk R B (fun _ _ => [])
      (fun j => canonicalLiveInputBank p X hG hK active source w
        (canonicalProfileCoreBank p X rb wb wm wp wk R B records coordinates) (e₀ (liveDescriptorCore j))) := by
  simpa only [canonicalLiveInputBank_core] using
    canonicalProfileCoreBank_data p X rb wb wm wp wk R B records coordinates hblock hrecords hpayload hkey

end
end IntegerMultBounds.MathlibTM2.Routing
