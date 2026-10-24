module

public import IntegerMultBounds.MathlibTM2.Routing.DescriptorScalarFields

/-! The six shared scalar operands complete the non-profile descriptor input.
All other roles outside the 55 per-mode fields are initially empty. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
noncomputable section

def descriptorSharedRole : Fin 6 → LiveDescriptorRole 11 :=
  ![.selectorBits,.group,.profile (.coordinate (.arithmetic .index)),
    .profile (.coordinate .one),.coordinate .cursor,.coordinate .one]

def descriptorSharedValue (p : Par) (w : LiveDescriptorWidths) : Fin 6 → ℕ :=
  ![w.selectorBits,p.G,0,1,0,1]

def descriptorSharedWidth (w : LiveDescriptorWidths) : Fin 6 → ℕ :=
  ![w.widthBits,w.groupBits,w.indexBits,w.selectorBits,w.coordinateBits,w.coordinateBits]

theorem descriptorSharedRole_injective : Function.Injective descriptorSharedRole := by
  decide +kernel

theorem descriptorSharedRole_separate (i : Fin 6) (j : Fin 11) (f : Fin 5) :
    descriptorSharedRole i ≠ descriptorScalarRole j f := by
  fin_cases i <;> fin_cases f <;> simp [descriptorSharedRole, descriptorScalarRole]

theorem descriptorSharedRole_operands {A : ℕ} (p : Par) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (source : Fin p.n → SlotSource p 0)
    (w : LiveDescriptorWidths) (i : Fin 6) :
    (binSyms (descriptorSharedWidth w i) (descriptorSharedValue p w i) : List (Fin (A + 4))) =
      canonicalDescriptorOperands p 0 hG hK active source w (descriptorSharedRole i) := by
  fin_cases i <;> rfl

theorem canonicalDescriptorOperands_other {A : ℕ} (p : Par) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (source : Fin p.n → SlotSource p 0)
    (w : LiveDescriptorWidths) (r : LiveDescriptorRole 11)
    (hscalar : ∀ j f, r ≠ descriptorScalarRole j f)
    (hshared : ∀ i, r ≠ descriptorSharedRole i) :
    canonicalDescriptorOperands (A := A) p 0 hG hK active source w r = [] := by
  have hs (i : Fin 6) := hshared i
  cases r with
  | stride j => exact (hscalar j 0 rfl).elim
  | base j => exact (hscalar j 1 rfl).elim
  | last j => exact (hscalar j 2 rfl).elim
  | rows j => exact (hscalar j 3 rfl).elim
  | sourceWidth j => exact (hscalar j 4 rfl).elim
  | selectorBits => exact (hs 0 rfl).elim
  | group => exact (hs 1 rfl).elim
  | profile r =>
    cases r with
    | coordinate r =>
      cases r with
      | arithmetic r =>
        cases r <;> first | exact (hs 2 rfl).elim | rfl
      | one => exact (hs 3 rfl).elim
      | _ => rfl
    | _ => rfl
  | coordinate r =>
    cases r with
    | cursor => exact (hs 4 rfl).elim
    | one => exact (hs 5 rfl).elim
    | _ => rfl
  | _ => rfl

/-- Matching the 61 scalar roles and blank remainder establishes the complete
canonical descriptor operand bank, including empty profile inputs. -/
theorem canonicalDescriptorOperands_eq {A : ℕ} (p : Par) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (source : Fin p.n → SlotSource p 0)
    (w : LiveDescriptorWidths) (data : LiveDescriptorRole 11 → List (Fin (A + 4)))
    (hscalar : ∀ j f, data (descriptorScalarRole j f) =
      binSyms (repairDescriptorScalarWidth w f) (repairDescriptorScalarValues p j f))
    (hshared : ∀ i, data (descriptorSharedRole i) =
      binSyms (descriptorSharedWidth w i) (descriptorSharedValue p w i))
    (hblank : ∀ r, (∀ j f, r ≠ descriptorScalarRole j f) →
      (∀ i, r ≠ descriptorSharedRole i) → data r = []) :
    data = canonicalDescriptorOperands p 0 hG hK active source w := by
  funext r
  by_cases hs : ∃ j f, r = descriptorScalarRole j f
  · obtain ⟨j,f,rfl⟩ := hs
    rw [hscalar, ← repairDescriptorScalarPalette_words]
    exact descriptorScalarRole_operands p hG hK active source w j f
  by_cases hh : ∃ i, r = descriptorSharedRole i
  · obtain ⟨i,rfl⟩ := hh
    rw [hshared]
    exact descriptorSharedRole_operands p hG hK active source w i
  have hs' : ∀ j f, r ≠ descriptorScalarRole j f := fun j f h => hs ⟨j,f,h⟩
  have hh' : ∀ i, r ≠ descriptorSharedRole i := fun i h => hh ⟨i,h⟩
  rw [hblank r hs' hh',canonicalDescriptorOperands_other p hG hK active source w r hs' hh']

end
end IntegerMultBounds.MathlibTM2.Routing
