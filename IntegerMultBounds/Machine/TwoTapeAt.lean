import IntegerMultBounds.Machine.PlacementBank
import IntegerMultBounds.Machine.SharedPlacementAlphabet
import IntegerMultBounds.Machine.Copy

/-! Exact two-tape routines placed at two fixed distinct slots, framing every
other cell and head. The injection depends only on the finite machine layout. -/
namespace IntegerMultBounds.Machine.TwoTapeAt
noncomputable section
open SharedPlacementAlphabet (setTape)
variable {t q states cost : ℕ}

def slots (i j : Fin t) : Fin 2 → Fin t := ![i,j]

theorem injective (i j : Fin t) (hij : i≠j) : Function.Injective (slots i j) := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp [slots] at hab ⊢
  · exact hij hab
  · exact hij hab.symm

def placement (i j : Fin t) (hij : i≠j) : Fin (2+(t-2)) ≃ Fin t :=
  InjectivePlacement.placement (slots i j) (injective i j hij) (by
    have ht := Fintype.card_le_of_injective _ (injective i j hij)
    simp only [Fintype.card_fin] at ht
    omega)

def program (M : Program 2 states q) (i j : Fin t) (hij : i≠j) :=
  Placement.placed M (placement i j hij)

def result (v : Tapes t q) (i j : Fin t) (f g : ℤ → Fin (q+4)) (p r : ℤ) :=
  setTape (setTape v i f p) j g r

theorem runs (M : Program 2 states q) (i j : Fin t) (hij : i≠j) (v : Tapes t q)
    (f g f' g' : ℤ → Fin (q+4)) (p r p' r' : ℤ)
    (hi : v.tape i=f ∧ v.head i=p) (hj : v.tape j=g ∧ v.head j=r)
    (h : HoareTime M (fun w => w=Copy.tapes f g p r) (fun w => w=Copy.tapes f' g' p' r') cost) :
    HoareTime (program M i j hij) (fun w => w=v)
      (fun w => w=result v i j f' g' p' r') cost := by
  have ha : Placement.active (placement i j hij) v=Copy.tapes f g p r := by
    rw [placement,InjectivePlacement.active_bank]
    unfold Copy.tapes Copy.cfg Config.tapes
    congr 1 <;> funext z <;> fin_cases z <;> simp [slots,hi,hj]
  apply (Placement.hoare_at h (placement i j hij) v ha).consequence (fun _ h => h) ?_ le_rfl
  rintro w ⟨small,rfl,rfl⟩
  apply Placement.Tapes.ext'
  · intro k
    by_cases hki : k=i
    · subst k
      have hh := InjectivePlacement.replace_head_slot (slots i j) (injective i j hij)
        (show 2+(t-2)=t by have ht := Fintype.card_le_of_injective _ (injective i j hij); simp only [Fintype.card_fin] at ht; omega)
        v (Copy.tapes f' g' p' r') 0
      simpa [placement,slots,result,setTape,hij,Ne.symm hij,Copy.tapes,Copy.cfg,Config.tapes] using hh
    · by_cases hkj : k=j
      · subst k
        have hh := InjectivePlacement.replace_head_slot (slots i j) (injective i j hij)
          (show 2+(t-2)=t by have ht := Fintype.card_le_of_injective _ (injective i j hij); simp only [Fintype.card_fin] at ht; omega)
          v (Copy.tapes f' g' p' r') 1
        simpa [placement,slots,result,setTape,Copy.tapes,Copy.cfg,Config.tapes] using hh
      · rw [Placement.replace_head_other _ _ _ k (by intro z; fin_cases z <;> simp [placement,slots,Ne.symm hki,Ne.symm hkj])]
        simp [result,setTape,hki,hkj]
  · intro k
    by_cases hki : k=i
    · subst k
      have hh := InjectivePlacement.replace_tape_slot (slots i j) (injective i j hij)
        (show 2+(t-2)=t by have ht := Fintype.card_le_of_injective _ (injective i j hij); simp only [Fintype.card_fin] at ht; omega)
        v (Copy.tapes f' g' p' r') 0
      simpa [placement,slots,result,setTape,hij,Ne.symm hij,Copy.tapes,Copy.cfg,Config.tapes] using hh
    · by_cases hkj : k=j
      · subst k
        have hh := InjectivePlacement.replace_tape_slot (slots i j) (injective i j hij)
          (show 2+(t-2)=t by have ht := Fintype.card_le_of_injective _ (injective i j hij); simp only [Fintype.card_fin] at ht; omega)
          v (Copy.tapes f' g' p' r') 1
        simpa [placement,slots,result,setTape,Copy.tapes,Copy.cfg,Config.tapes] using hh
      · rw [Placement.replace_tape_other _ _ _ k (by intro z; fin_cases z <;> simp [placement,slots,Ne.symm hki,Ne.symm hkj])]
        simp [result,setTape,hki,hkj]

end
end IntegerMultBounds.Machine.TwoTapeAt
