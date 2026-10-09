import IntegerMultBounds.Machine.CompactGadgetReservationHeadersCarvedBudget

/-! Physical placement of the original-array pad/split/erase machine inside
the same header/spectator/private bank consumed by the carved load. -/
namespace IntegerMultBounds.Machine.CompactGadgetReservationHeadersCarvedReservationRouting
noncomputable section
variable {s h t u w₁ w₂ a q : ℕ}

abbrev Total (s h t u w₁ w₂ : ℕ) := ((h+((s+t)+u))+w₁)+w₂
abbrev Extra (h t u w₁ w₂ : ℕ) := h+t+u+w₁+w₂

def slot (i : Fin s) : Fin (Total s h t u w₁ w₂) :=
  Fin.castAdd w₂ (Fin.castAdd w₁ (Fin.natAdd h (Fin.castAdd u (Fin.castAdd t i))))
theorem slot_injective : Function.Injective (slot (s := s) (h := h) (t := t) (u := u) (w₁ := w₁) (w₂ := w₂)) := by
  intro i j he
  exact Fin.castAdd_injective _ _ (Fin.castAdd_injective _ _
    (Fin.natAdd_injective _ _ (Fin.castAdd_injective _ _ (Fin.castAdd_injective _ _ he))))
def placement (s h t u w₁ w₂ : ℕ) :
    Fin (s+Extra h t u w₁ w₂) ≃ Fin (Total s h t u w₁ w₂) :=
  InjectivePlacement.placement slot slot_injective (by unfold Extra Total; omega)

def bank (frontBank : Tapes h a) (small : Tapes s a) (left : Tapes t a) (right : Tapes u a) :
    Tapes (Total s h t u w₁ w₂) a :=
  ((frontBank.append ((small.append left).append right)).append (SharedBank.empty w₁ a)).append
    (SharedBank.empty w₂ a)

theorem active (frontBank : Tapes h a) (small : Tapes s a) (left : Tapes t a) (right : Tapes u a) :
    Placement.active (placement s h t u w₁ w₂) (bank (w₁ := w₁) (w₂ := w₂) frontBank small left right) = small := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals simp only [placement,InjectivePlacement.active_slot,slot,bank,
    Tapes.append,Fin.addCases_left,Fin.addCases_right]

theorem frame (frontBank : Tapes h a) (small small' : Tapes s a) (left : Tapes t a) (right : Tapes u a)
    (z : Fin (Total s h t u w₁ w₂)) (hn : ¬∃ i : Fin s, slot i = z) :
    (bank (w₁ := w₁) (w₂ := w₂) frontBank small left right).head z =
      (bank (w₁ := w₁) (w₂ := w₂) frontBank small' left right).head z ∧
    (bank (w₁ := w₁) (w₂ := w₂) frontBank small left right).tape z =
      (bank (w₁ := w₁) (w₂ := w₂) frontBank small' left right).tape z := by
  induction z using (Fin.addCases (m := (h+((s+t)+u))+w₁) (n := w₂)) with
  | right i => simp only [bank,Tapes.append,Fin.addCases_right,and_self]
  | left z =>
    induction z using (Fin.addCases (m := h+((s+t)+u)) (n := w₁)) with
    | right i => simp only [bank,Tapes.append,Fin.addCases_left,Fin.addCases_right,and_self]
    | left z =>
      induction z using (Fin.addCases (m := h) (n := (s+t)+u)) with
      | left i => simp only [bank,Tapes.append,Fin.addCases_left,and_self]
      | right z =>
        induction z using (Fin.addCases (m := s+t) (n := u)) with
        | right i => simp only [bank,Tapes.append,Fin.addCases_left,Fin.addCases_right,and_self]
        | left z =>
          induction z using (Fin.addCases (m := s) (n := t)) with
          | right i => simp only [bank,Tapes.append,Fin.addCases_left,Fin.addCases_right,and_self]
          | left i => exact (hn ⟨i,rfl⟩).elim

theorem extra (frontBank : Tapes h a) (small small' : Tapes s a) (left : Tapes t a) (right : Tapes u a) :
    Placement.extra (placement s h t u w₁ w₂) (bank (w₁ := w₁) (w₂ := w₂) frontBank small left right) =
    Placement.extra (placement s h t u w₁ w₂) (bank (w₁ := w₁) (w₂ := w₂) frontBank small' left right) := by
  have hn (j : Fin (Extra h t u w₁ w₂)) :
      ¬∃ i : Fin s, slot i = placement s h t u w₁ w₂ (Fin.natAdd s j) := by
    rintro ⟨i,hi⟩
    have he : placement s h t u w₁ w₂ (Fin.castAdd (Extra h t u w₁ w₂) i) =
        placement s h t u w₁ w₂ (Fin.natAdd s j) := by
      simpa only [placement,InjectivePlacement.active_slot] using hi
    have hv := congrArg Fin.val ((placement s h t u w₁ w₂).injective he)
    simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
    omega
  apply congrArg₂ Tapes.mk <;> funext j
  · exact (frame frontBank small small' left right _ (hn j)).1
  · exact (frame frontBank small small' left right _ (hn j)).2

def program (M : Program s q a) (h t u w₁ w₂ : ℕ) := Placement.placed M (placement s h t u w₁ w₂)

theorem realizes (M : Program s q a) (frontBank : Tapes h a) (small small' : Tapes s a)
    (left : Tapes t a) (right : Tapes u a) (C : ℕ)
    (hr : HoareTime M (fun v => v = small) (fun v => v = small') C) :
    HoareTime (program M h t u w₁ w₂)
      (fun v => v = bank (w₁ := w₁) (w₂ := w₂) frontBank small left right)
      (fun v => v = bank (w₁ := w₁) (w₂ := w₂) frontBank small' left right) C := by
  have hh := Placement.hoare_at hr (placement s h t u w₁ w₂)
    (bank (w₁ := w₁) (w₂ := w₂) frontBank small left right) (active _ _ _ _)
  refine hh.consequence (fun _ h => h) ?_ le_rfl
  rintro v ⟨smallOut,hsmall,rfl⟩
  subst smallOut
  rw [Placement.replace,extra frontBank small small' left right]
  simpa only [active] using Placement.view (placement s h t u w₁ w₂)
    (bank (w₁ := w₁) (w₂ := w₂) frontBank small' left right)

end
end IntegerMultBounds.Machine.CompactGadgetReservationHeadersCarvedReservationRouting
