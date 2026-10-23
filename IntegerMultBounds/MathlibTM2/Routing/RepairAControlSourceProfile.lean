module

public import IntegerMultBounds.MathlibTM2.Routing.RepairZSourceProfile

/-! The first A source stream repeats one activity-gated control selector per
control group. This separates group repetition from selector arithmetic. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section
variable {A : ℕ}

theorem repairAControlSourceProfile (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) :
    affineSourceProfile (repairRotationSources p X hG hK active s .A 0) =
      (List.ofFn (fun c : Fin p.n => List.replicate p.G
        (active c, if active c then c.val * p.G + p.wc else 0))).flatten := by
  unfold affineSourceProfile
  dsimp only [repairRotationSlots]
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext c
  rw [← List.ofFn_const]
  apply congrArg List.ofFn
  funext j
  have hdiv : (c.val * p.G + j.val) / p.G = c.val := by
    rw [Nat.add_div_of_dvd_right (by simp)]
    simp [hG.ne', Nat.div_eq_of_lt j.isLt]
  have hc : controlIndex p hG ⟨c.val * p.G + j.val, by
      calc
        c.val * p.G + j.val < (c.val + 1) * p.G :=
          (Nat.add_lt_add_left j.isLt _).trans_eq (by rw [Nat.add_mul, Nat.one_mul])
        _ ≤ p.n * p.G := Nat.mul_le_mul_right _ c.isLt⟩ = c := by
    apply Fin.ext
    exact hdiv
  simp only [repairRotationSources, aSources, Matrix.cons_val_zero]
  rw [hc]
  cases active c <;> simp [controlWire, posC, Option.elim, Nat.add_comm]

theorem repairAControlSourceProfile_frames (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) (L : ℕ) :
    (LiveDescriptorMode.ofKey (some (.A, 0))).profileFrames (A := A) p X hG hK active s L =
      affineProfileFrames L ((List.ofFn (fun c : Fin p.n => List.replicate p.G
        (active c, if active c then c.val * p.G + p.wc else 0))).flatten) :=
  congrArg (affineProfileFrames L) (repairAControlSourceProfile p X hG hK active s)

end
end IntegerMultBounds.MathlibTM2.Routing
