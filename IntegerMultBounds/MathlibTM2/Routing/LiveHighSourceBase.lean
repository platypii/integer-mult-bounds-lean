module

public import IntegerMultBounds.MathlibTM2.Routing.LiveSelectedSourceLayout

/-! Generate rho + n*K in outer tape 5, preserving the live count, stride,
region offset and all arithmetic scratch. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
noncomputable section
local notation "T₀" => liveInactiveProfileT repairT 11
local notation "e₀" => liveInactiveProfileCore (N := repairT) (J := 11)

def liveHighSourceBaseRole : Fin 11 → LiveDescriptorRole 11 :=
  ![.archive, .stride 1, .coordinate .entry, .base 0, .archive,
    .profile (.coordinate (.arithmetic .muls)), .profile (.coordinate (.arithmetic .mult)),
    .profile (.coordinate (.arithmetic .tx)), .profile (.coordinate (.arithmetic .ty)),
    .profile (.coordinate (.arithmetic .tz)), .profile .loadTmp]

def liveHighSourceBaseReg (r : Fin 11) : Fin T₀ :=
  if r = 0 then liveInactiveProfileAux 0 else
  if r = 4 then liveInactiveProfileAux 5 else e₀ (liveDescriptorAux (liveHighSourceBaseRole r))

theorem liveHighSourceBaseReg_injective : Function.Injective liveHighSourceBaseReg := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [liveHighSourceBaseReg, liveHighSourceBaseRole,
      liveInactiveProfileAux_injective.eq_iff, liveInactiveProfileAux_core,
      liveInactiveProfileCore_aux, liveInactiveProfileCore_injective.eq_iff,
      liveDescriptorAux_injective.eq_iff]

variable {Q A : ℕ} {P U : Type}

def liveHighSourceBaseProgram : Pr P T₀ Q A U :=
  binaryAffinePositionProgram (liveHighSourceBaseReg 0) (liveHighSourceBaseReg 1)
    (liveHighSourceBaseReg 2) (liveHighSourceBaseReg 3) (liveHighSourceBaseReg 4)
    (liveHighSourceBaseReg 5) (liveHighSourceBaseReg 6) (liveHighSourceBaseReg 7)
    (liveHighSourceBaseReg 8) (liveHighSourceBaseReg 9) (liveHighSourceBaseReg 10)

theorem liveHighSourceBase_exec (body : P → Pr P T₀ Q A U)
    (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) (w : LiveDescriptorWidths)
    (hn : p.n < 2 ^ w.indexBits) (hk : p.K < 2 ^ w.strideBits)
    (hfit : p.ρ + p.n * p.K < 2 ^ w.coordinateBits)
    (v : HS T₀ Q A U) (S : Stacks T₀ A)
    (hbank : ∀ r, (∀ j : Fin 11, r ≠ .input j) →
      S.R (e₀ (liveDescriptorAux r)) = liveDescriptorData p X hG hK active s repairLiveMode w r)
    (hcount : S.R (liveInactiveProfileAux 0) = binSyms w.indexBits p.n)
    (houtput : S.R (liveInactiveProfileAux 5) = []) :
    ∃ (v' : HS T₀ Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ w.indexBits * (12 * w.coordinateBits + 20) + 26 * w.coordinateBits + 34 ∧
      Exec body liveHighSourceBaseProgram (mk v S) steps
        (mk v' { S with R := Function.update S.R (liveInactiveProfileAux 5) (binSyms w.coordinateBits (p.ρ + p.n * p.K)) }) := by
  have hr (r : Fin 11) : S.R (e₀ (liveDescriptorAux (liveHighSourceBaseRole r))) =
      liveDescriptorData p X hG hK active s repairLiveMode w (liveHighSourceBaseRole r) :=
    hbank _ (by intro j; fin_cases r <;> simp [liveHighSourceBaseRole])
  have hb (r : Fin 11) (h0 : r ≠ 0) (h1 : r ≠ 1) (h3 : r ≠ 3) (h4 : r ≠ 4) :
      S.R (liveHighSourceBaseReg r) = [] := by
    fin_cases r <;> simp_all [liveHighSourceBaseReg, liveHighSourceBaseRole, liveDescriptorData]
  have hi := liveHighSourceBaseReg_injective
  obtain ⟨v', steps, hu, ht, hx⟩ := binaryAffinePosition_exec body
    (liveHighSourceBaseReg 0) (liveHighSourceBaseReg 1) (liveHighSourceBaseReg 2)
    (liveHighSourceBaseReg 3) (liveHighSourceBaseReg 4) (liveHighSourceBaseReg 5)
    (liveHighSourceBaseReg 6) (liveHighSourceBaseReg 7) (liveHighSourceBaseReg 8)
    (liveHighSourceBaseReg 9) (liveHighSourceBaseReg 10)
    (by simp [List.nodup_cons, hi.eq_iff]) (hi.ne (by decide)) (hi.ne (by decide)) (hi.ne (by decide))
    w.indexBits w.strideBits p.n p.K p.ρ hn hk (by simpa [Nat.add_comm, LiveDescriptorWidths.coordinateBits] using hfit) v S
    (by simpa [liveHighSourceBaseReg] using hcount)
    (by simpa [liveHighSourceBaseReg, liveHighSourceBaseRole] using
      (hr 1).trans (selectedSourceStride p X hG hK active s w))
    (by simpa [liveHighSourceBaseReg, liveHighSourceBaseRole, LiveDescriptorWidths.coordinateBits] using
      (hr 3).trans (selectedSourceBase_rho p X hG hK active s w))
    (hb 2 (by decide) (by decide) (by decide) (by decide))
    (by simpa [liveHighSourceBaseReg] using houtput)
    (hb 5 (by decide) (by decide) (by decide) (by decide))
    (hb 6 (by decide) (by decide) (by decide) (by decide))
    (hb 7 (by decide) (by decide) (by decide) (by decide))
    (hb 8 (by decide) (by decide) (by decide) (by decide))
    (hb 9 (by decide) (by decide) (by decide) (by decide))
  have hd : liveHighSourceBaseReg 4 = liveInactiveProfileAux 5 := by simp [liveHighSourceBaseReg]
  rw [hd] at hx
  rw [show p.n * p.K + p.ρ = p.ρ + p.n * p.K by omega] at hx
  change Exec body liveHighSourceBaseProgram (mk v S) steps
    (mk v' { S with R := Function.update S.R (liveInactiveProfileAux 5) (binSyms w.coordinateBits (p.ρ + p.n * p.K)) }) at hx
  exact ⟨v', steps, hu, ht, hx⟩

end
end IntegerMultBounds.MathlibTM2.Routing
