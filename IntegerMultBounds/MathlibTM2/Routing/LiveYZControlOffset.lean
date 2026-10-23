module

public import IntegerMultBounds.MathlibTM2.Routing.LiveZSourceGenerate

/-! Form the YZ control-source base from existing target and control row counts.
The sum occupies one outer scratch tape; both input widths are restored. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section
variable {Q A : ℕ} {P U : Type}

local notation "T₀" => liveInactiveProfileT repairT 11
local notation "e₀" => liveInactiveProfileCore (N := repairT) (J := 11)

def liveYZControlOffsetReg : Fin 7 → Fin T₀ :=
  ![e₀ (liveDescriptorAux (.rows 3)), e₀ (liveDescriptorAux (.rows 5)), liveInactiveProfileAux 6,
    liveZSourceReg 8, liveZSourceReg 9, liveZSourceReg 10, liveZSourceReg 11]

theorem liveYZControlOffsetReg_injective : Function.Injective liveYZControlOffsetReg := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [liveYZControlOffsetReg, liveZSourceReg, liveZSourceRole,
      liveInactiveProfileCore_injective.eq_iff, liveDescriptorAux_injective.eq_iff,
      liveInactiveProfileCore_aux, liveInactiveProfileAux_core]

def liveYZControlOffsetProgram : Pr P T₀ Q A U :=
  badd (liveYZControlOffsetReg 0) (liveYZControlOffsetReg 1) (liveYZControlOffsetReg 2)
    (liveYZControlOffsetReg 3) (liveYZControlOffsetReg 4) (liveYZControlOffsetReg 5) (liveYZControlOffsetReg 6)

theorem liveYZControlOffset_exec (body : P → Pr P T₀ Q A U)
    (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) (w : LiveDescriptorWidths)
    (v : HS T₀ Q A U) (S : Stacks T₀ A)
    (hfit : ∀ j, LiveDescriptorBounds p X w (repairLiveMode j))
    (hwidth : w.selectorBits = w.coordinateBits)
    (hbank : ∀ r, (∀ j : Fin 11, r ≠ .input j) →
      S.R (e₀ (liveDescriptorAux r)) = liveDescriptorData p X hG hK active s repairLiveMode w r)
    (hblank : S.R (liveInactiveProfileAux 6) = []) :
    ∃ v', v'.user = v.user ∧
      Exec body liveYZControlOffsetProgram (mk v S) (8 * w.coordinateBits + 8)
        (mk v' { S with R := Function.update S.R (liveInactiveProfileAux 6) (binSyms w.coordinateBits (p.wy + p.wc)) }) := by
  have hsum : p.wy + p.wc < 2 ^ w.coordinateBits := by
    have h := (hfit 7).source_fits
    rw [hwidth] at h
    change p.wy + 2 * p.wc + X + 1 < 2 ^ w.coordinateBits at h
    omega
  have ha : S.R (liveYZControlOffsetReg 0) = binSyms w.coordinateBits p.wy :=
    hbank (.rows 3) (by intro j; simp)
  have hb : S.R (liveYZControlOffsetReg 1) = binSyms w.coordinateBits p.wc :=
    hbank (.rows 5) (by intro j; simp)
  have hs (r : Fin 3) : S.R (liveYZControlOffsetReg ⟨3 + r.val, by omega⟩) = [] := by
    fin_cases r <;>
      dsimp only [liveYZControlOffsetReg, liveZSourceReg, liveZSourceRole,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ,
        Nat.reduceAdd, Fin.val_zero, Fin.val_one] <;>
      exact hbank _ (by intro j; simp)
  have hinj := liveYZControlOffsetReg_injective
  obtain ⟨v', hu, _, _, hx⟩ := badd_exec body
    (a := liveYZControlOffsetReg 0) (b := liveYZControlOffsetReg 1) (c := liveYZControlOffsetReg 2)
    (tx := liveYZControlOffsetReg 3) (ty := liveYZControlOffsetReg 4)
    (tz := liveYZControlOffsetReg 5) (cy := liveYZControlOffsetReg 6)
    (by simp [List.nodup_cons, hinj.eq_iff]) (hinj.ne (by decide)) (hinj.ne (by decide))
    (by omega : p.wy < 2 ^ w.coordinateBits) (by omega : p.wc < 2 ^ w.coordinateBits)
    v S ha hb (hs 0) (hs 1) (hs 2)
  rw [Nat.mod_eq_of_lt hsum] at hx
  have hd : liveYZControlOffsetReg 2 = liveInactiveProfileAux 6 := by
    simp [liveYZControlOffsetReg]
  rw [hd, hblank, List.append_nil] at hx
  refine ⟨v', hu, ?_⟩
  simpa only [liveYZControlOffsetProgram, hd] using hx

end
end IntegerMultBounds.MathlibTM2.Routing
