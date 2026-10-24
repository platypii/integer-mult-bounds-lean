module

public import IntegerMultBounds.MathlibTM2.Routing.ReservoirMetadataGenerate

/-! Extend the exchange-operand bank with the surviving middle dimension.
The subtraction reuses the already computed `n - 2*w`, avoiding another multiplier. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def reservoirProductionScalarsProgram (rg : Fin 22 → Fin T) : Pr P T Q A U :=
  .seq (reservoirExchangeOperandsProgram rg)
    (bsub (rg 4) (rg 2) (rg 14) (rg 10) (rg 11) (rg 12) (rg 13))

theorem reservoirProductionScalars_exec (body : P → Pr P T Q A U)
    (rg : Fin 22 → Fin T) (hrg : Function.Injective rg) (L n H w : ℕ)
    (hn : n < 2 ^ L) (hfit : 9 * H ≤ n) (hw : w ≤ H)
    (v : HS T Q A U) (S : Stacks T A)
    (hdimension : S.R (rg 0) = binSyms L n) (hreservoir : S.R (rg 1) = binSyms L H)
    (hspan : S.R (rg 2) = binSyms L w)
    (hblank : ∀ j : Fin 22, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 13 → j ≠ 18 → S.R (rg j) = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (reservoirProductionScalarsProgram rg) (mk v S) (90 * L + 102)
        (mk v' { S with R := (Function.update (reservoirExchangeOperandBank S.R rg L n H w)
          (rg 14) (binSyms L (n - 3 * w))) }) := by
  obtain ⟨v₁, hu₁, he₁⟩ := reservoirExchangeOperands_exec body rg hrg L n H w hn hfit hw v S
    hdimension hreservoir hspan hblank
  let B : Stacks T A := { S with R := reservoirExchangeOperandBank S.R rg L n H w }
  have read (j : Fin 22) := reservoirExchangeOperandBank_read S.R rg hrg L n H w j
  obtain ⟨v₂, hu₂, _, _, he₂⟩ := bsub_exec (body := body)
    (a := rg 4) (b := rg 2) (c := rg 14) (tx := rg 10) (ty := rg 11) (tz := rg 12) (cy := rg 13)
    (by simp [List.nodup_cons, hrg.eq_iff]) (hrg.ne (by decide)) (hrg.ne (by decide))
    ((Nat.sub_le n (2 * w)).trans_lt hn) (by omega : w < 2 ^ L) v₁ B
    (read 4) ((read 2).trans hspan)
    ((read 10).trans (hblank 10 (by decide) (by decide) (by decide) (by decide) (by decide)))
    ((read 11).trans (hblank 11 (by decide) (by decide) (by decide) (by decide) (by decide)))
    ((read 12).trans (hblank 12 (by decide) (by decide) (by decide) (by decide) (by decide)))
  have hsub : (n - 2 * w + 2 ^ L - w) % 2 ^ L = n - 3 * w := by
    have he : n - 2 * w + 2 ^ L - w = (n - 3 * w) + 2 ^ L := by omega
    rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt ((Nat.sub_le n (3 * w)).trans_lt hn)]
  have hdst : B.R (rg 14) = [] :=
    (read 14).trans (hblank 14 (by decide) (by decide) (by decide) (by decide) (by decide))
  rw [hsub, hdst, List.append_nil] at he₂
  exact ⟨v₂, hu₂.trans hu₁, (Exec.seq he₁ he₂).cast (by ring) rfl⟩

/-- Clear the surviving dimension together with the exchange operands. -/
theorem reservoirProductionScalars_clean
    (R : Fin T → List (Fin (A + 4))) (rg : Fin 22 → Fin T)
    (hrg : Function.Injective rg) (L n H w : ℕ)
    (hblank : ∀ j ∈ (14 : Fin 22) :: reservoirOperandTargets, R (rg j) = []) :
    metadataCleared (Function.update (reservoirExchangeOperandBank R rg L n H w)
      (rg 14) (binSyms L (n - 3 * w)))
      (rg 14 :: reservoirOperandTargets.map rg) = R := by
  rw [metadataCleared, metadataCleared_update _ _ _ _
    (by simp [reservoirOperandTargets, hrg.eq_iff]),
    reservoirExchangeOperandBank_clean R rg hrg L n H w
      (fun j hj => hblank j (List.mem_cons_of_mem 14 hj)), Function.update_idem]
  have h14 : R (rg 14) = [] := hblank 14 (by simp)
  rw [← h14]
  exact Function.update_eq_self _ _

end IntegerMultBounds.MathlibTM2.Routing
