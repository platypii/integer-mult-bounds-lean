module

public import IntegerMultBounds.MathlibTM2.Routing.ReservoirBankPrepare

/-! Erase exactly the eight generated converter inputs after use. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def reservoirBankTargets (rg : Fin 29 → Fin T) : List (Fin T) :=
  [rg 18, rg 28, rg 22, rg 23, rg 24, rg 25, rg 26, rg 27]

theorem reservoirBankPrepared_read
    (R : Fin T → List (Fin (A + 4))) (rg : Fin 29 → Fin T) (hrg : Function.Injective rg)
    (n H : ℕ) (hfit : 9 * H ≤ n) (w : ℕ) (hw : w ≤ H) (k : Fin 3) (L : ℕ) (j : Fin 29) :
    reservoirBankPrepared R rg n H hfit w hw k L (rg j) =
      if j = 18 then middleLookupMetadata n H hfit w hw k L false ++ R (rg 18)
      else if j = 28 then middleLookupMetadata n H hfit w hw k L true ++ R (rg 28)
      else if j = 22 ∨ j = 23 then binSyms L 0
      else if j = 24 then binSyms L w
      else if j = 25 then binSyms L (n - 3 * w)
      else if j = 26 then binSyms L (3 * H)
      else if j = 27 then binSyms L (6 * H)
      else R (rg j) := by
  fin_cases j <;> simp [reservoirBankPrepared, reservoirScalarOutputs, reservoirBankScalarSlot, hrg.eq_iff]

theorem reservoirBankPrepared_keep
    (R : Fin T → List (Fin (A + 4))) (rg : Fin 29 → Fin T)
    (n H : ℕ) (hfit : 9 * H ≤ n) (w : ℕ) (hw : w ≤ H) (k : Fin 3) (L : ℕ)
    (x : Fin T) (hx : x ∉ reservoirBankTargets rg) :
    reservoirBankPrepared R rg n H hfit w hw k L x = R x := by
  simp only [reservoirBankTargets, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
  simp [reservoirBankPrepared, reservoirScalarOutputs, Function.comp_apply, reservoirBankScalarSlot,
    hx.1, hx.2.1,
    hx.2.2.1, hx.2.2.2.1,
    hx.2.2.2.2.1, hx.2.2.2.2.2.1,
    hx.2.2.2.2.2.2.1, hx.2.2.2.2.2.2.2]

theorem reservoirBankPrepared_clean
    (R : Fin T → List (Fin (A + 4))) (rg : Fin 29 → Fin T)
    (n H : ℕ) (hfit : 9 * H ≤ n) (w : ℕ) (hw : w ≤ H) (k : Fin 3) (L : ℕ)
    (hblank : ∀ x ∈ reservoirBankTargets rg, R x = []) :
    metadataCleared (reservoirBankPrepared R rg n H hfit w hw k L) (reservoirBankTargets rg) = R := by
  funext x
  by_cases hx : x ∈ reservoirBankTargets rg
  · rw [metadataCleared_at _ _ _ hx]
    exact (hblank x hx).symm
  · rw [metadataCleared_keep _ _ _ hx, reservoirBankPrepared_keep R rg n H hfit w hw k L x hx]

theorem reservoirBankPrepared_cleanCost
    (R : Fin T → List (Fin (A + 4))) (rg : Fin 29 → Fin T) (hrg : Function.Injective rg)
    (n H : ℕ) (hfit : 9 * H ≤ n) (w : ℕ) (hw : w ≤ H) (k : Fin 3) (L : ℕ)
    (hf : R (rg 18) = []) (hb : R (rg 28) = []) :
    metadataCleanCost (reservoirBankPrepared R rg n H hfit w hw k L) (reservoirBankTargets rg) =
      60 * L + 65 := by
  simp only [reservoirBankTargets, metadataCleanCost]
  simp [reservoirBankPrepared_read R rg hrg, hf, hb, List.append_nil,
    middleLookupMetadata_length, length_binSyms]
  ring

theorem reservoirBankClean_exec (body : P → Pr P T Q A U)
    (R : Fin T → List (Fin (A + 4))) (rg : Fin 29 → Fin T) (hrg : Function.Injective rg)
    (n H : ℕ) (hfit : 9 * H ≤ n) (w : ℕ) (hw : w ≤ H) (k : Fin 3) (L : ℕ)
    (hblank : ∀ x ∈ reservoirBankTargets rg, R x = [])
    (v : HS T Q A U) (S : Stacks T A)
    (hbank : S.R = reservoirBankPrepared R rg n H hfit w hw k L) :
    ∃ v', v'.user = v.user ∧
      Exec body (metadataClean (reservoirBankTargets rg)) (mk v S) (60 * L + 65)
        (mk v' { S with R := R }) := by
  obtain ⟨v', hu, he⟩ := metadataClean_exec body (reservoirBankTargets rg)
    (by simp [reservoirBankTargets, List.nodup_cons, hrg.eq_iff]) v S
  rw [hbank, reservoirBankPrepared_clean R rg n H hfit w hw k L hblank,
    reservoirBankPrepared_cleanCost R rg hrg n H hfit w hw k L
      (hblank _ (by simp [reservoirBankTargets])) (hblank _ (by simp [reservoirBankTargets]))] at he
  exact ⟨v', hu, he⟩

end IntegerMultBounds.MathlibTM2.Routing
