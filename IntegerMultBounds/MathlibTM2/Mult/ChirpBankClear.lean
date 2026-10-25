module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpBankLoad
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! # Release an initialized table bank after its caller returns

Only variables and the two length headers are owned live words. The table-machine
contract already restores the accumulator and arithmetic scratch to empty.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.TableVM

variable {T Q A n : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def chirpBankClear (rg : TblR n → Fin T) : Pr P T Q A U :=
  .seq (clearWords (List.ofFn fun i => rg (.v i))) (clearWords [rg .wr, rg .wn])

def chirpBankClearR (rg : TblR n → Fin T) (R : Fin T → List (Fin (A + 4))) : Fin T → List (Fin (A + 4)) :=
  fun k => if k ∈ [rg .wr, rg .wn] then [] else
    if k ∈ (List.ofFn fun i => rg (.v i)) then [] else R k

/-- Cleanup charges every initialized binary symbol and counter tick exactly once. -/
theorem chirpBankClear_exec (rg : TblR n → Fin T) (hrg : Function.Injective rg)
    (W e : ℕ) (wl nl : List (Fin (A + 4))) (hwl : wl.length = W) (hnl : nl.length = e)
    (st : TblSt n A) (v : HS T Q A U) (S : Stacks T A)
    (hS : tblHolds rg S (tblRho W wl nl st)) :
    ∃ v', v'.user = v.user ∧
      Exec body (chirpBankClear rg) (mk v S) (2 * (n * W) + 2 * n + 1 + (2 * (W + e) + 5))
        (mk v' { S with R := chirpBankClearR rg S.R }) := by
  let vars := List.ofFn fun i => rg (.v i)
  have hnd : vars.Nodup := List.nodup_ofFn.mpr (fun i j h => TblR.v.inj (hrg h))
  obtain ⟨v₁, hu₁, he₁⟩ := clearWords_exec (body := body) vars hnd v S
  let S₁ : Stacks T A := { S with R := fun k => if k ∈ vars then [] else S.R k }
  have hlen (i : Fin n) : (S.R (rg (.v i))).length = W := by rw [hS (.v i)]; simp
  have hsum : (vars.map fun k => (S.R k).length).sum = n * W := by
    simp only [vars, List.map_ofFn, Function.comp_def, hlen]
    simp
  have hwr : S₁.R (rg .wr) = wl := by
    have hnot : rg .wr ∉ vars := by simp [vars, List.mem_ofFn, hrg.eq_iff]
    simpa only [S₁, ite_eq_right hnot, tblRho] using hS .wr
  have hwn : S₁.R (rg .wn) = nl := by
    have hnot : rg .wn ∉ vars := by simp [vars, List.mem_ofFn, hrg.eq_iff]
    simpa only [S₁, ite_eq_right hnot, tblRho] using hS .wn
  obtain ⟨v₂, hu₂, he₂⟩ := clearWords_exec (body := body) [rg .wr, rg .wn]
    (by simp [hrg.eq_iff]) v₁ S₁
  rw [hsum, show vars.length = n by simp [vars]] at he₁
  have hcost : 2 * ([rg .wr, rg .wn].map fun k => (S₁.R k).length).sum + 2 * [rg .wr, rg .wn].length + 1 =
      2 * (W + e) + 5 := by simp [hwr, hwn, hwl, hnl]
  rw [hcost] at he₂
  exact ⟨v₂, hu₂.trans hu₁, Exec.seq he₁ he₂⟩

/-- All table roles are empty after cleanup when the evaluator restored its accumulator. -/
theorem chirpBankClear_empty (rg : TblR n → Fin T) (hrg : Function.Injective rg)
    (W : ℕ) (wl nl : List (Fin (A + 4))) (st : TblSt n A) (S : Stacks T A)
    (hS : tblHolds rg S (tblRho W wl nl st)) (hacc : st.acc = []) :
    ∀ r, chirpBankClearR rg S.R (rg r) = [] := by
  intro r
  cases r with
  | v i => simp [chirpBankClearR, List.mem_ofFn, hrg.eq_iff]
  | wr => simp [chirpBankClearR]
  | wn => simp [chirpBankClearR]
  | acc =>
    have hzero : S.R (rg .acc) = [] := (hS .acc).trans hacc
    simpa [chirpBankClearR, List.mem_ofFn, hrg.eq_iff] using hzero
  | z i =>
    have hzero : S.R (rg (.z i)) = [] := hS (.z i)
    simpa [chirpBankClearR, List.mem_ofFn, hrg.eq_iff] using hzero

/-- Loading and releasing a fresh bank restores the entire register function. -/
theorem chirpBankClear_load (rg : TblR n → Fin T)
    (input : Fin n → Fin T) (W e : ℕ) (value : Fin T → ℕ)
    (S : Stacks T A) (hblank : ∀ r, S.R (rg r) = []) :
    chirpBankClearR rg (chirpBankLoadR rg input W e value S.R) = S.R := by
  funext k
  by_cases hh : k ∈ [rg .wr, rg .wn]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
    rcases hh with rfl | rfl <;> simp [chirpBankClearR, hblank]
  by_cases hv : k ∈ (List.ofFn fun i => rg (.v i))
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
    simp [chirpBankClearR, List.mem_ofFn, hblank]
  · have ho : ∀ p ∈ chirpBankInputAssignments rg input, p.2 ≠ k := by
      intro p hp
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
      intro h
      exact hv (List.mem_ofFn.mpr ⟨i, h⟩)
    have hw : k ≠ rg .wr := by intro h; exact hh (by simp [h])
    have hn : k ≠ rg .wn := by intro h; exact hh (by simp [h])
    simp only [chirpBankClearR, ite_eq_right hh, ite_eq_right hv, chirpBankLoadR]
    rw [chirpBankCopiesR_off _ _ _ _ _ ho]
    simp only [Function.update_of_ne hn, Function.update_of_ne hw]

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
