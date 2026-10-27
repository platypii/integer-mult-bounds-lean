module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRowCoefficientHost
public import IntegerMultBounds.MathlibTM2.Mult.ChirpBankLoad
public import IntegerMultBounds.MathlibTM2.Fast.TableLoad

/-! # Initialize and load the coefficient table from ordinary unary headers -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def initializeRowCoefficientBank : Pr P₀ 117 Q A U :=
  chirpBankLoad rowCoefficientReg (fun _ => 106) 115 94

/-- All zero-valued table variables and both word counters are constructed. -/
theorem initializeRowCoefficientBank_exec (V W : ℕ) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hV : (S.R 115).length = V) (hW : (S.R 94).length = W) (hz : S.R 106 = [])
    (hblank : ∀ r, S.R (rowCoefficientReg r) = []) :
    ∃ v', v'.user = v.user ∧
      Exec body initializeRowCoefficientBank (mk v S) (304 * V + 4 * W + 409)
        (mk v' { S with R := chirpBankLoadR rowCoefficientReg (fun _ => 106) V W (fun _ => 0) S.R }) ∧
      tblHolds rowCoefficientReg { S with R := chirpBankLoadR rowCoefficientReg (fun _ => 106) V W (fun _ => 0) S.R }
        (tblRho V (List.replicate V tick) (List.replicate W tick) ⟨fun _ => 0, []⟩) := by
  have hoff (k : Fin 117) (hk : k ∉ rowCoefficientPorts) : ∀ r, rowCoefficientReg r ≠ k :=
    rowCoefficientReg_off k hk
  obtain ⟨v', hu, he⟩ := chirpBankLoad_exec (body := body) rowCoefficientReg rowCoefficientReg_injective
    (fun _ => 106) 115 94 (hoff 115 (by simp)) (hoff 94 (by simp))
    (fun _ => hoff 106 (by decide)) V W (fun _ => 0) (fun _ => 0) (by simp) (by simp)
    v S hV hW (by simpa [binSyms] using hz) hblank
  have hcost : chirpBankLoadCost rowCoefficientReg (fun _ : Fin 50 => 106) V W (fun _ => 0) =
      304 * V + 4 * W + 409 := by
    simp [chirpBankLoadCost, chirpBankCopiesCost, chirpBankInputAssignments,
      List.map_ofFn, Function.comp_def, List.ofFn_const]
    ring
  exact ⟨v', hu, he.cast hcost rfl,
    chirpBankLoad_holds rowCoefficientReg rowCoefficientReg_injective (fun _ => 106) V W (fun _ => 0) S hblank⟩

def loadRowCoefficientList : List (Fin 117 × Fin 50) → Pr P₀ 117 Q A U
  | [] => .act .done
  | (src, dst) :: rs => .seq (tblLoad1 rowCoefficientReg src dst) (loadRowCoefficientList rs)

def loadedRowCoefficientState (value : Fin 117 → ℕ) : List (Fin 117 × Fin 50) → TblSt 50 A → TblSt 50 A
  | [], st => st
  | (src, dst) :: rs, st => loadedRowCoefficientState value rs ⟨Function.update st.val dst (value src), st.acc⟩

def loadRowCoefficientListCost (V : ℕ) (value : Fin 117 → ℕ) (rs : List (Fin 117 × Fin 50)) : ℕ :=
  (rs.map (fun r => value r.1 * (4 * V + 10) + 6 * V + 10)).sum + 1

/-- A structural sequence of retained-header loads establishes the whole state. -/
theorem loadRowCoefficientList_exec (rs : List (Fin 117 × Fin 50))
    (hoff : ∀ r ∈ rs, ∀ k, rowCoefficientReg k ≠ r.1) (V W : ℕ) (value : Fin 117 → ℕ)
    (st : TblSt 50 A) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hsrc : ∀ r ∈ rs, (S.R r.1).length = value r.1)
    (hS : tblHolds rowCoefficientReg S (tblRho V (List.replicate V tick) (List.replicate W tick) st)) :
    ∃ v' S' m, v'.user = v.user ∧ m ≤ loadRowCoefficientListCost V value rs ∧
      Exec body (loadRowCoefficientList rs) (mk v S) m (mk v' S') ∧
      tblHolds rowCoefficientReg S' (tblRho V (List.replicate V tick) (List.replicate W tick)
        (loadedRowCoefficientState value rs st)) ∧ tblFr rowCoefficientReg S S' := by
  induction rs generalizing st v S with
  | nil =>
    refine ⟨v, S, 1, rfl, by simp [loadRowCoefficientListCost], ?_, hS, tblFr.refl S⟩
    exact Exec.act (body := body) .done (mk v S)
  | cons r rs ih =>
    obtain ⟨v₁, S₁, m₁, hu₁, hm₁, he₁, hS₁, hf₁⟩ := tbl_load1_runs (body := body)
      rowCoefficientReg_injective (List.replicate V tick) (List.replicate W tick) (by simp)
      (hoff r (by simp)) r.2 st (value r.1) v S (hsrc r (by simp)) hS
    obtain ⟨v₂, S₂, m₂, hu₂, hm₂, he₂, hS₂, hf₂⟩ := ih
      (fun r hr => hoff r (by simp [hr])) _ v₁ S₁ (by
        intro r hr
        rw [hf₁.2.2.2 _ (hoff r (by simp [hr]))]
        exact hsrc r (by simp [hr])) hS₁
    refine ⟨v₂, S₂, m₁ + m₂, hu₂.trans hu₁, ?_, Exec.seq he₁ he₂, hS₂, hf₁.trans hf₂⟩
    simp only [loadRowCoefficientListCost, List.map_cons, List.sum_cons] at hm₂ ⊢
    omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
