module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoefficientHost
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

def initializeCoefficientBank : Pr P₀ 117 Q A U :=
  chirpBankLoad coefficientReg (fun _ => 106) 115 94

/-- All zero-valued table variables and both word counters are constructed. -/
theorem initializeCoefficientBank_exec (V W : ℕ) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hV : (S.R 115).length = V) (hW : (S.R 94).length = W) (hz : S.R 106 = [])
    (hblank : ∀ r, S.R (coefficientReg r) = []) :
    ∃ v', v'.user = v.user ∧
      Exec body initializeCoefficientBank (mk v S) (292 * V + 4 * W + 393)
        (mk v' { S with R := chirpBankLoadR coefficientReg (fun _ => 106) V W (fun _ => 0) S.R }) ∧
      tblHolds coefficientReg { S with R := chirpBankLoadR coefficientReg (fun _ => 106) V W (fun _ => 0) S.R }
        (tblRho V (List.replicate V tick) (List.replicate W tick) ⟨fun _ => 0, []⟩) := by
  have hoff (k : Fin 117) (hk : 63 ≤ k.val) : ∀ r, coefficientReg r ≠ k := by
    intro r he
    have hr := coefficientReg_range r
    rw [he] at hr
    omega
  obtain ⟨v', hu, he⟩ := chirpBankLoad_exec (body := body) coefficientReg coefficientReg_injective
    (fun _ => 106) 115 94 (hoff 115 (by decide)) (hoff 94 (by decide))
    (fun _ => hoff 106 (by decide)) V W (fun _ => 0) (fun _ => 0) (by simp) (by simp)
    v S hV hW (by simpa [binSyms] using hz) hblank
  have hcost : chirpBankLoadCost coefficientReg (fun _ : Fin 48 => 106) V W (fun _ => 0) =
      292 * V + 4 * W + 393 := by
    simp [chirpBankLoadCost, chirpBankCopiesCost, chirpBankInputAssignments,
      List.map_ofFn, Function.comp_def, List.ofFn_const]
    ring
  exact ⟨v', hu, he.cast hcost rfl,
    chirpBankLoad_holds coefficientReg coefficientReg_injective (fun _ => 106) V W (fun _ => 0) S hblank⟩

def coefficientHeaderAssignments : List (Fin 117 × Fin 48) :=
  [(114, 19), (97, 34), (98, 35), (99, 36), (100, 38), (102, 42)]

def loadCoefficientList : List (Fin 117 × Fin 48) → Pr P₀ 117 Q A U
  | [] => .act .done
  | (src, dst) :: rs => .seq (tblLoad1 coefficientReg src dst) (loadCoefficientList rs)

def loadedCoefficientState (value : Fin 117 → ℕ) : List (Fin 117 × Fin 48) → TblSt 48 A → TblSt 48 A
  | [], st => st
  | (src, dst) :: rs, st => loadedCoefficientState value rs ⟨Function.update st.val dst (value src), st.acc⟩

def loadCoefficientListCost (V : ℕ) (value : Fin 117 → ℕ) (rs : List (Fin 117 × Fin 48)) : ℕ :=
  (rs.map (fun r => value r.1 * (4 * V + 10) + 6 * V + 10)).sum + 1

/-- A structural sequence of retained-header loads establishes the whole state. -/
theorem loadCoefficientList_exec (rs : List (Fin 117 × Fin 48))
    (hoff : ∀ r ∈ rs, ∀ k, coefficientReg k ≠ r.1) (V W : ℕ) (value : Fin 117 → ℕ)
    (st : TblSt 48 A) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hsrc : ∀ r ∈ rs, (S.R r.1).length = value r.1)
    (hS : tblHolds coefficientReg S (tblRho V (List.replicate V tick) (List.replicate W tick) st)) :
    ∃ v' S' m, v'.user = v.user ∧ m ≤ loadCoefficientListCost V value rs ∧
      Exec body (loadCoefficientList rs) (mk v S) m (mk v' S') ∧
      tblHolds coefficientReg S' (tblRho V (List.replicate V tick) (List.replicate W tick)
        (loadedCoefficientState value rs st)) ∧ tblFr coefficientReg S S' := by
  induction rs generalizing st v S with
  | nil =>
    refine ⟨v, S, 1, rfl, by simp [loadCoefficientListCost], ?_, hS, tblFr.refl S⟩
    exact Exec.act (body := body) .done (mk v S)
  | cons r rs ih =>
    obtain ⟨v₁, S₁, m₁, hu₁, hm₁, he₁, hS₁, hf₁⟩ := tbl_load1_runs (body := body)
      coefficientReg_injective (List.replicate V tick) (List.replicate W tick) (by simp)
      (hoff r (by simp)) r.2 st (value r.1) v S (hsrc r (by simp)) hS
    obtain ⟨v₂, S₂, m₂, hu₂, hm₂, he₂, hS₂, hf₂⟩ := ih
      (fun r hr => hoff r (by simp [hr])) _ v₁ S₁ (by
        intro r hr
        rw [hf₁.2.2.2 _ (hoff r (by simp [hr]))]
        exact hsrc r (by simp [hr])) hS₁
    refine ⟨v₂, S₂, m₁ + m₂, hu₂.trans hu₁, ?_, Exec.seq he₁ he₂, hS₂, hf₁.trans hf₂⟩
    simp only [loadCoefficientListCost, List.map_cons, List.sum_cons] at hm₂ ⊢
    omega

/-- The six header lengths are the only nonzero initial table variables. -/
def coefficientHeaderState (P s t u band L : ℕ) : TblSt 48 A :=
  ⟨Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (fun _ => 0) 19 P) 34 s) 35 t) 36 u) 38 band) 42 L, []⟩

def loadCoefficientHeaders : Pr P₀ 117 Q A U := loadCoefficientList coefficientHeaderAssignments

def coefficientHeadersCost (P s t u band L V : ℕ) : ℕ :=
  (P + s + t + u + band + L) * (4 * V + 10) + 36 * V + 61

/-- Loading all six unary headers gives the exact numerical table input state. -/
theorem loadCoefficientHeaders_exec (P s t u band L V W : ℕ)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hP : (S.R 114).length = P) (hs : (S.R 97).length = s) (ht : (S.R 98).length = t)
    (hu : (S.R 99).length = u) (hb : (S.R 100).length = band) (hL : (S.R 102).length = L)
    (hS : tblHolds coefficientReg S
      (tblRho V (List.replicate V tick) (List.replicate W tick) ⟨fun _ => 0, []⟩)) :
    ∃ v' S' m, v'.user = v.user ∧ m ≤ coefficientHeadersCost P s t u band L V ∧
      Exec body loadCoefficientHeaders (mk v S) m (mk v' S') ∧
      tblHolds coefficientReg S' (tblRho V (List.replicate V tick) (List.replicate W tick)
        (coefficientHeaderState P s t u band L)) ∧ tblFr coefficientReg S S' := by
  let value := fun k : Fin 117 => (S.R k).length
  have hhigh : ∀ r ∈ coefficientHeaderAssignments, 63 ≤ r.1.val := by
    intro r hr
    simp only [coefficientHeaderAssignments, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hoff : ∀ r ∈ coefficientHeaderAssignments, ∀ k, coefficientReg k ≠ r.1 := by
    intro r hr k he
    have hlo := coefficientReg_range k
    have hhi := hhigh r hr
    have hv := congrArg (fun x : Fin 117 => x.val) he
    omega
  obtain ⟨v', S', m, huser, hm, he, hholds, hframe⟩ := loadCoefficientList_exec (body := body)
    coefficientHeaderAssignments hoff V W value ⟨fun _ => 0, []⟩ v S (by intros; rfl) hS
  have hstate : loadedCoefficientState value coefficientHeaderAssignments (⟨fun _ => 0, []⟩ : TblSt 48 A) =
      coefficientHeaderState P s t u band L := by
    simp [loadedCoefficientState, coefficientHeaderAssignments, coefficientHeaderState, value, hP, hs, ht, hu, hb, hL]
  have hcost : loadCoefficientListCost V value coefficientHeaderAssignments = coefficientHeadersCost P s t u band L V := by
    simp [loadCoefficientListCost, coefficientHeaderAssignments, coefficientHeadersCost, value, hP, hs, ht, hu, hb, hL]
    ring
  exact ⟨v', S', m, huser, by simpa only [hcost] using hm, he, by simpa only [hstate] using hholds, hframe⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
