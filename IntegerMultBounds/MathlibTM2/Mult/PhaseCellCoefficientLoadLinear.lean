module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoefficientLoad
public import IntegerMultBounds.MathlibTM2.Fast.TableLoadLinear

/-! Linear retained-header loading for the numerical coefficient bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def loadCoefficientListLinear : List (Fin 117 × Fin 48) → Pr P₀ 117 Q A U
  | [] => .act .done
  | (src, dst) :: rs => .seq (tblLoadLinear coefficientReg src dst) (loadCoefficientListLinear rs)

def loadCoefficientListLinearCost (V : ℕ) (value : Fin 117 → ℕ) (rs : List (Fin 117 × Fin 48)) : ℕ :=
  (rs.map (fun r => 21*value r.1+14*V+30)).sum + 1

/-- A structural sequence of retained-header loads establishes the whole state. -/
theorem loadCoefficientListLinear_exec (rs : List (Fin 117 × Fin 48))
    (hoff : ∀ r ∈ rs, ∀ k, coefficientReg k ≠ r.1) (V W : ℕ) (value : Fin 117 → ℕ)
    (hfit : ∀ r ∈ rs, Nat.size (value r.1) ≤ V)
    (st : TblSt 48 A) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hsrc : ∀ r ∈ rs, (S.R r.1).length = value r.1)
    (hS : tblHolds coefficientReg S (tblRho V (List.replicate V tick) (List.replicate W tick) st)) :
    ∃ v' S' m, v'.user = v.user ∧ m ≤ loadCoefficientListLinearCost V value rs ∧
      Exec body (loadCoefficientListLinear rs) (mk v S) m (mk v' S') ∧
      tblHolds coefficientReg S' (tblRho V (List.replicate V tick) (List.replicate W tick)
        (loadedCoefficientState value rs st)) ∧ tblFr coefficientReg S S' := by
  induction rs generalizing st v S with
  | nil =>
    refine ⟨v, S, 1, rfl, by simp [loadCoefficientListLinearCost], ?_, hS, tblFr.refl S⟩
    exact Exec.act (body := body) .done (mk v S)
  | cons r rs ih =>
    obtain ⟨v₁, S₁, m₁, hu₁, hm₁, he₁, hS₁, hf₁⟩ := tbl_load_linear_runs (body := body)
      coefficientReg_injective (List.replicate V tick) (List.replicate W tick) (by simp)
      (hoff r (by simp)) r.2 st (value r.1) (hfit r (by simp)) v S (hsrc r (by simp)) hS
    obtain ⟨v₂, S₂, m₂, hu₂, hm₂, he₂, hS₂, hf₂⟩ := ih
      (fun r hr => hoff r (by simp [hr])) (fun r hr => hfit r (by simp [hr])) _ v₁ S₁ (by
        intro r hr
        rw [hf₁.2.2.2 _ (hoff r (by simp [hr]))]
        exact hsrc r (by simp [hr])) hS₁
    refine ⟨v₂, S₂, m₁ + m₂, hu₂.trans hu₁, ?_, Exec.seq he₁ he₂, hS₂, hf₁.trans hf₂⟩
    simp only [loadCoefficientListLinearCost, List.map_cons, List.sum_cons] at hm₂ ⊢
    omega

def loadCoefficientHeadersLinear : Pr P₀ 117 Q A U := loadCoefficientListLinear coefficientHeaderAssignments

def coefficientHeadersLinearCost (P s t u band L V : ℕ) : ℕ :=
  21*(P+s+t+u+band+L)+84*V+181

/-- Loading all six unary headers gives the exact numerical table input state. -/
theorem loadCoefficientHeadersLinear_exec (P s t u band L V W : ℕ)
    (hfit : ∀ x ∈ [P,s,t,u,band,L], Nat.size x ≤ V)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hP : (S.R 114).length = P) (hs : (S.R 97).length = s) (ht : (S.R 98).length = t)
    (hu : (S.R 99).length = u) (hb : (S.R 100).length = band) (hL : (S.R 102).length = L)
    (hS : tblHolds coefficientReg S
      (tblRho V (List.replicate V tick) (List.replicate W tick) ⟨fun _ => 0, []⟩)) :
    ∃ v' S' m, v'.user = v.user ∧ m ≤ coefficientHeadersLinearCost P s t u band L V ∧
      Exec body loadCoefficientHeadersLinear (mk v S) m (mk v' S') ∧
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
  obtain ⟨v', S', m, huser, hm, he, hholds, hframe⟩ := loadCoefficientListLinear_exec (body := body)
    coefficientHeaderAssignments hoff V W value (by
      intro r hr
      simp only [coefficientHeaderAssignments,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp only [value,hP,hs,ht,hu,hb,hL]; apply hfit; simp) ⟨fun _ => 0, []⟩ v S (by intros; rfl) hS
  have hstate : loadedCoefficientState value coefficientHeaderAssignments (⟨fun _ => 0, []⟩ : TblSt 48 A) =
      coefficientHeaderState P s t u band L := by
    simp [loadedCoefficientState, coefficientHeaderAssignments, coefficientHeaderState, value, hP, hs, ht, hu, hb, hL]
  have hcost : loadCoefficientListLinearCost V value coefficientHeaderAssignments = coefficientHeadersLinearCost P s t u band L V := by
    simp [loadCoefficientListLinearCost, coefficientHeaderAssignments, coefficientHeadersLinearCost, value, hP, hs, ht, hu, hb, hL]
    ring
  exact ⟨v', S', m, huser, by simpa only [hcost] using hm, he, by simpa only [hstate] using hholds, hframe⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
