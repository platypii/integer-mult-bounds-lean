module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoefficientLoad
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightWidth

/-! Load the seven ordinary unary headers used by numerical weight generation.
All original source symbols remain available to later setup stages. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def weightHeaderAssignments : List (Fin 117 × Fin 48) :=
  [(114, 19), (97, 34), (98, 35), (99, 36), (112, 45), (102, 46), (111, 47)]

def weightHeaderState (P s t u q L lo : ℕ) : TblSt 48 A :=
  ⟨Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (fun _ => 0) 19 P) 34 s) 35 t) 36 u) 45 q) 46 L) 47 lo, []⟩

def loadWeightHeaders : Pr P₀ 117 Q A U := loadCoefficientList weightHeaderAssignments

def weightHeadersCost (P s t u q L lo V : ℕ) : ℕ :=
  (P + s + t + u + q + L + lo) * (4 * V + 10) + 42 * V + 71

/-- Loading all seven unary headers gives the exact numerical table input state. -/
theorem loadWeightHeaders_exec (P s t u q L lo V W : ℕ)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hP : (S.R 114).length = P) (hs : (S.R 97).length = s) (ht : (S.R 98).length = t)
    (hu : (S.R 99).length = u) (hq : (S.R 112).length = q) (hlo : (S.R 111).length = lo) (hL : (S.R 102).length = L)
    (hS : tblHolds coefficientReg S
      (tblRho V (List.replicate V tick) (List.replicate W tick) ⟨fun _ => 0, []⟩)) :
    ∃ v' S' m, v'.user = v.user ∧ m ≤ weightHeadersCost P s t u q L lo V ∧
      Exec body loadWeightHeaders (mk v S) m (mk v' S') ∧
      tblHolds coefficientReg S' (tblRho V (List.replicate V tick) (List.replicate W tick)
        (weightHeaderState P s t u q L lo)) ∧ tblFr coefficientReg S S' := by
  let value := fun k : Fin 117 => (S.R k).length
  have hhigh : ∀ r ∈ weightHeaderAssignments, 63 ≤ r.1.val := by
    intro r hr
    simp only [weightHeaderAssignments, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hoff : ∀ r ∈ weightHeaderAssignments, ∀ k, coefficientReg k ≠ r.1 := by
    intro r hr k he
    have hlo := coefficientReg_range k
    have hhi := hhigh r hr
    have hv := congrArg (fun x : Fin 117 => x.val) he
    omega
  obtain ⟨v', S', m, huser, hm, he, hholds, hframe⟩ := loadCoefficientList_exec (body := body)
    weightHeaderAssignments hoff V W value ⟨fun _ => 0, []⟩ v S (by intros; rfl) hS
  have hstate : loadedCoefficientState value weightHeaderAssignments (⟨fun _ => 0, []⟩ : TblSt 48 A) =
      weightHeaderState P s t u q L lo := by
    simp [loadedCoefficientState, weightHeaderAssignments, weightHeaderState, value, hP, hs, ht, hu, hq, hL, hlo]
  have hcost : loadCoefficientListCost V value weightHeaderAssignments = weightHeadersCost P s t u q L lo V := by
    simp [loadCoefficientListCost, weightHeaderAssignments, weightHeadersCost, value, hP, hs, ht, hu, hq, hL, hlo]
    ring
  exact ⟨v', S', m, huser, by simpa only [hcost] using hm, he, by simpa only [hstate] using hholds, hframe⟩


/-- Every word of the loaded state fits the dimension-based workspace width. -/
theorem weightHeaderState_fits {P s t u q L lo w : ℕ}
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u)
    (hlo : lo < s) (hL : L ≤ s) :
    ∀ j, (weightHeaderState (A := A) P s t u q L lo).val j <
      2 ^ weightWorkspaceWidth P q w t u := by
  let V := weightWorkspaceWidth P q w t u
  obtain ⟨_, hPV, hqPV, _, hLV, hsV, htV, _⟩ :=
    weightWorkspaceWidth_facts (q := q) (w := w) hP hs hst hu hlo hL
  have hpow : V < 2 ^ V := Nat.lt_two_pow_self
  have hPfit : P < 2 ^ V := (show P < V by omega).trans hpow
  have hqfit : q < 2 ^ V := (show q < V by omega).trans hpow
  have hsfit : s < 2 ^ V := (show s ≤ 2 * s by omega).trans_lt hsV
  have hlofit : lo < 2 ^ V := hlo.trans hsfit
  have hufit : u < 2 ^ V := (Nat.lt_size_self u).trans_le
    (Nat.pow_le_pow_right (by decide) (show Nat.size u ≤ V by
      dsimp [V, weightWorkspaceWidth, coefficientWorkspaceWidth]; omega))
  have upd {f : Fin 48 → ℕ} {k : Fin 48} {n : ℕ}
      (hf : ∀ j, f j < 2 ^ V) (hn : n < 2 ^ V) :
      ∀ j, Function.update f k n j < 2 ^ V := by
    intro j
    by_cases hj : j = k
    · simpa [hj] using hn
    · simpa [hj] using hf j
  exact upd (upd (upd (upd (upd (upd (upd (fun _ => by positivity) hPfit)
    hsfit) htV) hufit) hqfit) hLV) hlofit

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
