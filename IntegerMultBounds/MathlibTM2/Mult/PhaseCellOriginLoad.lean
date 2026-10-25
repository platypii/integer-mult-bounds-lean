module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOriginController
public import IntegerMultBounds.MathlibTM2.Mult.ChirpBankLoad
public import IntegerMultBounds.MathlibTM2.Fast.TableLoad

/-! Construct the origin controller's table and load its four ordinary unary headers. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def initializeOriginBank : Pr P₀ 117 Q A U :=
  chirpBankLoad originReg (fun _ => 106) 115 115

/-- All zero-valued table variables and both word counters are constructed. -/
theorem initializeOriginBank_exec (V : ℕ) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hV : (S.R 115).length = V) (hz : S.R 106 = [])
    (hblank : ∀ r, S.R (originReg r) = []) :
    ∃ v', v'.user = v.user ∧
      Exec body initializeOriginBank (mk v S) (104 * V + 137)
        (mk v' { S with R := chirpBankLoadR originReg (fun _ => 106) V V (fun _ => 0) S.R }) ∧
      tblHolds originReg { S with R := chirpBankLoadR originReg (fun _ => 106) V V (fun _ => 0) S.R }
        (tblRho V (List.replicate V tick) (List.replicate V tick) ⟨fun _ => 0, []⟩) := by
  have hoff (k : Fin 117) (hk : 31 ≤ k.val) : ∀ r, originReg r ≠ k := by
    intro r he
    have hr := originReg_range r
    rw [he] at hr
    omega
  obtain ⟨v', hu, he⟩ := chirpBankLoad_exec (body := body) originReg originReg_injective
    (fun _ => 106) 115 115 (hoff 115 (by decide)) (hoff 115 (by decide))
    (fun _ => hoff 106 (by decide)) V V (fun _ => 0) (fun _ => 0) (by simp) (by simp)
    v S hV hV (by simpa [binSyms] using hz) hblank
  have hcost : chirpBankLoadCost originReg (fun _ : Fin 16 => 106) V V (fun _ => 0) =
      104 * V + 137 := by
    simp [chirpBankLoadCost, chirpBankCopiesCost, chirpBankInputAssignments,
      ]
    ring
  exact ⟨v', hu, he.cast hcost rfl,
    chirpBankLoad_holds originReg originReg_injective (fun _ => 106) V V (fun _ => 0) S hblank⟩

def originHeaderAssignments : List (Fin 117 × Fin 16) :=
  [(97, 0), (98, 1), (100, 2), (102, 3)]

def loadOriginList : List (Fin 117 × Fin 16) → Pr P₀ 117 Q A U
  | [] => .act .done
  | (src, dst) :: rs => .seq (tblLoad1 originReg src dst) (loadOriginList rs)

def loadedOriginState (value : Fin 117 → ℕ) : List (Fin 117 × Fin 16) → TblSt 16 A → TblSt 16 A
  | [], st => st
  | (src, dst) :: rs, st => loadedOriginState value rs ⟨Function.update st.val dst (value src), st.acc⟩

def loadOriginListCost (V : ℕ) (value : Fin 117 → ℕ) (rs : List (Fin 117 × Fin 16)) : ℕ :=
  (rs.map (fun r => value r.1 * (4 * V + 10) + 6 * V + 10)).sum + 1

/-- A structural sequence of retained-header loads establishes the whole state. -/
theorem loadOriginList_exec (rs : List (Fin 117 × Fin 16))
    (hoff : ∀ r ∈ rs, ∀ k, originReg k ≠ r.1) (V W : ℕ) (value : Fin 117 → ℕ)
    (st : TblSt 16 A) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hsrc : ∀ r ∈ rs, (S.R r.1).length = value r.1)
    (hS : tblHolds originReg S (tblRho V (List.replicate V tick) (List.replicate W tick) st)) :
    ∃ v' S' m, v'.user = v.user ∧ m ≤ loadOriginListCost V value rs ∧
      Exec body (loadOriginList rs) (mk v S) m (mk v' S') ∧
      tblHolds originReg S' (tblRho V (List.replicate V tick) (List.replicate W tick)
        (loadedOriginState value rs st)) ∧ tblFr originReg S S' := by
  induction rs generalizing st v S with
  | nil =>
    refine ⟨v, S, 1, rfl, by simp [loadOriginListCost], ?_, hS, tblFr.refl S⟩
    exact Exec.act (body := body) .done (mk v S)
  | cons r rs ih =>
    obtain ⟨v₁, S₁, m₁, hu₁, hm₁, he₁, hS₁, hf₁⟩ := tbl_load1_runs (body := body)
      originReg_injective (List.replicate V tick) (List.replicate W tick) (by simp)
      (hoff r (by simp)) r.2 st (value r.1) v S (hsrc r (by simp)) hS
    obtain ⟨v₂, S₂, m₂, hu₂, hm₂, he₂, hS₂, hf₂⟩ := ih
      (fun r hr => hoff r (by simp [hr])) _ v₁ S₁ (by
        intro r hr
        rw [hf₁.2.2.2 _ (hoff r (by simp [hr]))]
        exact hsrc r (by simp [hr])) hS₁
    refine ⟨v₂, S₂, m₁ + m₂, hu₂.trans hu₁, ?_, Exec.seq he₁ he₂, hS₂, hf₁.trans hf₂⟩
    simp only [loadOriginListCost, List.map_cons, List.sum_cons] at hm₂ ⊢
    omega

def loadOriginHeaders : Pr P₀ 117 Q A U := loadOriginList originHeaderAssignments

def originHeadersCost (s t band L V : ℕ) : ℕ :=
  (s + t + band + L) * (4 * V + 10) + 24 * V + 41

/-- Loading all four unary headers gives the exact numerical table input state. -/
theorem loadOriginHeaders_exec (s t band L V W : ℕ)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hs : (S.R 97).length = s) (ht : (S.R 98).length = t)
    (hb : (S.R 100).length = band) (hL : (S.R 102).length = L)
    (hS : tblHolds originReg S
      (tblRho V (List.replicate V tick) (List.replicate W tick) ⟨fun _ => 0, []⟩)) :
    ∃ v' S' m, v'.user = v.user ∧ m ≤ originHeadersCost s t band L V ∧
      Exec body loadOriginHeaders (mk v S) m (mk v' S') ∧
      tblHolds originReg S' (tblRho V (List.replicate V tick) (List.replicate W tick)
        (originRawState A s t band L)) ∧ tblFr originReg S S' := by
  let value := fun k : Fin 117 => (S.R k).length
  have hhigh : ∀ r ∈ originHeaderAssignments, 31 ≤ r.1.val := by
    intro r hr
    simp only [originHeaderAssignments, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide
  have hoff : ∀ r ∈ originHeaderAssignments, ∀ k, originReg k ≠ r.1 := by
    intro r hr k he
    have hlo := originReg_range k
    have hhi := hhigh r hr
    have hv := congrArg (fun x : Fin 117 => x.val) he
    omega
  obtain ⟨v', S', m, huser, hm, he, hholds, hframe⟩ := loadOriginList_exec (body := body)
    originHeaderAssignments hoff V W value ⟨fun _ => 0, []⟩ v S (by intros; rfl) hS
  have hstate : loadedOriginState value originHeaderAssignments (⟨fun _ => 0, []⟩ : TblSt 16 A) =
      originRawState A s t band L := by
    simp [loadedOriginState, originHeaderAssignments, originRawState, value, hs, ht, hb, hL]
  have hcost : loadOriginListCost V value originHeaderAssignments = originHeadersCost s t band L V := by
    simp [loadOriginListCost, originHeaderAssignments, originHeadersCost, value, hs, ht, hb, hL]
    ring
  exact ⟨v', S', m, huser, by simpa only [hcost] using hm, he, by simpa only [hstate] using hholds, hframe⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
