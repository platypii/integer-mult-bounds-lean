module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedOriginalColumn

/-! Reuse the original-column initializer at a one-point window around any coordinate. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

theorem mem_haloBoundary_singleton {s : ℕ} [NeZero s] (t band : ℕ) (hband : 0 < band) (j : ZMod s) :
    j ∈ haloBoundary s t band j.val (j.val+1) := by
  apply Finset.mem_sdiff.mpr
  constructor
  · exact (mem_haloVertices _ _ _).mpr ⟨le_rfl,by omega⟩
  · intro hj
    have hh := (Finset.mem_filter.mp hj).2.1
    omega

theorem LengthKeyReady.update_window {A P N q l s t u band V w : ℕ}
    {input : List (Fin (A+4))} {S : Stacks 144 A}
    (h : LengthKeyReady P N q l s t u band V w input S)
    (k : Fin 144) (hk : k = 141 ∨ k = 142) (xs : List (Fin (A+4))) :
    LengthKeyReady P N q l s t u band V w input {S with R := Function.update S.R k xs} := by
  constructor
  · intro r hr
    have hrk : r.1 ≠ k := by
      simp only [groupHeaderCopies,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hk with rfl | rfl
      all_goals rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simpa only [Function.update_of_ne hrk] using h.masters r hr
  · exact h.left
  · intro i hi h93 h110
    have hik : i ≠ k := by rcases hk with rfl | rfl <;> omega
    simpa only [Function.update_of_ne hik] using h.blank i hi h93 h110
  · rcases hk with rfl | rfl <;> simpa using h.source
  · rcases hk with rfl | rfl <;> simpa using h.countSaved
  · rcases hk with rfl | rfl <;> simpa using h.headerTemp
  · rcases hk with rfl | rfl <;> simpa using h.wordWidth
  · rcases hk with rfl | rfl <;> simpa using h.keyWidth
  · intro i hi
    have hik : i ≠ k := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hk with rfl | rfl
      all_goals rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simpa only [Function.update_of_ne hik] using h.fresh i hi

noncomputable def arbitraryOriginalColumn (hQ : SS.states ≤ Q) : Pr P₀ 148 Q A U :=
  .seq (ucopy 139 141 143) (.seq (ucopy 139 142 143)
    (.seq (.act (.push (.rt 142) (fun _ => tick) .done))
      (.seq (retainedOriginalColumn hQ) (clearWords [141,142]))))

def arbitraryOriginalColumnCost (p q s t u j : ℕ) : ℕ :=
  (4*j+4)+((4*j+4)+(1+(restoredOriginalColumnCost p q s t u j (j+1) j+(2*(j+(j+1))+5))))

theorem arbitraryOriginalColumn_spec (hQ : SS.states ≤ Q)
    {p q N l s t u : ℕ} [NeZero s] {alpha d : ℝ}
    (hA : 96 ≤ A) (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (halpha : 0 < alpha) (hst : s < t)
    (hsquare : alpha^2 = (u : ℝ)) (htheta : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : alpha^2*d ≤ p)
    (hw : q+couplingRowExponent 0 0 (8*p+1) (couplingCountExponent p u)+2 ≤ 2*q+8)
    (hband : PhaseCellBand.width p u ≤ s)
    (j : ZMod s) (tail : List (Fin (A+4))) (v : HS 148 Q A U) (S : Stacks 148 A)
    (hready : LengthKeyReady (2^15*p) N q l s t u (PhaseCellBand.width p u) 0 0 tail (embStk componentReg S))
    (hcoordinate : (S.R 139).length = j.val)
    (hfresh : ∀ k ∈ [(138 : Fin 148),141,142,143], S.R k = []) :
    let band := PhaseCellBand.width p u
    let column := couplingRowField (2^15*p) q t u band j.val (j.val+1) true (negativeUnitField q j) (fun _ => 0)
    let output := cstream A (2*q+8) (chirpLine s column)++tail
    let S' : Stacks 148 A := {S with R := Function.update S.R 110 output}
    ∃ v' m, v'.user = v.user ∧ m ≤ arbitraryOriginalColumnCost p q s t u j.val ∧
      Exec (embTab componentReg (embTab groupReg body)) (arbitraryOriginalColumn hQ) (mk v S) m (mk v' S') ∧
      (∀ i, (column i).im = 0) ∧
      (∀ i, ‖value q (column i)‖ ≤ 2+3*(2*band+1)*(1/(2 : ℝ)^q)) ∧
      (∀ i, |publishedCellRead q (2*q+8) (0 : ZMod s) (S'.R 110) i-realMatrix s t p u i j| ≤
        3*(2*band+1)*(1/(2 : ℝ)^q)) ∧
      LengthKeyReady (2^15*p) N q l s t u band 0 0 output (embStk componentReg S') := by
  dsimp only
  let n := j.val
  let S₁ : Stacks 148 A := {S with R := Function.update S.R 141 (List.replicate n tick)}
  let S₂ : Stacks 148 A := {S₁ with R := Function.update S₁.R 142 (List.replicate n tick)}
  let S₃ : Stacks 148 A := {S₁ with R := Function.update S₁.R 142 (List.replicate (n+1) tick)}
  obtain ⟨v₁,hv₁,he₁⟩ := ucopy_exec (embTab componentReg (embTab groupReg body))
    (a := 139) (b := 141) (t := 143) (by decide) (by decide) (by decide) v S (hfresh 143 (by simp))
  have he₁' : Exec (embTab componentReg (embTab groupReg body)) (ucopy 139 141 143)
      (mk v S) (4*n+4) (mk v₁ S₁) := by simpa [S₁,n,hcoordinate,hfresh 141 (by simp)] using he₁
  obtain ⟨v₂,hv₂,he₂⟩ := ucopy_exec (embTab componentReg (embTab groupReg body))
    (a := 139) (b := 142) (t := 143) (by decide) (by decide) (by decide) v₁ S₁
    (by simpa [S₁] using hfresh 143 (by simp))
  have he₂' : Exec (embTab componentReg (embTab groupReg body)) (ucopy 139 142 143)
      (mk v₁ S₁) (4*n+4) (mk v₂ S₂) := by simpa [S₂,S₁,n,hcoordinate,hfresh 142 (by simp)] using he₂
  have he₃ : Exec (embTab componentReg (embTab groupReg body))
      (.act (.push (.rt 142) (fun _ => tick) .done)) (mk v₂ S₂) 1 (mk v₂ S₃) := by
    convert Exec.act (body := embTab componentReg (embTab groupReg body))
      (.push (.rt 142) (fun _ => tick) .done) (mk v₂ S₂) using 1
    simp [S₃,S₂,Action.run,update_rt,List.replicate_succ]
  have hready₃ : LengthKeyReady (2^15*p) N q l s t u (PhaseCellBand.width p u) 0 0 tail (embStk componentReg S₃) := by
    dsimp only [S₃]
    have hproj142 := componentProject_updateR_inner S₁ (142 : Fin 144) (List.replicate (n+1) tick)
    have hc142 : componentReg (142 : Fin 144) = (142 : Fin 148) := by decide
    rw [hc142] at hproj142
    rw [hproj142]
    dsimp only [S₁]
    have hproj141 := componentProject_updateR_inner S (141 : Fin 144) (List.replicate n tick)
    have hc141 : componentReg (141 : Fin 144) = (141 : Fin 148) := by decide
    rw [hc141] at hproj141
    rw [hproj141]
    exact (hready.update_window 141 (Or.inl rfl) _).update_window 142 (Or.inr rfl) _
  obtain ⟨v₄,m,hv₄,hm,he₄,hreal,hnorm,herror,_⟩ := retainedOriginalColumn_spec (body := body)
    hQ hA hp hwidth halpha hst hsquare htheta hgap hbudget hw (Nat.le_of_lt j.val_lt)
    (by have := j.val_lt; omega) hband j (mem_haloBoundary_singleton t _ (PhaseCellBand.width_pos p u) j)
    tail v₂ S₃ hready₃ (by simp [S₃,S₁,n]) (by simp [S₃,n])
    (by simpa [S₃,S₁] using hcoordinate) (by simpa [S₃,S₁] using hfresh 143 (by simp))
    (by simpa [S₃,S₁] using hfresh 138 (by simp))
  let column := couplingRowField (2^15*p) q t u (PhaseCellBand.width p u) n (n+1) true (negativeUnitField q j) (fun _ => 0)
  let output := cstream A (2*q+8) (chirpLine s column)++tail
  let F : Stacks 148 A := {S₃ with R := Function.update S₃.R 110 output}
  obtain ⟨v₅,hv₅,he₅⟩ := clearWords_exec (body := embTab componentReg (embTab groupReg body))
    [(141 : Fin 148),142] (by decide) v₄ F
  have hlen : ([(141 : Fin 148),142].map (fun k => (F.R k).length)).sum = n+(n+1) := by simp [F,S₃,S₁]
  have hfinal : {F with R := fun k => if k ∈ [(141 : Fin 148),142] then [] else F.R k} =
      {S with R := Function.update S.R 110 output} := by
    ext1
    · rfl
    · rfl
    · rfl
    · funext k
      by_cases h141 : k = 141
      · subst k; simp [hfresh 141 (by simp)]
      by_cases h142 : k = 142
      · subst k; simp [hfresh 142 (by simp)]
      simp [F,S₃,S₁,h141,h142,Function.update_apply]
  refine ⟨v₅,(4*n+4)+((4*n+4)+(1+(m+(2*(n+(n+1))+5)))),
    hv₅.trans (hv₄.trans (hv₂.trans hv₁)),?_,?_,hreal,hnorm,?_,?_⟩
  · exact Nat.add_le_add_left (Nat.add_le_add_left (Nat.add_le_add_left
      (Nat.add_le_add_right hm _) _) _) _
  · exact (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃ (Exec.seq he₄ he₅)))).cast
      (by rw [hlen]; rfl) (congrArg (mk v₅) hfinal)
  · intro i
    simpa [F,S₃,S₁] using herror i
  · have hproj := componentProject_updateR_inner S (110 : Fin 144) output
    have hc110 : componentReg (110 : Fin 144) = (110 : Fin 148) := by decide
    rw [hc110] at hproj
    rw [hproj]
    exact hready.update_source output

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
