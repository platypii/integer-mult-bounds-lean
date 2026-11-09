module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedOriginalColumnStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellArbitraryOriginalColumn

/-! Reuse the original-column initializer at a one-point window around any coordinate. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

@[irreducible] def arbitraryOriginalColumnWorkspace (R p q s t u j : ℕ) : ℕ :=
  3*(4*j+4)+(3*(4*j+4)+(1+
    restoredOriginalColumnWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U) R p q s t u j (j+1) j))

theorem arbitraryOriginalColumn_trace_within {B : P₀ → Pr P₀ 148 Q A U}
    (hQ : SS.states ≤ Q) {v₀ v₁ v₂ v₃ v₄ v₅ : HS 148 Q A U}
    {S₀ S₁ S₂ S₃ S₄ S₅ : Stacks 148 A} {n₁ n₂ n₃ n₄ n₅ work cap : ℕ}
    (he₁ : Exec B (ucopy 139 141 143) (mk v₀ S₀) n₁ (mk v₁ S₁))
    (he₂ : Exec B (ucopy 139 142 143) (mk v₁ S₁) n₂ (mk v₂ S₂))
    (he₃ : Exec B (.act (.push (.rt 142) (fun _ => tick) .done)) (mk v₂ S₂) n₃ (mk v₃ S₃))
    (he₄ : ExecWithin B (fun d z => mnSize z+d ≤ mnSize (mk v₃ S₃)+0+work) 0
      (retainedOriginalColumn hQ) (mk v₃ S₃) n₄ (mk v₄ S₄))
    (he₅ : Exec B (clearWords [141,142]) (mk v₄ S₄) n₅ (mk v₅ S₅))
    (hcap : 3*n₁+(3*n₂+(n₃+work)) ≤ cap) :
    ExecWithin B (fun d z => mnSize z+d ≤ mnSize (mk v₀ S₀)+0+cap) 0
      (arbitraryOriginalColumn hQ) (mk v₀ S₀) (n₁+(n₂+(n₃+(n₄+n₅)))) (mk v₅ S₅) := by
  have hcopy (a b c : Fin 148) : mnNativePushBound 3
      (ucopy (P := P₀) (Q := Q) (A := A) (U := U) a b c) := by
    simp [ucopy,umulSym,scanR,drainR,popDo,keepIn,pushN,moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]
  have ht₁ := mn_native_exec_within he₁ 3 (hcopy ..) 0 _ (Nat.le_refl _)
  have ht₂ := mn_native_exec_within he₂ 3 (hcopy ..) 0 _ (Nat.le_refl _)
  have ht₃ := mn_native_exec_within he₃ 1 (by change 1 ≤ 1; exact le_refl _)
    0 (mnSize (mk v₂ S₂)+0+n₃) (by omega)
  have ht₅ := mn_native_exec_within he₅ 0 (clearWords_native_zero _) 0
    (mnSize (mk v₄ S₄)+0+0) (by omega)
  exact (mn_seq_within_add ht₁ (mn_seq_within_add ht₂
    (mn_seq_within_add ht₃ (mn_seq_within_add he₄ ht₅)))).mono (by intro d z hz; omega)

theorem arbitraryOriginalColumn_spec_within (hQ : SS.states ≤ Q)
    {p q N l s t u : ℕ} [NeZero s] {alpha d : ℝ}
    (hA : 96 ≤ A) (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (halpha : 0 < alpha) (hst : s < t)
    (hsquare : alpha^2 = (u : ℝ)) (htheta : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : alpha^2*d ≤ p)
    (hw : q+couplingRowExponent 0 0 (8*p+1) (couplingCountExponent p u)+2 ≤ 2*q+8)
    (hband : PhaseCellBand.width p u ≤ s)
    (j : ZMod s) (tail : List (Fin (A+4))) (R : ℕ) (hpush : mnProgPush (rmulOne (P := Empty) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ R)
    (v : HS 148 Q A U) (S : Stacks 148 A)
    (hready : LengthKeyReady (2^15*p) N q l s t u (PhaseCellBand.width p u) 0 0 tail (embStk componentReg S))
    (hcoordinate : (S.R 139).length = j.val)
    (hfresh : ∀ k ∈ [(138 : Fin 148),141,142,143], S.R k = []) :
    let band := PhaseCellBand.width p u
    let column := couplingRowField (2^15*p) q t u band j.val (j.val+1) true (negativeUnitField q j) (fun _ => 0)
    let output := cstream A (2*q+8) (chirpLine s column)++tail
    let S' : Stacks 148 A := {S with R := Function.update S.R 110 output}
    ∃ v' m, v'.user = v.user ∧ m ≤ arbitraryOriginalColumnCost p q s t u j.val ∧
      ExecWithin (embTab componentReg (embTab groupReg body)) (fun d z => mnSize z+d ≤ mnSize (mk v S)+0+
        arbitraryOriginalColumnWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U) R p q s t u j.val) 0
        (arbitraryOriginalColumn hQ) (mk v S) m (mk v' S') ∧
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
  obtain ⟨v₄,m,hv₄,hm,he₄,hreal,hnorm,herror,_⟩ := retainedOriginalColumn_spec_within (body := body)
    hQ hA hp hwidth halpha hst hsquare htheta hgap hbudget hw (Nat.le_of_lt j.val_lt)
    (by have := j.val_lt; omega) hband j (mem_haloBoundary_singleton t _ (PhaseCellBand.width_pos p u) j)
    tail R hpush v₂ S₃ hready₃ (by simp [S₃,S₁,n]) (by simp [S₃,n])
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
  have ht := arbitraryOriginalColumn_trace_within hQ he₁' he₂' he₃ he₄ he₅
    (cap := arbitraryOriginalColumnWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U) R p q s t u j.val)
    (by unfold arbitraryOriginalColumnWorkspace; exact le_refl _)
  refine ⟨v₅,(4*n+4)+((4*n+4)+(1+(m+(2*(n+(n+1))+5)))),
    hv₅.trans (hv₄.trans (hv₂.trans hv₁)),?_,?_,hreal,hnorm,?_,?_⟩
  · exact Nat.add_le_add_left (Nat.add_le_add_left (Nat.add_le_add_left
      (Nat.add_le_add_right hm _) _) _) _
  · exact ht.cast
      (by rw [hlen]; rfl) (congrArg (mk v₅) hfinal)
  · intro i
    simpa [F,S₃,S₁] using herror i
  · have hproj := componentProject_updateR_inner S (110 : Fin 144) output
    have hc110 : componentReg (110 : Fin 144) = (110 : Fin 148) := by decide
    rw [hc110] at hproj
    rw [hproj]
    exact hready.update_source output

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
