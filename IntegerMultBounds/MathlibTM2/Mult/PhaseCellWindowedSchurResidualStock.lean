module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWindowedSchurResidual
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellArchivedSchurResidualStock

/-! Borrowed interval endpoints compose with the complete archived residual trace. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

@[irreducible] def windowedSchurResidualWorkspace
    (J ringPush batchPush rowPush p l s t u target rhsExp a b : ℕ) : ℕ :=
  2*(4*a+4)+(2*(4*b+4)+archivedSchurResidualWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
    J ringPush batchPush rowPush p l s t u target rhsExp a b)

theorem windowedSchurResidual_spec_within (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (lower upper : Fin 148) (hports : [lower,upper,141,142,143].Nodup)
    {p l s t u target rhsExp a b : ℕ} [NeZero s] {alpha d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (halpha : 0 < alpha) (hst : s < t) (hu : 1 ≤ u)
    (hsquare : alpha^2 = (u : ℝ)) (htheta : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : alpha^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (ha : a ≤ s) (hb : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (B : ZMod s → GaussianInt)
    (hB : ∀ i, ‖value (executionPrecision p l (initialSchurTarget p u target rhsExp) rhsExp) (B i)‖ ≤ (2 : ℝ)^rhsExp)
    (J ringPush batchPush : ℕ)
    (hpushJ : mnProgPush (rmulOne (P := P₀) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ J)
    (hpushR : mnProgPush (rpProg (P := P₀) (Q := Q) (A := A) (U := U)
      Fixed.ringReg Fixed.hostReg Fixed.layout.ι_inj (by decide) hR) ≤ ringPush)
    (hpushK : mnProgPush (cmulBlock cr
      (rmulOne (P := P₀) (Q := Q) (A := A) (U := U) mul mul_injective (by decide) hQ cr)) ≤ batchPush)
    (rowPush : ℕ) (hrowPush : mnProgPush (rmulOne (P := Empty) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ rowPush)
    (v : HS 148 Q A U) (S : Stacks 148 A) (tail : List (Fin (A+4)))
    (h127 : S.R 127 = []) (h138 : S.R 138 = []) (h143 : S.R 143 = [])
    (haSrc : (S.R lower).length = a) (hbSrc : (S.R upper).length = b)
    (h141 : S.R 141 = []) (h142 : S.R 142 = [])
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target rhsExp) rhsExp+1)
      (executionPrecision p l (initialSchurTarget p u target rhsExp) rhsExp) l s t u (PhaseCellBand.width p u) 0 0
      (cstream A (executionWidth p l (initialSchurTarget p u target rhsExp) rhsExp) (chirpLine s B)++tail) (embStk componentReg S))
    (h147 : S.R 147 = []) :
    let q := executionPrecision p l (initialSchurTarget p u target rhsExp) rhsExp
    let w := executionWidth p l (initialSchurTarget p u target rhsExp) rhsExp
    let band := PhaseCellBand.width p u
    ∃ v' m, ∃ C : ZMod s → GaussianInt, ∃ R : (ZMod s → ℝ) → ZMod s → ℝ,
      let output := cstream A w (chirpLine s C)++S.R 132
      let S' : Stacks 148 A := {S with R := Function.update S.R 132 output}
      (∀ rhs, SchurDominance.Solves (realMatrix s t p u) (haloInterior s t band a b) (R rhs) rhs) ∧
      v'.user = v.user ∧ m ≤ (4*a+4)+((4*b+4)+(releasedSchurResidualCost p l s t u target rhsExp a b+archiveResidualPrefixCost q s+(2*(a+b)+5))) ∧
      ExecWithin (embTab componentReg (embTab groupReg body))
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+0+
          windowedSchurResidualWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
            J ringPush batchPush rowPush p l s t u target rhsExp a b)
        0 (windowedSchurResidual hR hQ lower upper) (mk v S) m (mk v' S') ∧
      (∀ i, (C i).im = 0) ∧
      (∀ i, ‖value q (C i)‖ ≤ (2 : ℝ)^couplingRowExponent rhsExp (stableInteriorExponent p rhsExp)
        (8*p+1) (couplingCountExponent p u)) ∧
      (∀ i ∈ haloBoundary s t band a b, 8*p*|(value q (C i)).re-
        SchurDominance.residual (realMatrix s t p u) (haloInterior s t band a b) R
          (fun k => (value q (B k)).re) i| ≤ 1/(2 : ℝ)^(recoveryTarget p target+2)) ∧
      LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target rhsExp) rhsExp+1)
        q l s t u band 0 0 (S.R 110) (embStk componentReg S') := by
  dsimp only
  have hlow141 : lower ≠ 141 := by intro he; subst lower; simp at hports
  have hupp141 : upper ≠ 141 := by intro he; subst upper; simp at hports
  have hlow143 : lower ≠ 143 := by intro he; subst lower; simp at hports
  have hupp142 : upper ≠ 142 := by intro he; subst upper; simp at hports
  have hupp143 : upper ≠ 143 := by intro he; subst upper; simp at hports
  let S₁ : Stacks 148 A := {S with R := Function.update S.R 141 (List.replicate a tick)}
  let S₂ : Stacks 148 A := {S₁ with R := Function.update S₁.R 142 (List.replicate b tick)}
  obtain ⟨v₁,hv₁,he₁⟩ := ucopy_exec (embTab componentReg (embTab groupReg body))
    (a := lower) (b := 141) (t := 143) hlow141 hlow143 (by decide) v S h143
  have he₁' : Exec (embTab componentReg (embTab groupReg body)) (ucopy lower 141 143)
      (mk v S) (4*a+4) (mk v₁ S₁) := by simpa only [haSrc,h141,List.append_nil] using he₁
  obtain ⟨v₂,hv₂,he₂⟩ := ucopy_exec (embTab componentReg (embTab groupReg body))
    (a := upper) (b := 142) (t := 143) hupp142 hupp143 (by decide) v₁ S₁
    (by simpa [S₁] using h143)
  have he₂' : Exec (embTab componentReg (embTab groupReg body)) (ucopy upper 142 143)
      (mk v₁ S₁) (4*b+4) (mk v₂ S₂) := by
    simpa [S₂,S₁,hupp141,hbSrc,h142] using he₂
  have hready₂ : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target rhsExp) rhsExp+1)
      (executionPrecision p l (initialSchurTarget p u target rhsExp) rhsExp) l s t u (PhaseCellBand.width p u) 0 0
      (cstream A (executionWidth p l (initialSchurTarget p u target rhsExp) rhsExp) (chirpLine s B)++tail) (embStk componentReg S₂) := by
    have hproj142 := componentProject_updateR_inner S₁ (142 : Fin 144) (List.replicate b tick)
    have hc142 : componentReg (142 : Fin 144) = (142 : Fin 148) := by decide
    rw [hc142] at hproj142
    have hproj141 := componentProject_updateR_inner S (141 : Fin 144) (List.replicate a tick)
    have hc141 : componentReg (141 : Fin 144) = (141 : Fin 148) := by decide
    rw [hc141] at hproj141
    dsimp only [S₂]
    rw [hproj142]
    dsimp only [S₁]
    rw [hproj141]
    exact (hready.update_window 141 (Or.inl rfl) _).update_window 142 (Or.inr rfl) _
  obtain ⟨v₃,m₃,C,R,hRsolve,hv₃,hm₃,he₃,hreal,hnorm,herror,_⟩ := archivedSchurResidual_spec_within (body := body)
    hR hQ hA hp hwidth halpha hst hu hsquare htheta hgap hbudget hband ha hb hpad B hB J ringPush batchPush hpushJ hpushR hpushK rowPush hrowPush v₂ S₂ tail
    (by simpa [S₂,S₁] using h127) (by simpa [S₂,S₁] using h138) (by simpa [S₂,S₁] using h143)
    (by simp [S₂,S₁]) (by simp [S₂]) hready₂ (by simpa [S₂,S₁] using h147)
  let q := executionPrecision p l (initialSchurTarget p u target rhsExp) rhsExp
  let w := executionWidth p l (initialSchurTarget p u target rhsExp) rhsExp
  let output := cstream A w (chirpLine s C)++S.R 132
  let F : Stacks 148 A := {S₂ with R := Function.update S₂.R 132 output}
  have he₃' : ExecWithin (embTab componentReg (embTab groupReg body))
      (fun d z => mnSize z+d ≤ mnSize (mk v₂ S₂)+0+
        archivedSchurResidualWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
          J ringPush batchPush rowPush p l s t u target rhsExp a b)
      0 (archivedSchurResidual hR hQ)
      (mk v₂ S₂) m₃ (mk v₃ F) := by simpa [F,S₂,S₁,output,w] using he₃
  obtain ⟨v₄,hv₄,he₄⟩ := clearWords_exec (body := embTab componentReg (embTab groupReg body))
    [(141 : Fin 148),142] (by decide) v₃ F
  have hlen : ([(141 : Fin 148),142].map (fun k => (F.R k).length)).sum = a+b := by simp [F,S₂,S₁]
  have hfinal : {F with R := fun k => if k ∈ [(141 : Fin 148),142] then [] else F.R k} =
      {S with R := Function.update S.R 132 output} := by
    ext1
    · rfl
    · rfl
    · rfl
    · funext k
      by_cases h141' : k = 141
      · subst k; simp [h141]
      by_cases h142' : k = 142
      · subst k; simp [h142]
      simp [F,S₂,S₁,h141',h142',Function.update_apply]
  have hcopy (i j k : Fin 148) : mnNativePushBound 2
      (ucopy i j k : Pr P₀ 148 Q A U) := by
    simp [ucopy,umulSym,scanR,drainR,popDo,keepIn,pushN,moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]
  have ht₁ := mn_native_exec_within he₁' 2 (hcopy _ _ _) 0 _ (Nat.le_refl _)
  have ht₂ := mn_native_exec_within he₂' 2 (hcopy _ _ _) 0 _ (Nat.le_refl _)
  have ht₄ := mn_native_exec_within he₄ 0 (clearWords_native_zero _) 0 _ (Nat.le_refl _)
  have ht := (mn_seq_within_add ht₁ (mn_seq_within_add ht₂ (mn_seq_within_add he₃' ht₄))).mono
    (J := fun d z => mnSize z+d ≤ mnSize (mk v S)+0+
      windowedSchurResidualWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
        J ringPush batchPush rowPush p l s t u target rhsExp a b) (by
      intro d z hz
      unfold windowedSchurResidualWorkspace
      omega)
  refine ⟨v₄,(4*a+4)+((4*b+4)+(m₃+(2*(a+b)+5))),C,R,hRsolve,
    hv₄.trans (hv₃.trans (hv₂.trans hv₁)),by omega,
    ht.cast (by rw [hlen]; rfl)
      (congrArg (mk v₄) hfinal),hreal,hnorm,herror,?_⟩
  have hproject := componentProject_updateR_inner S (132 : Fin 144) output
  have hc : componentReg (132 : Fin 144) = (132 : Fin 148) := by decide
  rw [hc] at hproject
  rw [hproject]
  have hsource : S.R 110 = cstream A w (chirpLine s B)++tail := by
    simpa [embStk,componentReg,w] using hready.source
  rw [hsource]
  exact hready.update_output output

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
