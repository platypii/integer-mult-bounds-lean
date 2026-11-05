module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellStandardBoundaryMasterPreparation

/-! The first boundary core starts at zero. Convert its retained binary width,
form its wide bit count, then reuse narrow-count preparation. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P U : Type}

def firstBoundaryMasterPreparationCost (N narrowWidth D width W : ℕ) : ℕ :=
  (6*width+11*D+6)+(width*(4*W+9)+4)+(2*width+3)+
    ((6*(width*narrowWidth)+6)+(N*(4*(width*narrowWidth)+9)+4))


def firstBoundaryMasterPreparation (cropCount : Fin 117) : Pr P 117 Q A U :=
  .seq (toUnary 56 54 30 31 32)
    (.seq (unaryProduct 54 17 24 27 28)
      (.seq (clearWords [54]) (standardSeamCountPreparation cropCount)))

theorem firstBoundaryMasterPreparation_native (cropCount : Fin 117) :
    mnNativePushBound 3
      (firstBoundaryMasterPreparation (P := P) (Q := Q) (A := A) (U := U) cropCount) := by
  refine ⟨?_,⟨mnNativePushBound_mono (by decide) (unaryProduct_native 54 17 24 27 28),
    ⟨mnNativePushBound_mono (by decide) (clearWords_native _),?_⟩⟩⟩
  · simp [toUnary,eachSym,hornerIter,udbl,drainR,popDo,pushN,
      moveR,moveStep,whileR,peekR,popPush,mnNativePushBound,mnActPush]
  · exact ⟨mnNativePushBound_mono (by decide)
      (copyWordHeaders_native (T := 117) (P := P) (Q := Q) (A := A) (U := U) 27 28 [(cropCount,54)]).1,
      mnNativePushBound_mono (by decide) (unaryProduct_native 15 54 19 27 28)⟩

theorem firstBoundaryMasterPreparation_exec (body : P → Pr P 117 Q A U)
    (cropCount : Fin 117) (hreg : [cropCount,15,54,19,27,28,24,26].Nodup)
    (N narrowWidth D s width W : ℕ) (hwidth : width ≤ s) (hfit : width < 2^D)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hbinary : S.R 56 = binSyms D width) (hwide : (S.R 17).length = W)
    (hN : (S.R 15).length = N)
    (hbits : (S.R cropCount).length = width*narrowWidth)
    (hmasters : S.R 26 = [] ∧ S.R 24 = [] ∧ S.R 54 = [] ∧ S.R 19 = [])
    (hscratch : S.R 30 = [] ∧ S.R 31 = [] ∧ S.R 32 = [] ∧ S.R 27 = [] ∧ S.R 28 = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ (6*width+11*D+6)+(width*(4*W+9)+4)+(2*width+3)+
        ((6*(width*narrowWidth)+6)+(N*(4*(width*narrowWidth)+9)+4)) ∧
      Exec body (firstBoundaryMasterPreparation cropCount) (mk v S) n
        (mk v' (standardBoundaryMasterState cropCount N narrowWidth s width 0 W S)) := by
  obtain ⟨h26,h24,h54,h19⟩ := hmasters
  obtain ⟨h30,h31,h32,h27,h28⟩ := hscratch
  have hr := hreg
  regs_ne hr
  have hcrop24 : cropCount ≠ 24 := by assumption
  obtain ⟨u,a,hu,ha,he⟩ := toUnary_exec_linear (body := body)
    (a := 56) (z := 54) (w := 30) (t := 31) (t₂ := 32) (by decide +kernel)
    hfit v S hbinary h30 h31 h32
  simp only [h54,List.append_nil] at he
  let M : Stacks 117 A := {S with R := Function.update S.R 54 (List.replicate width tick)}
  obtain ⟨u',b,hu',hb,he'⟩ := unaryProduct_exec (body := body)
    (a := 54) (b := 17) (dst := 24) (t₁ := 27) (t₂ := 28) (by decide +kernel) u M
    (by simpa [M] using h27) (by simpa [M] using h28)
  simp [M,hwide] at hb
  let F : Stacks 117 A := {M with R := Function.update M.R 24 (List.replicate (width*W) tick)}
  have hprod : Exec body (unaryProduct 54 17 24 27 28) (mk u M) b (mk u' F) := by
    simpa [F,M,h24,hwide] using he'
  obtain ⟨u'',hu'',hclear⟩ := clearWords_exec (body := body) [(54:Fin 117)] (by decide) u' F
  have hclearCost : ([(54:Fin 117)].map (fun i => (F.R i).length)).sum = width := by simp [F,M]
  rw [hclearCost] at hclear
  let G : Stacks 117 A := {S with R := Function.update S.R 24 (List.replicate (width*W) tick)}
  have hclear' : Exec body (clearWords [54]) (mk u' F) (2*width+3) (mk u'' G) := by
    have hstate : ({F with R := fun k => if k = 54 then [] else F.R k} : Stacks 117 A) = G := by
      refine Stacks.ext (by rfl) (by rfl) (by rfl) ?_
      funext i
      by_cases hi : i = 54
      · subst i; simp [G,h54]
      · simp [G,F,M,hi,Function.update_apply]
    have heclear : Exec body (clearWords [54]) (mk u' F) (2*width+3)
        (mk u'' {F with R := fun k => if k = 54 then [] else F.R k}) := by
      simpa [Nat.add_assoc] using hclear
    rw [hstate] at heclear
    exact heclear
  obtain ⟨v',c,hv,hc,hex⟩ := standardSeamCountPreparation_exec (body := body) cropCount
    (by regs_nodup) N width narrowWidth u'' G
    (by simpa [G] using hN)
    (by simpa [G,Function.update_of_ne hcrop24] using hbits)
    ⟨by simpa [G] using h54,by simpa [G] using h19,
      by simpa [G] using h27,by simpa [G] using h28⟩
  refine ⟨v',a+(b+((2*width+3)+c)),hv.trans (hu''.trans (hu'.trans hu)),by omega,?_⟩
  have h26id : Function.update S.R 26 [] = S.R := by
    rw [←h26]
    exact Function.update_eq_self _ _
  have hfull := Exec.seq he (Exec.seq hprod (Exec.seq hclear' hex))
  simpa [firstBoundaryMasterPreparation,standardBoundaryMasterState,coreStart,coreLength,
    Nat.min_eq_left hwidth,h26id,G,M,Function.update_of_ne hcrop24] using hfull

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
