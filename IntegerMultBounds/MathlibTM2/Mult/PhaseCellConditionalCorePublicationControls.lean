module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCorePublicationControls

/-! The remainder header selects the clipped control generator at runtime.
An empty remainder emits no packet and preserves the existing suffix. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def remainderPublicationControls (remainder count coreWidth wordWidth product control saved tmp : Fin T) : Pr P T Q A U :=
  .seq (.act (peekR remainder))
    (.cond (·.flag) (clippedCorePublicationControls count coreWidth wordWidth product control saved tmp) (.act .done))

def remainderPublicationControlsCost (s width w : ℕ) :=
  if 0 < s%width then (s/width)*(4*width+9)+(s/width*width)*(4*w+11)+13 else 3

theorem remainderPublicationControls_exec
    (remainder count coreWidth wordWidth product control saved tmp : Fin T)
    (hreg : [count,coreWidth,wordWidth,product,control,saved,tmp].Nodup)
    (s width w : ℕ) (hw : 0 < width) (v : HS T Q A U) (S : Stacks T A)
    (hrem : (S.R remainder).length = s%width)
    (hcount : (S.R count).length = s/width) (hcore : (S.R coreWidth).length = width)
    (hword : (S.R wordWidth).length = w)
    (hproduct : S.R product = []) (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ remainderPublicationControlsCost s width w ∧
      Exec body (remainderPublicationControls remainder count coreWidth wordWidth product control saved tmp)
        (mk v S) n (mk v' {S with R := (Function.update S.R control
          (gatherControls A ((corePublicationWindows s width (s%width) hw).gaps w)++S.R control))}) := by
  let v₀ : HS T Q A U := {v with flag := (S.R remainder).head?.isSome}
  have hpeek : Exec body (.act (peekR remainder)) (mk v S) 1 (mk v₀ S) := by
    simpa only [peekR_run,v₀] using Exec.act (body := body) (peekR remainder) (mk v S)
  by_cases hr : 0 < s%width
  · obtain ⟨v₁,n,hu,hn,he⟩ := clippedCorePublicationControls_exec (body := body)
      count coreWidth wordWidth product control saved tmp hreg s width w hw hr v₀ S
      hcount hcore hword hproduct hsaved htmp
    have hflag : v₀.flag = true := by
      have hne : S.R remainder ≠ [] := List.length_pos_iff.mp (by omega)
      obtain ⟨x,xs,hxs⟩ := List.exists_cons_of_ne_nil hne
      simp [v₀,hxs]
    refine ⟨v₁,1+(n+1),hu,?_,Exec.seq hpeek (Exec.cond_true hflag he)⟩
    simp only [remainderPublicationControlsCost,if_pos hr]
    omega
  · have hz : S.R remainder = [] := List.length_eq_zero_iff.mp (by omega)
    have hflag : v₀.flag = false := by simp [v₀,hz]
    have hdone : Exec body (.act .done) (mk v₀ S) 1 (mk v₀ S) := by
      simpa [Action.run] using Exec.act (body := body) .done (mk v₀ S)
    refine ⟨v₀,3,rfl,by simp [remainderPublicationControlsCost,hr],?_⟩
    have he := Exec.seq hpeek (Exec.cond_false
      (p := clippedCorePublicationControls count coreWidth wordWidth product control saved tmp) hflag hdone)
    simpa [remainderPublicationControls,corePublication_remainder_gaps s width w hw,hr,gatherControls] using he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
