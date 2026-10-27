module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPowerWord
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellMovePrefix

/-! Set one real bit in an owned zero word, restoring the position header and every scratch tape. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def setPowerWord (count src parked saved tmp : Fin T) : Pr P T Q A U :=
  .seq (movePrefix count src parked saved tmp)
    (.seq (.act (dropTop src (.push (.rt src) (fun _ => pairSym A true false) .done))) (moveR parked src id))

theorem setPowerWord_exec {count src parked saved tmp : Fin T} (hreg : [count,src,parked,saved,tmp].Nodup)
    (w e : ℕ) (he : e < w) (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hcount : (S.R count).length = e) (hsrc : S.R src = csyms A w 0++tail)
    (hparked : S.R parked = []) (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧ Exec body (setPowerWord count src parked saved tmp) (mk v S) (8*e+9)
      (mk v' {S with R := Function.update S.R src (csyms A w (⟨(2 : ℤ)^e,0⟩ : GaussianInt)++tail)}) := by
  have hr := hreg
  regs_ne hr
  let z := pairSym A false false
  let rest := List.replicate (w-e-1) z++tail
  have hzero : List.replicate w z = List.replicate e z++z::List.replicate (w-e-1) z := by
    calc
      _ = List.replicate (e+(w-e-1+1)) z := by congr 1; omega
      _ = List.replicate e z++List.replicate (w-e-1+1) z := List.replicate_add _ _ _
      _ = _ := by rw [List.replicate_succ]
  obtain ⟨v₁,hu₁,he₁⟩ := movePrefix_exec (body := body) hreg (List.replicate e z) (z::rest) v S
    (by simpa [csyms_zero,z,hzero,rest,List.append_assoc] using hsrc)
    (by simpa using hcount) hsaved htmp
  let S₁ : Stacks T A := {S with R := Function.update (Function.update S.R src (z::rest)) parked (List.replicate e z)}
  have he₁' : Exec body (movePrefix count src parked saved tmp) (mk v S) (6*e+6) (mk v₁ S₁) := by
    simpa [S₁,hparked] using he₁
  let S₂ : Stacks T A := {S₁ with R := Function.update S₁.R src (pairSym A true false::rest)}
  have he₂ : Exec body (.act (dropTop src (.push (.rt src) (fun _ => pairSym A true false) .done)))
      (mk v₁ S₁) 1 (mk v₁ S₂) := by
    simpa [S₂,S₁,dropTop,Action.run,update_rt,‹src ≠ parked›] using
      Exec.act (body := body) (dropTop src (.push (.rt src) (fun _ => pairSym A true false) .done)) (mk v₁ S₁)
  obtain ⟨v₂,hu₂,he₃⟩ := moveR_exec body parked src ‹src ≠ parked›.symm id v₁ S₂
  have hlen : (S₂.R parked).length = e := by simp [S₂,S₁,‹src ≠ parked›.symm]
  refine ⟨v₂,hu₂.trans hu₁,(Exec.seq he₁' (Exec.seq he₂ he₃)).cast (by rw [hlen]; omega) ?_⟩
  apply congrArg (mk v₂)
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases his : i = src <;> by_cases hip : i = parked <;>
    simp [S₂,S₁,movedR,his,hip,hparked,‹src ≠ parked›,‹src ≠ parked›.symm,
      csyms_pow_two A w e he,z,rest,List.append_assoc]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
