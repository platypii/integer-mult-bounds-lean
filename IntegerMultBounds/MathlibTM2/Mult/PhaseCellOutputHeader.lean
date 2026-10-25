module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellQuarterCount
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComplementHeader

/-! # Generate the final rescaling exponent from retained headers -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

/-- Add the two row-size contributions and the two guard bits. -/
def extendOutputShift (rows shift saved : Fin T) : Pr P T Q A U :=
  .seq (copyR rows shift saved id)
    (.seq (copyR rows shift saved id)
      (.act (.push (.rt shift) (fun _ => tick)
        (.push (.rt shift) (fun _ => tick) .done))))

theorem extendOutputShift_exec {rows shift saved : Fin T}
    (hreg : [rows, shift, saved].Nodup) (v : HS T Q A U) (S : Stacks T A)
    (hsaved : S.R saved = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (extendOutputShift rows shift saved) (mk v S)
        (8 * (S.R rows).length + 9)
        (mk v' { S with R := (Function.update S.R shift
          (tick :: tick :: (S.R rows).reverse ++ (S.R rows).reverse ++ S.R shift)) }) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, hu₁, he₁⟩ := copyR_exec body rows shift saved
    ‹rows ≠ shift› ‹rows ≠ saved› ‹shift ≠ saved› id v S hsaved
  let S₁ : Stacks T A := { S with R := (Function.update S.R shift
    ((S.R rows).reverse ++ S.R shift)) }
  have he₁' : Exec body (copyR rows shift saved id) (mk v S)
      (4 * (S.R rows).length + 4) (mk v₁ S₁) := by
    simpa only [List.map_id] using he₁
  obtain ⟨v₂, hu₂, he₂⟩ := copyR_exec body rows shift saved
    ‹rows ≠ shift› ‹rows ≠ saved› ‹shift ≠ saved› id v₁ S₁
    (by simpa [S₁, ‹shift ≠ saved›.symm] using hsaved)
  let S₂ : Stacks T A := { S with R := (Function.update S.R shift
    ((S.R rows).reverse ++ (S.R rows).reverse ++ S.R shift)) }
  have he₂' : Exec body (copyR rows shift saved id) (mk v₁ S₁)
      (4 * (S.R rows).length + 4) (mk v₂ S₂) := by
    simpa [S₁, S₂, ‹rows ≠ shift›, List.append_assoc] using he₂
  let act : Act T Q A U := .push (.rt shift) (fun _ => tick)
    (.push (.rt shift) (fun _ => tick) .done)
  have hp := Exec.act (body := body) act (mk v₂ S₂)
  have hp' : Exec body (.act act) (mk v₂ S₂) 1
      (mk v₂ { S with R := (Function.update S.R shift
        (tick :: tick :: (S.R rows).reverse ++ (S.R rows).reverse ++ S.R shift)) }) := by
    convert hp using 1; simp [act, Action.run, update_rt, S₂, List.append_assoc]
  exact ⟨v₂, hu₂.trans hu₁, (Exec.seq he₁' (Exec.seq he₂' hp')).cast (by omega) rfl⟩

/-- Produce b+2*l+2 from the quarter precision 4*b and retained row exponent l. -/
def outputShiftHeader (precision rows shift saved half : Fin T) : Pr P T Q A U :=
  .seq (quarterCount precision saved half shift) (extendOutputShift rows shift saved)

theorem outputShiftHeader_exec {precision rows shift saved half : Fin T}
    (hreg : [precision, rows, shift, saved, half].Nodup) (b : ℕ)
    (v : HS T Q A U) (S : Stacks T A)
    (hq : (S.R precision).length = 4 * b) (hshift : S.R shift = []) (hsaved : S.R saved = []) (hhalf : S.R half = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (outputShiftHeader precision rows shift saved half) (mk v S)
        (22 * b + 8 * (S.R rows).length + 19)
        (mk v' { S with R := (Function.update S.R shift
          (tick :: tick :: (S.R rows).reverse ++ (S.R rows).reverse ++ List.replicate b tick)) }) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, hu₁, he₁⟩ := quarterCount_exec (body := body)
    (show [precision, saved, half, shift].Nodup by simp_all [ne_comm]) b v S hq hsaved hhalf
  let S₁ : Stacks T A := { S with R := (Function.update S.R shift (List.replicate b tick)) }
  have he₁' : Exec body (quarterCount precision saved half shift) (mk v S) (22 * b + 10) (mk v₁ S₁) := by
    simpa only [hshift, List.append_nil] using he₁
  obtain ⟨v₂, hu₂, he₂⟩ := extendOutputShift_exec (body := body)
    (show [rows, shift, saved].Nodup by simp_all) v₁ S₁
    (by simpa [S₁, ‹shift ≠ saved›.symm] using hsaved)
  refine ⟨v₂, hu₂.trans hu₁, (Exec.seq he₁' he₂).cast ?_ ?_⟩
  · simp [S₁, ‹rows ≠ shift›]; omega
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases hk : k = shift
    · subst k; simp [S₁, ‹rows ≠ shift›]
    · simp [S₁, hk]

/-- Generate both controls required by the existing output scaling machine. -/
def outputHeaders (precision rows width shift rest saved tmp : Fin T) : Pr P T Q A U :=
  .seq (outputShiftHeader precision rows shift saved rest)
    (complementHeader width shift rest saved tmp)

theorem outputHeaders_exec {precision rows width shift rest saved tmp : Fin T}
    (hreg : [precision, rows, width, shift, rest, saved, tmp].Nodup) (b : ℕ)
    (v : HS T Q A U) (S : Stacks T A)
    (hq : (S.R precision).length = 4 * b)
    (hfit : b + 2 * (S.R rows).length + 2 ≤ (S.R width).length)
    (hshift : S.R shift = []) (hrest : S.R rest = [])
    (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    let d := b + 2 * (S.R rows).length + 2
    let shiftSymbols := tick :: tick :: (S.R rows).reverse ++ (S.R rows).reverse ++ List.replicate b tick
    ∃ v', v'.user = v.user ∧
      Exec body (outputHeaders precision rows width shift rest saved tmp) (mk v S)
        (22 * b + 8 * (S.R rows).length + 4 * (S.R width).length + 6 * d + 29)
        (mk v' { S with R := (Function.update (Function.update S.R shift shiftSymbols)
          rest ((S.R width).reverse.drop d)) }) := by
  dsimp only
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, hu₁, he₁⟩ := outputShiftHeader_exec (body := body)
    (show [precision, rows, shift, saved, rest].Nodup by simp_all [ne_comm]) b v S hq hshift hsaved hrest
  let shiftSymbols := tick :: tick :: (S.R rows).reverse ++ (S.R rows).reverse ++ List.replicate b tick
  let S₁ : Stacks T A := { S with R := (Function.update S.R shift shiftSymbols) }
  have hlen : (S₁.R shift).length = b + 2 * (S.R rows).length + 2 := by
    simp [S₁, shiftSymbols]; omega
  obtain ⟨v₂, hu₂, he₂⟩ := complementHeader_exec (body := body)
    (show [width, shift, rest, saved, tmp].Nodup by simp_all) v₁ S₁
    (by rw [hlen]; simpa only [S₁, Function.update_of_ne ‹width ≠ shift›] using hfit)
    (by simpa [S₁, ‹shift ≠ rest›.symm] using hrest)
    (by simpa [S₁, ‹shift ≠ saved›.symm] using hsaved)
    (by simpa [S₁, ‹shift ≠ tmp›.symm] using htmp)
  refine ⟨v₂, hu₂.trans hu₁, (Exec.seq he₁ he₂).cast ?_ ?_⟩
  · simp only [hlen, S₁, Function.update_of_ne ‹width ≠ shift›]
    omega
  · simp only [hlen, S₁, Function.update_of_ne ‹width ≠ shift›]
    rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
