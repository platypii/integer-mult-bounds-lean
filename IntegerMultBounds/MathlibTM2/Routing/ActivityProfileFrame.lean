module

public import IntegerMultBounds.MathlibTM2.Routing.OptionalBinaryProfileFrame
public import IntegerMultBounds.MathlibTM2.Routing.OptionalAffineSourceCall

/-! Read and archive raw activity after computing a source address, then emit
its active selector or an inactive frame. The selector survives either branch. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def activityProfileFrameProgram (activity saved selector dst tmp work : Fin T)
    (zr : BinaryZeroReg → Fin T) : Pr P T Q A U :=
  .seq (.act (sourceActivityArchive activity saved)) (optionalBinaryProfileFrameProgram selector dst tmp work zr)

def activityProfileFrameBank (R : Fin T → List (Fin (A + 4))) (activity saved dst : Fin T)
    (L q : ℕ) (enabled : Bool) (rest : List (Fin (A + 4))) :=
  Function.update (Function.update (Function.update R activity rest) saved (bitSymbol enabled :: R saved)) dst
    (affineProfileFrames L [(enabled, if enabled then q else 0)] ++ R dst)

theorem activityProfileFrame_exec (body : P → Pr P T Q A U)
    (activity saved selector dst tmp work : Fin T)
    (hreg : [activity, saved, selector, dst, tmp, work].Nodup)
    (zr : BinaryZeroReg → Fin T) (hzr : Function.Injective zr) (hdst : zr .dst = dst)
    (haZr : ∀ r, activity ≠ zr r) (hsZr : ∀ r, saved ≠ zr r)
    (Lw L q : ℕ) (hwidth : L < 2 ^ Lw) (enabled : Bool) (rest : List (Fin (A + 4)))
    (v : HS T Q A U) (S : Stacks T A)
    (hactivity : S.R activity = bitSymbol enabled :: rest)
    (hselector : S.R selector = binSyms L q) (htmp : S.R tmp = []) (hwork : S.R work = [])
    (hwidthInput : S.R (zr .width) = binSyms Lw L)
    (hunary : S.R (zr .unary) = []) (hscratch : ∀ r, S.R (zr (.scratch r)) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧ steps ≤ optionalBinaryProfileFrameCost Lw L + 1 ∧
      Exec body (activityProfileFrameProgram activity saved selector dst tmp work zr) (mk v S) steps
        (mk v' { S with R := activityProfileFrameBank S.R activity saved dst L q enabled rest }) := by
  have hn := hreg
  regs_ne hn
  let u := { v with sym := some (bitSymbol enabled), flag := enabled }
  let B : Stacks T A := { S with R := Function.update (Function.update S.R activity rest) saved (bitSymbol enabled :: S.R saved) }
  have hp : (sourceActivityArchive activity saved : Act T Q A U).run (mk v S) = mk u B := by
    simp [sourceActivityArchive, Action.run, update_rt, hactivity, u, B, ‹activity ≠ saved›.symm]
  have hzkeep (r : BinaryZeroReg) : B.R (zr r) = S.R (zr r) := by
    simp [B, (haZr r).symm, (hsZr r).symm]
  obtain ⟨v₁, m₁, hu₁, hm₁, hx₁⟩ := optionalBinaryProfileFrame_exec body selector dst tmp work (by regs_nodup)
    zr hzr hdst Lw L q hwidth enabled u B rfl
    (by simp [B, ‹activity ≠ selector›.symm, ‹saved ≠ selector›.symm, hselector])
    (by simp [B, ‹activity ≠ tmp›.symm, ‹saved ≠ tmp›.symm, htmp])
    (by simp [B, ‹activity ≠ work›.symm, ‹saved ≠ work›.symm, hwork])
    ((hzkeep .width).trans hwidthInput) ((hzkeep .unary).trans hunary)
    (fun r => (hzkeep (.scratch r)).trans (hscratch r))
  have hd : B.R dst = S.R dst := by simp [B, ‹activity ≠ dst›.symm, ‹saved ≠ dst›.symm]
  rw [hd] at hx₁
  exact ⟨v₁, 1 + m₁, hu₁, by omega, Exec.seq (hp ▸ Exec.act (body := body) _ (mk v S)) hx₁⟩

end IntegerMultBounds.MathlibTM2.Routing
