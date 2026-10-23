module

public import IntegerMultBounds.MathlibTM2.Routing.OptionalAffineSourceFrame

/-! Read and archive one activity bit, then generate its affine or inactive
profile frame. No activity/source pair or selector word is supplied. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def sourceActivityArchive (src saved : Fin T) : Act T Q A U :=
  .pop (.rt src) (fun v x => { v with sym := x, flag := symBit (x.getD blank) })
    (.push (.rt saved) (fun v => v.sym.getD blank) .done)

def optionalAffineSourceCallProgram (rg : Fin 12 → Fin T) (zr : BinaryZeroReg → Fin T) (src saved : Fin T) : Pr P T Q A U :=
  .seq (.act (sourceActivityArchive src saved)) (optionalAffineSourceFrameProgram rg zr)

def optionalAffineSourceCallBank (R : Fin T → List (Fin (A + 4))) (src saved dst : Fin T)
    (L i k o : ℕ) (enabled : Bool) (rest : List (Fin (A + 4))) :=
  Function.update (Function.update (Function.update R src rest) saved (bitSymbol enabled :: R saved)) dst
    (affineProfileFrames L [(enabled, if enabled then i * k + o else 0)] ++ R dst)

theorem optionalAffineSourceCall_exec (body : P → Pr P T Q A U)
    (rg : Fin 12 → Fin T) (hrg : Function.Injective rg)
    (zr : BinaryZeroReg → Fin T) (hzr : Function.Injective zr) (hdst : zr .dst = rg 5)
    (src saved : Fin T) (hss : src ≠ saved)
    (hsrcRg : ∀ r, src ≠ rg r) (hsavedRg : ∀ r, saved ≠ rg r)
    (hsrcZr : ∀ r, src ≠ zr r) (hsavedZr : ∀ r, saved ≠ zr r)
    (Lw Li Lk i k o : ℕ) (hwidth : Li + Lk < 2 ^ Lw)
    (hi : i < 2 ^ Li) (hk : k < 2 ^ Lk) (hfit : i * k + o < 2 ^ (Li + Lk))
    (enabled : Bool) (rest : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = bitSymbol enabled :: rest)
    (hindex : S.R (rg 0) = binSyms Li i) (hstride : S.R (rg 1) = binSyms Lk k)
    (hoffset : S.R (rg 2) = binSyms (Li + Lk) o)
    (hblank : ∀ r : Fin 12, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 5 → S.R (rg r) = [])
    (hwidthInput : S.R (zr .width) = binSyms Lw (Li + Lk))
    (hunary : S.R (zr .unary) = []) (hzeroScratch : ∀ r, S.R (zr (.scratch r)) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧ steps ≤ optionalAffineSourceFrameCost Lw Li Lk + 1 ∧
      Exec body (optionalAffineSourceCallProgram rg zr src saved) (mk v S) steps
        (mk v' { S with R := optionalAffineSourceCallBank S.R src saved (rg 5) (Li + Lk) i k o enabled rest }) := by
  let u := { v with sym := some (bitSymbol enabled), flag := enabled }
  let B : Stacks T A := { S with R := Function.update (Function.update S.R src rest) saved (bitSymbol enabled :: S.R saved) }
  have hp : (sourceActivityArchive src saved : Act T Q A U).run (mk v S) = mk u B := by
    simp [sourceActivityArchive, Action.run, update_rt, hsrc, u, B, hss.symm]
  have hrgkeep (r : Fin 12) : B.R (rg r) = S.R (rg r) := by simp [B, (hsrcRg r).symm, (hsavedRg r).symm]
  have hzrkeep (r : BinaryZeroReg) : B.R (zr r) = S.R (zr r) := by simp [B, (hsrcZr r).symm, (hsavedZr r).symm]
  obtain ⟨v₁, m₁, hu₁, hm₁, hx₁⟩ := optionalAffineSourceFrame_exec body rg hrg zr hzr hdst
    Lw Li Lk i k o hwidth hi hk hfit enabled u B rfl ((hrgkeep 0).trans hindex)
    ((hrgkeep 1).trans hstride) ((hrgkeep 2).trans hoffset)
    (fun r h0 h1 h2 h5 => (hrgkeep r).trans (hblank r h0 h1 h2 h5))
    ((hzrkeep .width).trans hwidthInput) ((hzrkeep .unary).trans hunary)
    (fun r => (hzrkeep (.scratch r)).trans (hzeroScratch r))
  rw [hrgkeep 5] at hx₁
  exact ⟨v₁, 1 + m₁, hu₁, by omega, Exec.seq (hp ▸ Exec.act (body := body) _ (mk v S)) hx₁⟩

end IntegerMultBounds.MathlibTM2.Routing
