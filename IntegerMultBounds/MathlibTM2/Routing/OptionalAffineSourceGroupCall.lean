module

public import IntegerMultBounds.MathlibTM2.Routing.OptionalAffineSourceGroupStep
public import IntegerMultBounds.MathlibTM2.Routing.OptionalAffineSourceCall

/-! Consume and archive one raw activity bit, emit its complete source group,
and advance the group index. Only source, archive, index and output change. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def optionalAffineSourceGroupCallProgram (rg : Fin 12 → Fin T)
    (zr : BinaryZeroReg → Fin T) (rp : Fin 7 → Fin T) (src saved : Fin T) : Pr P T Q A U :=
  .seq (.act (sourceActivityArchive src saved)) (optionalAffineSourceGroupStepProgram rg zr rp)

def optionalAffineSourceGroupCallBank (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 12 → Fin T) (rp : Fin 7 → Fin T) (src saved : Fin T)
    (Li Lk i k o g : ℕ) (enabled : Bool) (rest : List (Fin (A + 4))) :=
  optionalAffineSourceGroupStepBank
    (Function.update (Function.update R src rest) saved (bitSymbol enabled :: R saved))
    rg rp Li Lk i k o g enabled

theorem optionalAffineSourceGroupCall_exec (body : P → Pr P T Q A U)
    (rg : Fin 12 → Fin T) (hrg : Function.Injective rg)
    (zr : BinaryZeroReg → Fin T) (hzr : Function.Injective zr) (hdst : zr .dst = rg 5)
    (rp : Fin 7 → Fin T) (hrp : Function.Injective rp) (hsep : ∀ r, rp r ≠ rg 5)
    (hdsep : ∀ r, rp 3 ≠ rg r)
    (src saved : Fin T) (hss : src ≠ saved)
    (hsrcRg : ∀ r, src ≠ rg r) (hsavedRg : ∀ r, saved ≠ rg r)
    (hsrcZr : ∀ r, src ≠ zr r) (hsavedZr : ∀ r, saved ≠ zr r)
    (hsrcRp : ∀ r, src ≠ rp r) (hsavedRp : ∀ r, saved ≠ rp r)
    (Lg g : ℕ) (hg : g < 2 ^ Lg)
    (Lw Li Lk i k o : ℕ) (hwidth : Li + Lk < 2 ^ Lw)
    (hi : i < 2 ^ Li) (hk : k < 2 ^ Lk) (hfit : i * k + o < 2 ^ (Li + Lk))
    (enabled : Bool) (rest : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = bitSymbol enabled :: rest)
    (hindex : S.R (rg 0) = binSyms Li i) (hstride : S.R (rg 1) = binSyms Lk k)
    (hoffset : S.R (rg 2) = binSyms (Li + Lk) o)
    (hblank : ∀ r : Fin 12, r ≠ 0 → r ≠ 1 → r ≠ 2 → S.R (rg r) = [])
    (hwidthInput : S.R (zr .width) = binSyms Lw (Li + Lk))
    (hunary : S.R (zr .unary) = []) (hzeroScratch : ∀ r, S.R (zr (.scratch r)) = [])
    (hgroup : S.R (rp 0) = binSyms Lg g)
    (hcount : S.R (rp 1) = []) (hsaved : S.R (rp 2) = [])
    (hwork : S.R (rp 4) = []) (htmp : S.R (rp 5) = []) (hctmp : S.R (rp 6) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧ steps ≤ optionalAffineSourceFrameCost Lw Li Lk + binaryWordRepeatCost Lg g (Li + Lk + 3) + (2 * (Li + Lk + 3) + 2) + (4 * Li + 5) + 1 ∧
      Exec body (optionalAffineSourceGroupCallProgram rg zr rp src saved) (mk v S) steps
        (mk v' { S with R := optionalAffineSourceGroupCallBank S.R rg rp src saved Li Lk i k o g enabled rest }) := by
  let u := { v with sym := some (bitSymbol enabled), flag := enabled }
  let B : Stacks T A := { S with R := Function.update (Function.update S.R src rest) saved (bitSymbol enabled :: S.R saved) }
  have hp : (sourceActivityArchive src saved : Act T Q A U).run (mk v S) = mk u B := by
    simp [sourceActivityArchive, Action.run, update_rt, hsrc, u, B, hss.symm]
  have hrgkeep (r : Fin 12) : B.R (rg r) = S.R (rg r) := by simp [B, (hsrcRg r).symm, (hsavedRg r).symm]
  have hzrkeep (r : BinaryZeroReg) : B.R (zr r) = S.R (zr r) := by simp [B, (hsrcZr r).symm, (hsavedZr r).symm]
  have hrpkeep (r : Fin 7) : B.R (rp r) = S.R (rp r) := by simp [B, (hsrcRp r).symm, (hsavedRp r).symm]
  obtain ⟨v₁, m₁, hu₁, hm₁, hx₁⟩ := optionalAffineSourceGroupStep_exec body rg hrg zr hzr hdst rp hrp hsep hdsep
    Lg g hg Lw Li Lk i k o hwidth hi hk hfit enabled u B rfl
    ((hrgkeep 0).trans hindex) ((hrgkeep 1).trans hstride) ((hrgkeep 2).trans hoffset)
    (fun r h0 h1 h2 => (hrgkeep r).trans (hblank r h0 h1 h2))
    ((hzrkeep .width).trans hwidthInput) ((hzrkeep .unary).trans hunary)
    (fun r => (hzrkeep (.scratch r)).trans (hzeroScratch r))
    ((hrpkeep 0).trans hgroup) ((hrpkeep 1).trans hcount) ((hrpkeep 2).trans hsaved)
    ((hrpkeep 4).trans hwork) ((hrpkeep 5).trans htmp) ((hrpkeep 6).trans hctmp)
  exact ⟨v₁, 1 + m₁, hu₁, by omega, Exec.seq (hp ▸ Exec.act (body := body) _ (mk v S)) hx₁⟩

end IntegerMultBounds.MathlibTM2.Routing
