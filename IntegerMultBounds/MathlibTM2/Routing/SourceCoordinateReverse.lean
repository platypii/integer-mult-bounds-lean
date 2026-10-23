module

public import IntegerMultBounds.MathlibTM2.Routing.SourceCoordinateCall
public import IntegerMultBounds.MathlibTM2.Routing.AffineProfileCoordinates

/-! Accumulate compiled source records in reverse while restoring the temporary
record destination. Both raw input and output remain ready for final rewind. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def sourceCoordinateReverseProgram (rg : Fin 21 → Fin T) (src saved tmp accum : Fin T) : Pr P T Q A U :=
  .seq (sourceCoordinateCallProgram rg src saved tmp) (moveR (rg 19) accum id)

def sourceCoordinateReverseBank (R : Fin T → List (Fin (A + 4))) (src saved accum : Fin T)
    (Li Lk q low high k : ℕ) (enabled : Bool) (rest : List (Fin (A + 4))) :=
  Function.update (Function.update (Function.update R src rest)
    saved ((sourceCoordinateInputRecord Li Lk q enabled).reverse ++ R saved)) accum
    (((sourceCoordinateChoice q low high k enabled).word Li Lk).reverse ++ R accum)

def sourceCoordinateIterationCost (Li Lk : ℕ) :=
  sourceCoordinateRecordCost Li Lk + 6 * (Li + Lk) + 22 + 2 * (Li + (Li + Lk) + 5) + 4

theorem sourceCoordinateReverse_exec (body : P → Pr P T Q A U)
    (rg : Fin 21 → Fin T) (hrg : Function.Injective rg) (src saved tmp accum : Fin T)
    (hreg : [src, saved, tmp, accum].Nodup)
    (hsrc : ∀ j, src ≠ rg j) (hsaved : ∀ j, saved ≠ rg j) (htmp : ∀ j, tmp ≠ rg j)
    (hacc : ∀ j, accum ≠ rg j)
    (Li Lk q low high k : ℕ) (enabled : Bool)
    (hq : q < 2 ^ (Li + Lk)) (hlow : low < 2 ^ (Li + Lk)) (hhigh : high < 2 ^ (Li + Lk))
    (hk : k < 2 ^ Lk) (hk0 : 0 < k)
    (rest : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A)
    (setup : SourceCoordinateSetup rg Li Lk low high k S)
    (hraw : S.R src = sourceCoordinateInputRecord Li Lk q enabled ++ rest)
    (htmpBlank : S.R tmp = []) (houtput : S.R (rg 19) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps + 2 ≤ sourceCoordinateIterationCost Li Lk ∧
      Exec body (sourceCoordinateReverseProgram rg src saved tmp accum) (mk v S) steps
        (mk v' { S with R := sourceCoordinateReverseBank S.R src saved accum Li Lk q low high k enabled rest }) := by
  have hn := hreg
  regs_ne hn
  obtain ⟨v₁, m₁, hu₁, hm₁, hx₁⟩ := sourceCoordinateCall_exec body rg hrg src saved tmp (by regs_nodup)
    hsrc hsaved htmp Li Lk q low high k enabled hq hlow hhigh hk hk0 rest v S setup hraw htmpBlank
  let G : Stacks T A := { S with R := sourceCoordinateCallBank S.R src saved (rg 19) Li Lk q low high k enabled rest }
  let word := (sourceCoordinateChoice q low high k enabled).word (A := A) Li Lk
  have hf : G.R (rg 19) = word := by simp [G, sourceCoordinateCallBank, houtput, word]
  obtain ⟨v₂, hu₂, hx₂⟩ := moveR_exec (body := body) (rg 19) accum (hacc 19).symm id v₁ G
  have hbank : movedR G.R (rg 19) accum id (G.R (rg 19)) =
      sourceCoordinateReverseBank S.R src saved accum Li Lk q low high k enabled rest := by
    funext j
    by_cases hd : j = rg 19
    · subst j
      simp [movedR, sourceCoordinateReverseBank, (hacc 19).symm, (hsrc 19).symm, (hsaved 19).symm, houtput]
    · by_cases ha : j = accum
      · subst j
        simp [movedR, G, sourceCoordinateCallBank, sourceCoordinateReverseBank,
          ‹src ≠ accum›.symm, ‹saved ≠ accum›.symm, hacc 19, houtput]
      · simp [movedR, G, sourceCoordinateCallBank, sourceCoordinateReverseBank, Function.update_apply, hd, ha]
  have hlen : word.length = Li + (Li + Lk) + 5 := GatedSelectedSourceChoice.word_length _ Li Lk
  rw [hbank, hf, hlen] at hx₂
  exact ⟨v₂, m₁ + (2 * (Li + (Li + Lk) + 5) + 2), hu₂.trans hu₁,
    by unfold sourceCoordinateIterationCost; omega, Exec.seq hx₁ hx₂⟩

end IntegerMultBounds.MathlibTM2.Routing
