module

public import IntegerMultBounds.MathlibTM2.Routing.ReservoirMetadataGenerate

/-! Generate both coordinate-exchange directions on a shared reusable bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def reservoirMetadataForwardSlot : Fin 22 → Fin 23 := Fin.castSucc
def reservoirMetadataBackwardSlot : Fin 22 → Fin 23 :=
  Function.update reservoirMetadataForwardSlot 18 22

theorem reservoirMetadataForwardSlot_injective : Function.Injective reservoirMetadataForwardSlot := by
  decide +kernel

theorem reservoirMetadataBackwardSlot_injective : Function.Injective reservoirMetadataBackwardSlot := by
  decide +kernel

def reservoirMetadataPairProgram (rg : Fin 23 → Fin T) (k : Fin 3) : Pr P T Q A U :=
  .seq (reservoirMetadataProgram (rg ∘ reservoirMetadataForwardSlot) k false)
    (reservoirMetadataProgram (rg ∘ reservoirMetadataBackwardSlot) k true)

theorem reservoirMetadataPair_exec (body : P → Pr P T Q A U)
    (rg : Fin 23 → Fin T) (hrg : Function.Injective rg) (L n H w : ℕ)
    (hn : n < 2 ^ L) (hfit : 9 * H ≤ n) (hw : w ≤ H) (k : Fin 3)
    (v : HS T Q A U) (S : Stacks T A)
    (hdimension : S.R (rg 0) = binSyms L n) (hreservoir : S.R (rg 1) = binSyms L H)
    (hspan : S.R (rg 2) = binSyms L w)
    (hblank : ∀ j : Fin 23, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 13 → j ≠ 18 → j ≠ 22 → S.R (rg j) = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (reservoirMetadataPairProgram rg k) (mk v S) (472 * L + 530)
        (mk v' { S with R := (Function.update (Function.update S.R (rg 18)
          (middleLookupMetadata n H hfit w hw k L false ++ S.R (rg 18))) (rg 22)
          (middleLookupMetadata n H hfit w hw k L true ++ S.R (rg 22))) }) := by
  have hforwardBlank : ∀ j : Fin 22, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 13 → j ≠ 18 →
      S.R ((rg ∘ reservoirMetadataForwardSlot) j) = [] := by
    intro j hj0 hj1 hj2 hj13 hj18
    apply hblank
    · exact fun he => hj0 (Fin.ext (congrArg (fun a : Fin 23 => a.val) he))
    · exact fun he => hj1 (Fin.ext (congrArg (fun a : Fin 23 => a.val) he))
    · exact fun he => hj2 (Fin.ext (congrArg (fun a : Fin 23 => a.val) he))
    · exact fun he => hj13 (Fin.ext (congrArg (fun a : Fin 23 => a.val) he))
    · exact fun he => hj18 (Fin.ext (congrArg (fun a : Fin 23 => a.val) he))
    · intro he
      have hv := congrArg Fin.val he
      change j.val = 22 at hv
      exact (Nat.ne_of_lt j.isLt) hv
  obtain ⟨v₁, hu₁, he₁⟩ := reservoirMetadata_generate_exec body (rg ∘ reservoirMetadataForwardSlot)
    (hrg.comp reservoirMetadataForwardSlot_injective) L n H w hn hfit hw k false v S
    hdimension hreservoir hspan hforwardBlank
  let C : Stacks T A := { S with R := (Function.update S.R (rg 18)
    (middleLookupMetadata n H hfit w hw k L false ++ S.R (rg 18))) }
  have hkeep (j : Fin 22) : C.R ((rg ∘ reservoirMetadataBackwardSlot) j) =
      S.R ((rg ∘ reservoirMetadataBackwardSlot) j) := by
    apply Function.update_of_ne
    apply hrg.ne
    fin_cases j <;> decide
  have hbackwardBlank : ∀ j : Fin 22, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 13 → j ≠ 18 →
      C.R ((rg ∘ reservoirMetadataBackwardSlot) j) = [] := by
    intro j hj0 hj1 hj2 hj13 hj18
    rw [hkeep]
    simpa only [Function.comp_apply, reservoirMetadataBackwardSlot, Function.update_of_ne hj18]
      using hforwardBlank j hj0 hj1 hj2 hj13 hj18
  obtain ⟨v₂, hu₂, he₂⟩ := reservoirMetadata_generate_exec body (rg ∘ reservoirMetadataBackwardSlot)
    (hrg.comp reservoirMetadataBackwardSlot_injective) L n H w hn hfit hw k true v₁ C
    ((hkeep 0).trans hdimension) ((hkeep 1).trans hreservoir) ((hkeep 2).trans hspan) hbackwardBlank
  rw [hkeep 18] at he₂
  exact ⟨v₂, hu₂.trans hu₁, (Exec.seq he₁ he₂).cast (by ring) rfl⟩

end IntegerMultBounds.MathlibTM2.Routing
