module

public import IntegerMultBounds.MathlibTM2.Routing.ReservoirMetadataPair
public import IntegerMultBounds.MathlibTM2.Routing.ReservoirScalarPrepare

/-! Combine both exchange metadata directions with six scalar converter inputs
on one shared bank, restoring all production scratch. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def reservoirBankScalarSlot : Fin 28 → Fin 29 := Fin.castSucc
def reservoirBankMetadataSlot : Fin 23 → Fin 29 :=
  fun j => if j = 22 then 28 else ⟨j.val, Nat.lt_trans j.isLt (by decide)⟩

theorem reservoirBankScalarSlot_injective : Function.Injective reservoirBankScalarSlot := by decide +kernel
theorem reservoirBankMetadataSlot_injective : Function.Injective reservoirBankMetadataSlot := by decide +kernel

def reservoirBankPrepareProgram (rg : Fin 29 → Fin T) (k : Fin 3) : Pr P T Q A U :=
  .seq (reservoirMetadataPairProgram (rg ∘ reservoirBankMetadataSlot) k)
    (reservoirScalarPrepareProgram (rg ∘ reservoirBankScalarSlot))

def reservoirBankPrepared (R : Fin T → List (Fin (A + 4))) (rg : Fin 29 → Fin T)
    (n H : ℕ) (hfit : 9 * H ≤ n) (w : ℕ) (hw : w ≤ H) (k : Fin 3) (L : ℕ) : Fin T → List (Fin (A + 4)) :=
  reservoirScalarOutputs (Function.update (Function.update R (rg 18)
    (middleLookupMetadata n H hfit w hw k L false ++ R (rg 18))) (rg 28)
    (middleLookupMetadata n H hfit w hw k L true ++ R (rg 28)))
    (rg ∘ reservoirBankScalarSlot) L n H w

theorem reservoirBankPrepare_exec (body : P → Pr P T Q A U)
    (rg : Fin 29 → Fin T) (hrg : Function.Injective rg) (L n H w : ℕ)
    (hn : n < 2 ^ L) (hfit : 9 * H ≤ n) (hw : w ≤ H) (k : Fin 3)
    (v : HS T Q A U) (S : Stacks T A)
    (hdimension : S.R (rg 0) = binSyms L n) (hreservoir : S.R (rg 1) = binSyms L H)
    (hspan : S.R (rg 2) = binSyms L w)
    (hblank : ∀ j : Fin 29, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 13 → j ≠ 18 → j ≠ 28 → S.R (rg j) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ 622 * L + 700 ∧
      Exec body (reservoirBankPrepareProgram rg k) (mk v S) m
        (mk v' { S with R := reservoirBankPrepared S.R rg n H hfit w hw k L }) := by
  have hmetaBlank : ∀ j : Fin 23, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 13 → j ≠ 18 → j ≠ 22 →
      S.R ((rg ∘ reservoirBankMetadataSlot) j) = [] := by
    intro j hj0 hj1 hj2 hj13 hj18 hj22
    simp only [Function.comp_apply, reservoirBankMetadataSlot, if_neg hj22]
    apply hblank
    · exact fun he => hj0 (Fin.ext (congrArg (fun a : Fin 29 => a.val) he))
    · exact fun he => hj1 (Fin.ext (congrArg (fun a : Fin 29 => a.val) he))
    · exact fun he => hj2 (Fin.ext (congrArg (fun a : Fin 29 => a.val) he))
    · exact fun he => hj13 (Fin.ext (congrArg (fun a : Fin 29 => a.val) he))
    · exact fun he => hj18 (Fin.ext (congrArg (fun a : Fin 29 => a.val) he))
    · intro he
      have hv := congrArg Fin.val he
      change j.val = 28 at hv
      omega
  obtain ⟨v₁, hu₁, he₁⟩ := reservoirMetadataPair_exec body (rg ∘ reservoirBankMetadataSlot)
    (hrg.comp reservoirBankMetadataSlot_injective) L n H w hn hfit hw k v S
    hdimension hreservoir hspan hmetaBlank
  let C : Stacks T A := { S with R := (Function.update (Function.update S.R (rg 18)
    (middleLookupMetadata n H hfit w hw k L false ++ S.R (rg 18))) (rg 28)
    (middleLookupMetadata n H hfit w hw k L true ++ S.R (rg 28))) }
  have keep (j : Fin 28) (hj : j ≠ 18) : C.R ((rg ∘ reservoirBankScalarSlot) j) =
      S.R ((rg ∘ reservoirBankScalarSlot) j) := by
    have hj28 : reservoirBankScalarSlot j ≠ 28 := by
      intro he
      have hv := congrArg Fin.val he
      change j.val = 28 at hv
      exact (Nat.ne_of_lt j.isLt) hv
    have hj18 : reservoirBankScalarSlot j ≠ 18 :=
      fun he => hj (Fin.ext (congrArg (fun a : Fin 29 => a.val) he))
    exact (Function.update_of_ne (hrg.ne hj28) _ _).trans (Function.update_of_ne (hrg.ne hj18) _ _)
  have hscalarBlank : ∀ j : Fin 28, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 13 → j ≠ 18 →
      C.R ((rg ∘ reservoirBankScalarSlot) j) = [] := by
    intro j hj0 hj1 hj2 hj13 hj18
    rw [keep j hj18]
    apply hblank
    · exact fun he => hj0 (Fin.ext (congrArg (fun a : Fin 29 => a.val) he))
    · exact fun he => hj1 (Fin.ext (congrArg (fun a : Fin 29 => a.val) he))
    · exact fun he => hj2 (Fin.ext (congrArg (fun a : Fin 29 => a.val) he))
    · exact fun he => hj13 (Fin.ext (congrArg (fun a : Fin 29 => a.val) he))
    · exact fun he => hj18 (Fin.ext (congrArg (fun a : Fin 29 => a.val) he))
    · intro he
      have hv := congrArg Fin.val he
      change j.val = 28 at hv
      exact (Nat.ne_of_lt j.isLt) hv
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := reservoirScalarPrepare_exec body (rg ∘ reservoirBankScalarSlot)
    (hrg.comp reservoirBankScalarSlot_injective) L n H w hn hfit hw v₁ C
    ((keep 0 (by decide)).trans hdimension) ((keep 1 (by decide)).trans hreservoir)
    ((keep 2 (by decide)).trans hspan) hscalarBlank
  exact ⟨v₂, (472 * L + 530) + m₂, hu₂.trans hu₁, by omega, Exec.seq he₁ he₂⟩

end IntegerMultBounds.MathlibTM2.Routing
