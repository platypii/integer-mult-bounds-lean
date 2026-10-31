module

public import IntegerMultBounds.MathlibTM2.Host.WordCmdStock
public import IntegerMultBounds.MathlibTM2.Host.EmbedStock

/-! Closed programs and their embeddings need no procedure-body resource oracle.
Use their atomic push bound only for shared setup or linear traffic. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host.WordCmd
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast.Main

theorem noCalls_empty {K : Type} {Γ : K → Type} {σ : Type} (p : Prog Empty Γ σ) :
    NoCalls p := by
  induction p with
  | act a => trivial
  | seq p q hp hq => exact ⟨hp,hq⟩
  | cond f p q hp hq => exact ⟨hp,hq⟩
  | loop f p hp => exact hp
  | call f => exact nomatch f

theorem noCalls_of_native {K : Type} {Γ : K → Type} {σ P : Type}
    {p : Prog P Γ σ} {c : ℕ} (h : mnNativePushBound c p) : NoCalls p := by
  induction p with
  | act a => trivial
  | seq p q hp hq => exact ⟨hp h.1,hq h.2⟩
  | cond f p q hp hq => exact ⟨hp h.1,hq h.2⟩
  | loop f p hp => exact hp h
  | call f => exact h.elim

theorem empty_native {K : Type} {Γ : K → Type} {σ : Type} (p : Prog Empty Γ σ) :
    mnNativePushBound (mnProgPush p) p := native_of_noCalls (noCalls_empty p) le_rfl

end IntegerMultBounds.MathlibTM2.Host.WordCmd
