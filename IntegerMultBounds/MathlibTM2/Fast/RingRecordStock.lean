module

public import IntegerMultBounds.MathlibTM2.Host.WordCmdStock
public import IntegerMultBounds.MathlibTM2.Host.WordBankStock
public import IntegerMultBounds.Schoenhage.RingRecord

/-! Persistent record-bank stock changes only by completed output bits.
The record cost supplies one scratch allowance to the structural loop proof. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Host.WordCmd IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds.Schoenhage IntegerMultBounds.Schoenhage.Tp
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def ringRecordCost (Wd r w s N : ℕ) : ℕ :=
  r*(56*w+400)+ringCost Wd r w s N+202

/-- Archiving consumed operands preserves their total cells. Only completed
output bits increase the stock of the persistent record bank. -/
theorem ringRecord_boundary_stock (τ : Fin 𝕌 → WTape)
    (Pf Rf Lf Pg Rg Lg : List (List Bool)) (acc output : List Bool)
    (hP : τ iP = ⟨Lf,Pf++Rf⟩) (hL : τ iL = ⟨Lg,Pg++Rg⟩) (hZ : τ zO = ⟨[acc],[]⟩) :
    wordBankStock (Function.update (Function.update (Function.update τ
      iP ⟨Pf.reverse++Lf,Rf⟩) iL ⟨Pg.reverse++Lg,Rg⟩) zO ⟨[acc++output],[]⟩) =
      wordBankStock τ+output.length := by
  let τ₁ := Function.update τ iP (⟨Pf.reverse++Lf,Rf⟩ : WTape)
  let τ₂ := Function.update τ₁ iL (⟨Pg.reverse++Lg,Rg⟩ : WTape)
  have hp := wordBankStock_update τ iP (⟨Pf.reverse++Lf,Rf⟩ : WTape)
  have hl := wordBankStock_update τ₁ iL (⟨Pg.reverse++Lg,Rg⟩ : WTape)
  have hz := wordBankStock_update τ₂ zO (⟨[acc++output],[]⟩ : WTape)
  have hτ₁ : τ₁ iL = τ iL := Function.update_of_ne (by decide) _ _
  have hτ₂ : τ₂ zO = τ zO := by
    dsimp only [τ₂,τ₁]
    rw [Function.update_of_ne (by decide),Function.update_of_ne (by decide)]
  change wordBankStock τ₁+_ = _ at hp
  change wordBankStock τ₂+_ = _ at hl
  simp only [hP,hL,hZ,hτ₁,hτ₂,clen_append,clen_reverse,clen_cons,clen_nil,List.length_append] at hp hl hz
  change wordBankStock (Function.update τ₂ zO ⟨[acc++output],[]⟩) = _
  omega

private theorem flatMap_length_le {α β : Type} (xs : List α) (f : α → List β) (b : ℕ)
    (h : ∀ x ∈ xs, (f x).length ≤ b) : (xs.flatMap f).length ≤ xs.length*b := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have hs := ih (fun y hy => h y (by simp [hy]))
    simp only [List.flatMap_cons,List.length_append,List.length_cons]
    nlinarith only [hx,hs]

/-- All completed records occupy only their encoded output volume. -/
theorem ringRecordOutput_length_le (Wd r w s N : ℕ)
    (ps : List (List (List Bool × List Bool) × List (List Bool × List Bool))) :
    (ps.flatMap (fun q => ((ringWords Wd r w s N q.1 q.2).map List.reverse).flatten)).length ≤
      ps.length*(2*r*w) := by
  apply flatMap_length_le
  intro q _
  have h := flatMap_length_le (ringWords Wd r w s N q.1 q.2) List.reverse w (by
    intro x hx
    simpa only [List.length_reverse] using ringWords_le x hx)
  simpa only [List.flatMap_def,ringWords_length] using h

end IntegerMultBounds.MathlibTM2.Fast
