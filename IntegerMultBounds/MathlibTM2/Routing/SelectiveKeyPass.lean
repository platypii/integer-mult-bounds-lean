module

public import IntegerMultBounds.MathlibTM2.Routing.SelectiveKeyEmitter

/-!
# Complete executed destination keying for selective repair

Emit the actual arbitrary-source ideal destination of each input record, including
its row bits. Copy records, advance the counters, restore forward stream order
and reset all six index counters. Every register except the stream is restored.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

variable {T Q A : ℕ} {P U : Type}

def selectiveKeyPass (ι : PatternReg 6 → Fin T) (src acc ctr tmp : Fin T) : Pr P T Q A U :=
  keyStream (selectiveKeyEmitter ι acc) (fun f => ι (.fld f)) src acc ctr tmp (ι .st)

def selectiveKeyPassCost (p : Par) (X rb M B : ℕ) : ℕ :=
  1 + (M * (keyRecordCost (selectiveKeyEmitterCost p X rb) B (selectiveKeyLen p X rb) + 1) + 1) +
    (2 * (M * (fieldsLen (selectiveKeyLen p X rb) + B)) + 2) +
    (4 * fieldsLen (selectiveKeyLen p X rb) + 4 * 6 + 1)

/-- Closed complete-keying ledger, including stream restoration and counter reset. -/
theorem selectiveKeyPassCost_eq (p : Par) (X rb M B : ℕ) :
    selectiveKeyPassCost p X rb M B =
      M * (selectiveKeyEmitterCost p X rb + 6 * B + 6 * fieldsLen (selectiveKeyLen p X rb) + 33) +
        4 * fieldsLen (selectiveKeyLen p X rb) + 29 := by
  unfold selectiveKeyPassCost keyRecordCost fieldsLen
  ring

def selectiveUniformKeyPassCost (n rb M B : ℕ) : ℕ :=
  M * (n * (6 * n + 25) + 19 * n + 11 * rb + 6 * B + 99) + 4 * (n + rb) + 29

theorem selectiveKeyPassCost_le (p : Par) (X rb M B n : ℕ)
    (hfields : fieldsLen (selectiveLen p X) = n) :
    selectiveKeyPassCost p X rb M B ≤ selectiveUniformKeyPassCost n rb M B := by
  have he := selectiveKeyEmitterCost_le p X rb n hfields
  rw [selectiveKeyPassCost_eq, selectiveKeyWidth, hfields]
  unfold selectiveUniformKeyPassCost
  have hc : selectiveKeyEmitterCost p X rb + 6 * B + 6 * (n + rb) + 33 ≤
      n * (6 * n + 25) + 19 * n + 11 * rb + 6 * B + 99 := by omega
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_left M hc) (4 * (n + rb))) 29

/-- The full fixed keying program supplies the exact ideal-rank keys needed by
repair; no supplied emitter or precomputed source-word contract remains. -/
theorem selectiveKeyPass_exec (p : Par) (X rb : ℕ) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)
    (hs : ∀ c, (s c).Allowed active) (body : P → Pr P T Q A U)
    (ι : PatternReg 6 → Fin T) (hι : Function.Injective ι) (src acc ctr tmp : Fin T)
    (hsrcbank : ∀ r, ι r ≠ src) (haccbank : ∀ r, ι r ≠ acc)
    (driver : KeyDriverRegs (fun f => ι (.fld f)) src acc ctr tmp)
    {R B : ℕ} (hB : 1 ≤ B) (l : List (List (Fin (A + 4))))
    (hl : l.length = R * 2 ^ fieldsLen (selectiveLen p X)) (hlen : ∀ r ∈ l, r.length = B)
    (v : HS T Q A U) (S : Stacks T A) (hI : KeyPatternInv p X rb active s ι S.R 0)
    (hsrc : S.R src = l.flatten) (hacc : S.R acc = []) (hctr : (S.R ctr).length = B)
    (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (selectiveKeyPass ι src acc ctr tmp) (mk v S)
        (selectiveKeyPassCost p X rb (R * 2 ^ fieldsLen (selectiveLen p X)) B)
        (mk v' { S with R := Function.update S.R src (keyRecs (fieldsLen (selectiveKeyLen p X rb)) (selectiveIdealPerm hK active s R hs) l).flatten }) := by
  have hkey : ∀ i, (selectiveKeyBits (A := A) p X rb active s i).length =
      fieldsLen (selectiveKeyLen p X rb) := by
    intro i
    simp [selectiveKeyBits, List.length_flatMap, fieldsLen, Fin.sum_univ_def]
  obtain ⟨v', hu, he⟩ := keyStream_exec body
    (selectiveKeyEmitter_spec p X rb active s hK body ι hι src acc hsrcbank haccbank)
    driver hB hkey l hlen v S hI hsrc hacc hctr htmp
  rw [selectiveKeyedFrom p X rb hK active s hs l hl] at he
  exact ⟨v', hu, Exec.cast he (by simp only [selectiveKeyPassCost, fieldsLen, hl]) rfl⟩

end IntegerMultBounds.MathlibTM2.Routing
