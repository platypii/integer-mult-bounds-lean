module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.BlocksWithin

/-! Linear preparation and recovery surround a bounded clean block. The
space reserve adds only boundary costs, independently of the core's runtime. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.Blocks
open IntegerMultBounds.Machine
open GraphContract (Runs)
open SharedBankStageInput (raw)
noncomputable section
variable {t a A B C : ℕ} {s r : Graph.Block t a} {x y z : Tapes t a}

def RawWithin (s : Graph.Block t a) (x y : Tapes t a) (time space : ℕ) : Prop :=
  ∀ lo hi : ℤ, (∀ n j, lo+(space : ℕ) ≤ (raw x n).head j ∧
    (raw x n).head j+(space : ℕ) ≤ hi) →
    HoareWithin s.program (· = raw x s.tapes) (· = raw y s.tapes) time
      (fun v => ∀ j, lo ≤ v.head j ∧ v.head j ≤ hi)

private theorem zero_margin {space : ℕ} {lo hi : ℤ}
    (h : ∀ n j, lo+(space : ℕ) ≤ (raw x n).head j ∧ (raw x n).head j+(space : ℕ) ≤ hi) :
    lo+(space : ℕ) ≤ 0 ∧ (space : ℤ) ≤ hi := by
  have hz := h (t+1) (Fin.last t)
  simpa only [raw,Fin.val_last,lt_self_iff_false,↓reduceDIte,zero_add] using hz

theorem before_within (hs : Leading s) (hr : Leading r)
    (h₁ : Runs s x y A) (h₂ : RawWithin r y z B C) :
    RawWithin (seqB s r) x z (A+B+1) (A+C) := by
  intro lo hi hm
  have hz := zero_margin hm
  have hw₁ := HoareWithin.of_time_heads h₁ lo hi (by
    rintro w rfl j
    have h := hm s.tapes j
    omega)
  have hw₂ := h₂ lo hi (by
    intro n j
    have h := hm n j
    have ht := raw_head_change h₁ n j
    omega)
  exact seq_within hs hr hw₁ hw₂ (by omega) (by omega)

theorem after_within (hs : Leading s) (hr : Leading r)
    (h₁ : RawWithin s x y A C) (h₂ : Runs r y z B) :
    RawWithin (seqB s r) x z (A+B+1) (C+B) := by
  intro lo hi hm
  have hz := zero_margin hm
  have hw₁ := h₁ (lo+(B : ℕ)) (hi-(B : ℕ)) (by
    intro n j
    have h := hm n j
    omega)
  have hy := post_raw_heads hw₁ (by omega) (by omega)
  have hw₂ := HoareWithin.of_time_heads h₂ lo hi (by
    rintro w rfl j
    have h := hy r.tapes j
    omega)
  exact seq_within hs hr
    (hw₁.consequence (J := fun v => ∀ j, lo ≤ v.head j ∧ v.head j ≤ hi)
      (fun _ h => h) (fun _ h => h) le_rfl (by intro v hv j; have h := hv j; omega))
    hw₂ (by omega) (by omega)

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.Blocks
