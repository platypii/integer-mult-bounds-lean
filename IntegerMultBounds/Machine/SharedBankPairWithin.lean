module

public import IntegerMultBounds.Machine.SharedBankPair
public import IntegerMultBounds.Machine.HoareWithinPlacement

/-! Shared-bank physical composition reuses one head interval, including
stationary stripped metadata and the actual sequence transition. -/
@[expose] public section
namespace IntegerMultBounds.Machine.SharedBank
noncomputable section
variable {k t q a B : ℕ} {M : Program t q a} {v w : Tapes t a} {lo hi : ℤ}

theorem stage_within
    (h : HoareWithin M (· = v) (· = w) B (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi))
    (slots : Fin k → Fin t) (hinj : Function.Injective slots) (hlo : lo ≤ 0) (hhi : 0 ≤ hi) :
    HoareWithin (Placement.placed M (placement slots)) (· = bank v slots) (· = bank w slots) B
      (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi) := by
  have hp := HoareWithin.placed_heads_at h (placement slots) (bank v slots) (active_bank v slots) (by
    rw [extra_bank v slots hinj]
    intro j
    exact ⟨hlo,hhi⟩)
  apply HoareWithin.of_time_invariant (stage_hoare h.time slots hinj)
  intro z hz
  exact hp.invariant hz

theorem strip_heads (slots : Fin k → Fin t) (hlo : lo ≤ 0) (hhi : 0 ≤ hi)
    (hv : ∀ j, lo ≤ v.head j ∧ v.head j ≤ hi) :
    ∀ j, lo ≤ (strip v slots).head j ∧ (strip v slots).head j ≤ hi := by
  intro j
  change lo ≤ (if ∃ i, slots i = j then 0 else v.head j) ∧
    (if ∃ i, slots i = j then 0 else v.head j) ≤ hi
  split_ifs <;> first | exact ⟨hlo,hhi⟩ | exact hv j

end
end IntegerMultBounds.Machine.SharedBank

namespace IntegerMultBounds.Machine.SharedBankPair
noncomputable section
variable {k t u q r a m n : ℕ} {M : Program t q a} {N : Program u r a}
  {v w : Tapes t a} {x y : Tapes u a} {lo hi : ℤ}

theorem pair_within
    (hM : HoareWithin M (· = v) (· = w) m (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi))
    (hN : HoareWithin N (· = x) (· = y) n (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi))
    (slots : Fin k → Fin t) (hinj : Function.Injective slots)
    (slots' : Fin k → Fin u) (hinj' : Function.Injective slots')
    (hcommon : SharedBank.payload w slots = SharedBank.payload x slots')
    (hlo : lo ≤ 0) (hhi : 0 ≤ hi) :
    HoareWithin (program M N slots slots') (· = input v x slots slots') (· = output w y slots slots')
      (m+n+1) (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi) := by
  have hx : ∀ j, lo ≤ x.head j ∧ x.head j ≤ hi := by
    obtain ⟨l,hl,c,hr,hh,hp⟩ := hN x rfl
    exact hr.initial
  have hw : ∀ j, lo ≤ w.head j ∧ w.head j ≤ hi := by
    obtain ⟨l,hl,c,hr,hh,hp⟩ := hM v rfl
    have hf := hr.finish
    rwa [hp] at hf
  have hm := HoareWithin.extend_heads_eq (SharedBank.strip x slots') lo hi
    (SharedBank.stage_within hM slots hinj hlo hhi) (SharedBank.strip_heads slots' hlo hhi hx)
  have hn := SharedBank.stage_within hN slots' hinj' hlo hhi
  have ha : Placement.active (placement k t u) ((SharedBank.bank w slots).append (SharedBank.strip x slots')) =
      SharedBank.bank x slots' := by
    rw [SharedBank.bank,active_bank,hcommon]
    rfl
  have hh := HoareWithin.placed_heads_at hn (placement k t u)
    ((SharedBank.bank w slots).append (SharedBank.strip x slots')) ha (by
      rw [SharedBank.bank,extra_bank]
      exact SharedBank.strip_heads slots hlo hhi hw)
  have hh' : HoareWithin (Placement.placed (Placement.placed N (SharedBank.placement slots')) (placement k t u))
      (· = (SharedBank.bank w slots).append (SharedBank.strip x slots'))
      (· = output w y slots slots') n (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi) := by
    apply hh.consequence (fun _ h => h) ?_ le_rfl (fun _ h => h)
    rintro z ⟨small,hsmall,rfl⟩
    subst small
    simp only [Placement.replace,SharedBank.bank,extra_bank,combine_bank,output]
  exact (hm.seq hh').consequence (fun _ h => h) (fun _ h => h) (by omega) (fun _ h => h)

end
end IntegerMultBounds.Machine.SharedBankPair
