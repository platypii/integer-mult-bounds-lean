module

public import IntegerMultBounds.Machine.SharedBankFamily
public import IntegerMultBounds.Machine.RunWithinFrame

/-! A clean block's checked prefix head bounds survive fixed family padding.
The returned witness retains its actual time, halt and exact postcondition. -/
@[expose] public section
namespace IntegerMultBounds.Machine.SharedBankFamily
open SharedBankStageInput (raw)
noncomputable section
variable {k t n q a : ℕ}

theorem pad_within_heads (M : Program t q a) (h : t ≤ n) (hkt : k ≤ t)
    (before after : Tapes k a) (cost : ℕ)
    (hh : HoareTime M (· = raw before t) (· = raw after t) cost)
    (lo hi : ℤ) (hlo : lo ≤ 0) (hhi : 0 ≤ hi)
    (hheads : ∀ c, RunInvariant M (· = raw before t) c → ∀ i, lo ≤ c.head i ∧ c.head i ≤ hi) :
    ∃ m ≤ cost, ∃ d,
      RunWithin (padProgram M h) (fun v => ∀ i, lo ≤ v.head i ∧ v.head i ≤ hi) m
        ((raw before n).start (padProgram M h)) d ∧
      step (padProgram M h) d = none ∧ d.tapes = raw after n := by
  obtain ⟨m,d,hm,hr,hd,hpost⟩ := hh _ rfl
  let extra := SharedBank.empty (n-t) a
  let e := finCongr (Nat.add_sub_of_le h)
  let H : TapePred n a := fun v => ∀ i, lo ≤ v.head i ∧ v.head i ≤ hi
  have hw : RunWithin M (fun v => H ((v.append extra).reindex e)) m ((raw before t).start M) d := by
    refine ⟨hr,?_⟩
    intro l hl z hz i
    have hb := hheads z ⟨raw before t,rfl,l,hz⟩
    change lo ≤ (z.tapes.append extra).head (e.symm i) ∧
      (z.tapes.append extra).head (e.symm i) ≤ hi
    induction e.symm i using Fin.addCases with
    | left j => simpa only [Tapes.append,Fin.addCases_left,Config.tapes] using hb j
    | right j => simpa only [Tapes.append,Fin.addCases_right,extra,SharedBank.empty] using And.intro hlo hhi
  have hp := (hw.extend extra).reindex e
  have hstart : (((raw before t).start M).extend extra).reindex e =
      (raw before n).start (padProgram M h) := by
    change (((raw before t).append extra).reindex e).start (padProgram M h) = _
    rw [raw_append before hkt,raw_reindex]
  have hend : ((d.extend extra).reindex e).tapes = raw after n := by
    change ((d.tapes.append extra).reindex e) = _
    rw [hpost,raw_append after hkt,raw_reindex]
  refine ⟨m,hm,_,?_,?_,hend⟩
  · simpa only [hstart,padProgram,H,e] using hp
  · exact reindex_halt _ e (extend_halt M extra hd)

end
end IntegerMultBounds.Machine.SharedBankFamily
