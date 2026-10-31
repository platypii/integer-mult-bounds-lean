module

public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Pad
public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.CoreWithin
public import IntegerMultBounds.Machine.SharedBankFamilyWithin

/-! A bounded phase pads to the core's common tape count, keeping every
private spectator at zero and preserving the original phase relation and cost. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Stage2Machine.PadWithin
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor)
open SharedBankStageInput (raw)
noncomputable section
variable {k t n s : ℕ}

theorem pad_step {M : Program t s prime} (h : t ≤ n) (hkt : k ≤ t)
    {B : Descriptor → (ℕ → ZMod 2) → Tapes k prime} {u u' : Descriptor}
    {P : (ℕ → ZMod 2) → (ℕ → ZMod 2) → Prop} {c : ℕ} {lo upper : ℤ}
    (hM : Core.PhaseWithin M (fun u X => raw (B u X) t) u u' P c
      (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ upper)) (hlo : lo ≤ 0) (hupper : 0 ≤ upper) :
    Core.PhaseWithin (SharedBankFamily.padProgram M h) (fun u X => raw (B u X) n) u u' P c
      (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ upper) := by
  intro X input hinput
  subst input
  obtain ⟨j,hj,d,hr,hh,Y,hY,hd⟩ := hM X _ rfl
  have ht : HoareTime M (· = raw (B u X) t) (· = raw (B u' Y) t) c := by
    rintro input rfl
    exact ⟨j,d,hj,hr.1,hh,hd⟩
  obtain ⟨m,hm,e,he,heh,heout⟩ := SharedBankFamily.pad_within_heads M h hkt (B u X) (B u' Y) c
    ht lo upper hlo hupper (fun z hz => (hM X).invariant hz)
  exact ⟨m,hm,e,he,heh,Y,hY,heout⟩

end
end IntegerMultBounds.MathlibTM2.M8.Stage2Machine.PadWithin
