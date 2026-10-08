import IntegerMultBounds.Machine.SharedBankFamily

/-! Exact finite-state execution survives uniform workspace padding. In
particular, width-test and return-decoder terminal states remain available to
the cyclic controller; a tape-only Hoare contract would lose this information. -/
namespace IntegerMultBounds.Machine.SharedBankFamilyExact
open SharedBankFamily SharedBankStageInput
variable {k t n r a : ℕ}
noncomputable section

def atState (v : Tapes t a) (st : Fin r) : Config t r a := ⟨st,v.head,v.tape⟩

def padConfig (h : t ≤ n) (c : Config t r a) : Config n r a :=
  (c.extend (SharedBank.empty (n-t) a)).reindex (finCongr (Nat.add_sub_of_le h))

theorem pad_state (h : t ≤ n) (c : Config t r a) : (padConfig h c).state = c.state := rfl

theorem pad_raw (h : t ≤ n) (hkt : k ≤ t) (v : Tapes k a) (st : Fin r) :
    padConfig h (atState (raw v t) st) = atState (raw v n) st := by
  have he : ((raw v t).append (SharedBank.empty (n-t) a)).reindex
      (finCongr (Nat.add_sub_of_le h)) = raw v n := by
    rw [raw_append v hkt,raw_reindex]
  exact congrArg (fun w : Tapes n a => atState w st) he

/-- Padding retains the exact terminal state and every physical step count. -/
theorem pad_run (M : Program t r a) (h : t ≤ n) (hkt : k ≤ t)
    (before after : Tapes k a) (start finish : Fin r) (steps : ℕ)
    (hr : run M steps (atState (raw before t) start) = some (atState (raw after t) finish)) :
    run (padProgram M h) steps (atState (raw before n) start) = some (atState (raw after n) finish) := by
  have hh := reindex_run (extend M (n-t)) (finCongr (Nat.add_sub_of_le h))
    (extend_run M (SharedBank.empty (n-t) a) hr)
  change run (padProgram M h) steps (padConfig h (atState (raw before t) start)) =
    some (padConfig h (atState (raw after t) finish)) at hh
  simpa only [pad_raw h hkt] using hh

theorem pad_halt (M : Program t r a) (h : t ≤ n) (hkt : k ≤ t)
    (after : Tapes k a) (finish : Fin r)
    (hh : step M (atState (raw after t) finish) = none) :
    step (padProgram M h) (atState (raw after n) finish) = none := by
  have hp := reindex_halt (extend M (n-t)) (finCongr (Nat.add_sub_of_le h))
    (extend_halt M (SharedBank.empty (n-t) a) hh)
  change step (padProgram M h) (padConfig h (atState (raw after t) finish)) = none at hp
  simpa only [pad_raw h hkt] using hp

/-- Exact clean block execution, starting at its actual initial control state. -/
theorem pad_exact (M : Program t r a) (h : t ≤ n) (hkt : k ≤ t)
    (before after : Tapes k a) (steps : ℕ) (finish : Fin r)
    (hr : run M steps ((raw before t).start M) = some (atState (raw after t) finish))
    (hh : step M (atState (raw after t) finish) = none) :
    run (padProgram M h) steps ((raw before n).start (padProgram M h)) =
      some (atState (raw after n) finish) ∧
      step (padProgram M h) (atState (raw after n) finish) = none :=
  ⟨pad_run M h hkt before after M.start finish steps hr,pad_halt M h hkt after finish hh⟩

variable {Label : Type*} [Fintype Label]

/-- Every fixed family member preserves its own actual exit state in the
single shared workspace, ready for a real finite-flow jump. -/
theorem family_exact (blocks : Label → SharedBankSkeleton.Skeleton k a) (i : Label)
    (before after : Tapes k a) (steps : ℕ) (finish : Fin (blocks i).states)
    (hr : run (blocks i).program steps ((raw before (blocks i).tapes).start (blocks i).program) =
      some (atState (raw after (blocks i).tapes) finish))
    (hh : step (blocks i).program (atState (raw after (blocks i).tapes) finish) = none) :
    run (SharedBankFamily.program blocks i) steps
      ((raw before (tapeCount blocks)).start (SharedBankFamily.program blocks i)) =
        some (atState (raw after (tapeCount blocks)) finish) ∧
    step (SharedBankFamily.program blocks i) (atState (raw after (tapeCount blocks)) finish) = none :=
  pad_exact (blocks i).program (block_le blocks i) (common_le (blocks i)) before after steps finish hr hh

end
end IntegerMultBounds.Machine.SharedBankFamilyExact
