import IntegerMultBounds.Machine.AllAxisPhaseFlagsEndpoint

/-! The reused scanner clocks and immutable f descriptor return to their exact
caller cells, leaving only the control head and two retained flags changed. -/
namespace IntegerMultBounds.Machine.AllAxisPhaseFlagsNormalize
noncomputable section
open AllAxisPhaseFlagsCaller (scanSlots scanInjective scanPlacement)
open MarkedWordCleanup (one)
open UnitPhaseNumerator (flags)

def privateBefore (addr bs : List Bool) (tail : Tapes 6 2) : Tapes 13 2 :=
  (one (SelectedSourceBitsScan.word addr) 0).append
    ((one (SelectedSourceBitsScan.word bs) 0).append
      ((SharedBank.empty 3 2).append ((flags 0).append tail)))
def privateAfter (addr bs : List Bool) (p : Fin 4) (tail : Tapes 6 2) : Tapes 13 2 :=
  (one (SelectedSourceBitsScan.word addr) 0).append
    ((one (SelectedSourceBitsScan.word bs) bs.length).append
      ((SharedBank.empty 3 2).append ((flags p).append tail)))

private theorem private_head_eq (addr bs : List Bool) (p : Fin 4) (tail : Tapes 6 2)
    (k : Fin 13) (hk : k≠1) :
    (privateBefore addr bs tail).head k=(privateAfter addr bs p tail).head k := by
  fin_cases k <;> first | exact False.elim (hk rfl) | rfl

private theorem private_tape_eq (addr bs : List Bool) (p : Fin 4) (tail : Tapes 6 2)
    (k : Fin 13) (h5 : k≠5) (h6 : k≠6) :
    (privateBefore addr bs tail).tape k=(privateAfter addr bs p tail).tape k := by
  unfold privateBefore privateAfter
  simp only [Tapes.append,Fin.addCases]
  split_ifs <;> try rfl
  all_goals rename_i h1 h2 h3 h4
  all_goals change ¬k.val<1 at h1
  all_goals change ¬(k.val-1)<1 at h2
  all_goals change ¬(k.val-1-1)<3 at h3
  all_goals change k.val-1-1-3<2 at h4
  all_goals by_cases he : k.val=5
  all_goals first
    | exact False.elim (h5 (Fin.ext he))
    | exact False.elim (h6 (Fin.ext (by omega)))

private theorem normalized_head (b : Tapes 43 2) (addr bs ds : List Bool) (p : Fin 4)
    (tail : Tapes 6 2) (hb : b.head 7=1) :
    (Placement.replace scanPlacement (b.append (privateBefore addr bs tail))
      (RepeatedWeightedPhaseHeader.boundary p (SelectedSourceBitsScan.word bs) bs.length ds)).head=
      (b.append (privateAfter addr bs p tail)).head := by
  funext k
  by_cases ha : ∃ i : Fin 6,scanSlots i=k
  · obtain ⟨i,rfl⟩ := ha
    rw [scanPlacement,InjectivePlacement.replace_head_slot]
    fin_cases i <;> simp [scanSlots,RepeatedWeightedPhaseHeader.boundary,
      RepeatedWeightedPhaseHeader.bank4,CountedLoopHeaderClean.bank,WeightedPhaseAccumulator.bank,
      flags,UnitPhaseNumerator.flags,privateAfter,one,Tapes.append,Fin.addCases,hb,SharedBank.empty]
  · rw [scanPlacement,InjectivePlacement.replace_head_other _ _ _ _ _ _ (by
      intro i he; exact ha ⟨i,he⟩)]
    change Fin (43+13) at k
    induction k using Fin.addCases with
    | left k => simp only [Tapes.append,Fin.addCases_left]
    | right k =>
      simp only [Tapes.append,Fin.addCases_right]
      apply private_head_eq
      intro he
      subst k
      exact ha ⟨2,rfl⟩

private theorem normalized_tape (b : Tapes 43 2) (addr bs ds : List Bool) (p : Fin 4)
    (tail : Tapes 6 2) (hb : b.tape 7=RadixZeroFill.encodedBinary ds) :
    (Placement.replace scanPlacement (b.append (privateBefore addr bs tail))
      (RepeatedWeightedPhaseHeader.boundary p (SelectedSourceBitsScan.word bs) bs.length ds)).tape=
      (b.append (privateAfter addr bs p tail)).tape := by
  funext k
  by_cases ha : ∃ i : Fin 6,scanSlots i=k
  · obtain ⟨i,rfl⟩ := ha
    rw [scanPlacement,InjectivePlacement.replace_tape_slot]
    fin_cases i <;> simp [scanSlots,RepeatedWeightedPhaseHeader.boundary,
      RepeatedWeightedPhaseHeader.bank4,CountedLoopHeaderClean.bank,WeightedPhaseAccumulator.bank,
      flags,UnitPhaseNumerator.flags,privateAfter,one,Tapes.append,Fin.addCases,hb,SharedBank.empty]
  · rw [scanPlacement,InjectivePlacement.replace_tape_other _ _ _ _ _ _ (by
      intro i he; exact ha ⟨i,he⟩)]
    change Fin (43+13) at k
    induction k using Fin.addCases with
    | left k => simp only [Tapes.append,Fin.addCases_left]
    | right k =>
      simp only [Tapes.append,Fin.addCases_right]
      apply private_tape_eq
      · intro he
        subst k
        exact ha ⟨0,rfl⟩
      · intro he
        subst k
        exact ha ⟨1,rfl⟩

theorem normalized (b : Tapes 43 2) (addr bs ds : List Bool) (p : Fin 4)
    (tail : Tapes 6 2) (hh : b.head 7=1) (ht : b.tape 7=RadixZeroFill.encodedBinary ds) :
    Placement.replace scanPlacement (b.append (privateBefore addr bs tail))
      (RepeatedWeightedPhaseHeader.boundary p (SelectedSourceBitsScan.word bs) bs.length ds)=
      b.append (privateAfter addr bs p tail) :=
  congrArg₂ Tapes.mk (normalized_head b addr bs ds p tail hh) (normalized_tape b addr bs ds p tail ht)

open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open ActivePrefixStageHeadersData (Order)

theorem output_eq {s : Shape} (order : Order) (v : Stage s) (rows m : ℕ)
    (ws : List (ZMod 4)) (addr : List Bool) (tail : Tapes 6 2) :
    AllAxisPhaseFlagsCaller.output order v rows m ws addr tail=
      (ActiveRepairRankHeadersCommands.bank (AllAxisPhaseHeadersData.finished order v rows m)).append
        (privateAfter addr (AllAxisPhaseFlagsCaller.controls v m addr)
          (AllAxisPhaseFlagsCaller.phase v m ws addr) tail) := by
  have hl : (AllAxisPhaseFlagsCaller.controls v m addr).length=m*v.f := by
    simp only [AllAxisPhaseFlagsCaller.controls,SelectedSourceBitsData.selected_length]
  unfold AllAxisPhaseFlagsCaller.output
  have hlz : (m : ℤ)*(v.f : ℤ)=((AllAxisPhaseFlagsCaller.controls v m addr).length : ℤ) := by
    rw [hl,Nat.cast_mul]
  rw [hlz]
  apply normalized
  all_goals simp [ActiveRepairRankHeadersCommands.bank,AllAxisPhaseHeadersData.finished,
    AllAxisPhaseHeadersData.initial,ActivePrefixStageHeadersData.finished,
    ActivePrefixStageHeadersData.originalValues,ActivePrefixStageHeadersData.outputs,
    ActiveRepairRankHeadersCommands.put,ActiveRepairRankHeadersCommands.caller,CleanSubbank.bank,
    Tapes.append,Fin.addCases,Function.update]

end
end IntegerMultBounds.Machine.AllAxisPhaseFlagsNormalize
