import IntegerMultBounds.Machine.RadixHighBlockJoinBank
namespace IntegerMultBounds.Machine.RadixHighBlockJoinBank
noncomputable section
variable {q a : ℕ}
private theorem initialized_head (source : ℤ → Fin (a+4)) (ss originalP originalE ps es ws : List Bool) :
    (bank (q := q) source ss originalP originalE (some ps) (some es) (some ws)).head =
      ((RadixDigitMoveBlockExecution.bank (Q := q) source ps ss es).append (tail ws originalP originalE)).head := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    refine Fin.addCases ?_ ?_ j
    · intro k
      refine Fin.addCases ?_ ?_ k
      · intro l
        refine Fin.addCases ?_ ?_ l
        · intro z
          refine Fin.addCases ?_ ?_ z
          · intro h; fin_cases h
            simp only [bank,tail,RadixDigitMoveBlockExecution.bank,RadixDigitMoveBlockPlacement.bank,
              RadixDigitMoveBlockPlacement.controls,RadixDigitMoveBlockPlacement.tail,CyclicRowCopy.payload,
              SharedBank.empty,Tapes.append,Fin.addCases_left,Fin.addCases_right,
              prefixSlot,suffixSlot,baseSlot,spectatorSlot,originalPrefixSlot,originalSuffixSlot,
              Fin.val_castAdd,Fin.val_natAdd,Fin.val_zero,Fin.val_ofNat,RadixDigitMoveCore.count]
            repeat' (split_ifs <;> (try simp_all only [false_or,or_false,not_false_eq_true]) <;> (try omega) <;> (try rfl))
            all_goals first | contradiction | omega | rfl
          · intro h
            have hh := h.isLt
            simp only [bank,tail,RadixDigitMoveBlockExecution.bank,RadixDigitMoveBlockPlacement.bank,
              RadixDigitMoveBlockPlacement.controls,RadixDigitMoveBlockPlacement.tail,CyclicRowCopy.payload,
              SharedBank.empty,Tapes.append,Fin.addCases_left,Fin.addCases_right,
              prefixSlot,suffixSlot,baseSlot,spectatorSlot,originalPrefixSlot,originalSuffixSlot,
              Fin.val_castAdd,Fin.val_natAdd,Fin.val_zero,Fin.val_ofNat,RadixDigitMoveCore.count]
            repeat' (split_ifs <;> (try simp_all only [false_or,or_false,not_false_eq_true]) <;> (try omega) <;> (try rfl))
            all_goals first | contradiction | omega | rfl
        · intro z; fin_cases z
          all_goals
            simp only [bank,tail,RadixDigitMoveBlockExecution.bank,RadixDigitMoveBlockPlacement.bank,
              RadixDigitMoveBlockPlacement.controls,RadixDigitMoveBlockPlacement.tail,CyclicRowCopy.payload,
              SharedBank.empty,Tapes.append,Fin.addCases_left,Fin.addCases_right,
              prefixSlot,suffixSlot,baseSlot,spectatorSlot,originalPrefixSlot,originalSuffixSlot,
              Fin.val_castAdd,Fin.val_natAdd,Fin.val_zero,Fin.val_ofNat,RadixDigitMoveCore.count]
            repeat' (split_ifs <;> (try simp_all only [false_or,or_false,not_false_eq_true]) <;> (try omega) <;> (try rfl))
            all_goals first | contradiction | omega | rfl
      · intro l
        have hl := l.isLt
        change l.val < 1+q+6 at hl
        simp only [bank,tail,RadixDigitMoveBlockExecution.bank,RadixDigitMoveBlockPlacement.bank,
          RadixDigitMoveBlockPlacement.controls,RadixDigitMoveBlockPlacement.tail,CyclicRowCopy.payload,
          SharedBank.empty,Tapes.append,Fin.addCases_left,Fin.addCases_right,
          prefixSlot,suffixSlot,baseSlot,spectatorSlot,originalPrefixSlot,originalSuffixSlot,
          Fin.val_castAdd,Fin.val_natAdd,Fin.val_zero,Fin.val_ofNat,RadixDigitMoveCore.count]
        repeat' (split_ifs <;> (try simp_all only [false_or,or_false,not_false_eq_true]) <;> (try omega) <;> (try rfl))
        all_goals first | contradiction | omega | rfl
    · intro k; fin_cases k
      all_goals
        simp only [bank,tail,RadixDigitMoveBlockExecution.bank,RadixDigitMoveBlockPlacement.bank,
          RadixDigitMoveBlockPlacement.controls,RadixDigitMoveBlockPlacement.tail,CyclicRowCopy.payload,
          SharedBank.empty,Tapes.append,Fin.addCases_left,Fin.addCases_right,
          prefixSlot,suffixSlot,baseSlot,spectatorSlot,originalPrefixSlot,originalSuffixSlot,
          Fin.val_castAdd,Fin.val_natAdd,Fin.val_zero,Fin.val_ofNat,RadixDigitMoveCore.count]
        repeat' (split_ifs <;> (try simp_all only [false_or,or_false,not_false_eq_true]) <;> (try omega) <;> (try rfl))
        all_goals first | contradiction | omega | rfl
  · intro j; fin_cases j
    all_goals
      simp only [bank,tail,RadixDigitMoveBlockExecution.bank,RadixDigitMoveBlockPlacement.bank,
        RadixDigitMoveBlockPlacement.controls,RadixDigitMoveBlockPlacement.tail,CyclicRowCopy.payload,
        SharedBank.empty,Tapes.append,Fin.addCases_left,Fin.addCases_right,
        prefixSlot,suffixSlot,baseSlot,spectatorSlot,originalPrefixSlot,originalSuffixSlot,
        Fin.val_castAdd,Fin.val_natAdd,Fin.val_zero,Fin.val_ofNat,RadixDigitMoveCore.count]
      repeat' (split_ifs <;> (try simp_all only [false_or,or_false,not_false_eq_true]) <;> (try omega) <;> (try rfl))
      all_goals first | contradiction | omega | rfl

private theorem initialized_tape_core (source : ℤ → Fin (a+4)) (ss originalP originalE ps es ws : List Bool) (j : Fin ((RadixDigitMoveCore.count q+RadixDigitMoveCore.count q)+4)) :
    (bank (q := q) source ss originalP originalE (some ps) (some es) (some ws)).tape (Fin.castAdd 16 j) = ((RadixDigitMoveBlockExecution.bank (Q := q) source ps ss es).append (tail ws originalP originalE)).tape (Fin.castAdd 16 j) := by
  refine Fin.addCases ?_ ?_ j
  · intro k
    refine Fin.addCases ?_ ?_ k
    · intro l
      refine Fin.addCases ?_ ?_ l
      · intro z
        refine Fin.addCases ?_ ?_ z
        · intro h; fin_cases h
          simp only [bank,tail,RadixDigitMoveBlockExecution.bank,RadixDigitMoveBlockPlacement.bank,
            RadixDigitMoveBlockPlacement.controls,RadixDigitMoveBlockPlacement.tail,CyclicRowCopy.payload,
            SharedBank.empty,Tapes.append,Fin.addCases_left,Fin.addCases_right,
            prefixSlot,suffixSlot,baseSlot,spectatorSlot,originalPrefixSlot,originalSuffixSlot,
            Fin.val_castAdd,Fin.val_natAdd,Fin.val_zero,Fin.val_ofNat,RadixDigitMoveCore.count]
          repeat' (split_ifs <;> (try simp_all only [false_or,or_false,not_false_eq_true]) <;> (try omega) <;> (try rfl))
          all_goals first | contradiction | omega | rfl
        · intro h
          have hh := h.isLt
          simp only [bank,tail,RadixDigitMoveBlockExecution.bank,RadixDigitMoveBlockPlacement.bank,
            RadixDigitMoveBlockPlacement.controls,RadixDigitMoveBlockPlacement.tail,CyclicRowCopy.payload,
            SharedBank.empty,Tapes.append,Fin.addCases_left,Fin.addCases_right,
            prefixSlot,suffixSlot,baseSlot,spectatorSlot,originalPrefixSlot,originalSuffixSlot,
            Fin.val_castAdd,Fin.val_natAdd,Fin.val_zero,Fin.val_ofNat,RadixDigitMoveCore.count]
          repeat' (split_ifs <;> (try simp_all only [false_or,or_false,not_false_eq_true]) <;> (try omega) <;> (try rfl))
          all_goals first | contradiction | omega | rfl
      · intro z; fin_cases z
        all_goals
          simp only [bank,tail,RadixDigitMoveBlockExecution.bank,RadixDigitMoveBlockPlacement.bank,
            RadixDigitMoveBlockPlacement.controls,RadixDigitMoveBlockPlacement.tail,CyclicRowCopy.payload,
            SharedBank.empty,Tapes.append,Fin.addCases_left,Fin.addCases_right,
            prefixSlot,suffixSlot,baseSlot,spectatorSlot,originalPrefixSlot,originalSuffixSlot,
            Fin.val_castAdd,Fin.val_natAdd,Fin.val_zero,Fin.val_ofNat,RadixDigitMoveCore.count]
          repeat' (split_ifs <;> (try simp_all only [false_or,or_false,not_false_eq_true]) <;> (try omega) <;> (try rfl))
          all_goals first | contradiction | omega | rfl
    · intro l
      have hl := l.isLt
      change l.val < 1+q+6 at hl
      simp only [bank,tail,RadixDigitMoveBlockExecution.bank,RadixDigitMoveBlockPlacement.bank,
        RadixDigitMoveBlockPlacement.controls,RadixDigitMoveBlockPlacement.tail,CyclicRowCopy.payload,
        SharedBank.empty,Tapes.append,Fin.addCases_left,Fin.addCases_right,
        prefixSlot,suffixSlot,baseSlot,spectatorSlot,originalPrefixSlot,originalSuffixSlot,
        Fin.val_castAdd,Fin.val_natAdd,Fin.val_zero,Fin.val_ofNat,RadixDigitMoveCore.count]
      repeat' (split_ifs <;> (try simp_all only [false_or,or_false,not_false_eq_true]) <;> (try omega) <;> (try rfl))
      all_goals first | contradiction | omega | rfl
  · intro k; fin_cases k
    all_goals
      simp only [bank,tail,RadixDigitMoveBlockExecution.bank,RadixDigitMoveBlockPlacement.bank,
        RadixDigitMoveBlockPlacement.controls,RadixDigitMoveBlockPlacement.tail,CyclicRowCopy.payload,
        SharedBank.empty,Tapes.append,Fin.addCases_left,Fin.addCases_right,
        prefixSlot,suffixSlot,baseSlot,spectatorSlot,originalPrefixSlot,originalSuffixSlot,
        Fin.val_castAdd,Fin.val_natAdd,Fin.val_zero,Fin.val_ofNat,RadixDigitMoveCore.count]
      repeat' (split_ifs <;> (try simp_all only [false_or,or_false,not_false_eq_true]) <;> (try omega) <;> (try rfl))
      all_goals first | contradiction | omega | rfl
private theorem initialized_tape_tail_0 (source : ℤ → Fin (a+4)) (ss originalP originalE ps es ws : List Bool) :
    (bank (q := q) source ss originalP originalE (some ps) (some es) (some ws)).tape (Fin.natAdd ((RadixDigitMoveCore.count q+RadixDigitMoveCore.count q)+4) (0 : Fin 16)) = ((RadixDigitMoveBlockExecution.bank (Q := q) source ps ss es).append (tail ws originalP originalE)).tape (Fin.natAdd ((RadixDigitMoveCore.count q+RadixDigitMoveCore.count q)+4) (0 : Fin 16)) := by
  simp only [bank,tail,RadixDigitMoveBlockExecution.bank,RadixDigitMoveBlockPlacement.bank,
    RadixDigitMoveBlockPlacement.controls,RadixDigitMoveBlockPlacement.tail,CyclicRowCopy.payload,
    SharedBank.empty,Tapes.append,Fin.addCases_left,Fin.addCases_right,
    prefixSlot,suffixSlot,baseSlot,spectatorSlot,originalPrefixSlot,originalSuffixSlot,
    Fin.val_castAdd,Fin.val_natAdd,Fin.val_zero,Fin.val_ofNat,RadixDigitMoveCore.count]
  repeat' (split_ifs <;> (try simp_all only [false_or,or_false,not_false_eq_true]) <;> (try omega) <;> (try rfl))
  all_goals first | contradiction | omega | rfl

private theorem initialized_tape_tail_1 (source : ℤ → Fin (a+4)) (ss originalP originalE ps es ws : List Bool) :
    (bank (q := q) source ss originalP originalE (some ps) (some es) (some ws)).tape (Fin.natAdd ((RadixDigitMoveCore.count q+RadixDigitMoveCore.count q)+4) (1 : Fin 16)) = ((RadixDigitMoveBlockExecution.bank (Q := q) source ps ss es).append (tail ws originalP originalE)).tape (Fin.natAdd ((RadixDigitMoveCore.count q+RadixDigitMoveCore.count q)+4) (1 : Fin 16)) := by
  simp only [bank,tail,RadixDigitMoveBlockExecution.bank,RadixDigitMoveBlockPlacement.bank,
    RadixDigitMoveBlockPlacement.controls,RadixDigitMoveBlockPlacement.tail,CyclicRowCopy.payload,
    SharedBank.empty,Tapes.append,Fin.addCases_left,Fin.addCases_right,
    prefixSlot,suffixSlot,baseSlot,spectatorSlot,originalPrefixSlot,originalSuffixSlot,
    Fin.val_castAdd,Fin.val_natAdd,Fin.val_zero,Fin.val_ofNat,RadixDigitMoveCore.count]
  repeat' (split_ifs <;> (try simp_all only [false_or,or_false,not_false_eq_true]) <;> (try omega) <;> (try rfl))
  all_goals first | contradiction | omega | rfl

private theorem initialized_tape_tail_2 (source : ℤ → Fin (a+4)) (ss originalP originalE ps es ws : List Bool) :
    (bank (q := q) source ss originalP originalE (some ps) (some es) (some ws)).tape (Fin.natAdd ((RadixDigitMoveCore.count q+RadixDigitMoveCore.count q)+4) (2 : Fin 16)) = ((RadixDigitMoveBlockExecution.bank (Q := q) source ps ss es).append (tail ws originalP originalE)).tape (Fin.natAdd ((RadixDigitMoveCore.count q+RadixDigitMoveCore.count q)+4) (2 : Fin 16)) := by
  simp only [bank,tail,RadixDigitMoveBlockExecution.bank,RadixDigitMoveBlockPlacement.bank,
    RadixDigitMoveBlockPlacement.controls,RadixDigitMoveBlockPlacement.tail,CyclicRowCopy.payload,
    SharedBank.empty,Tapes.append,Fin.addCases_left,Fin.addCases_right,
    prefixSlot,suffixSlot,baseSlot,spectatorSlot,originalPrefixSlot,originalSuffixSlot,
    Fin.val_castAdd,Fin.val_natAdd,Fin.val_zero,Fin.val_ofNat,RadixDigitMoveCore.count]
  repeat' (split_ifs <;> (try simp_all only [false_or,or_false,not_false_eq_true]) <;> (try omega) <;> (try rfl))
  all_goals first | contradiction | omega | rfl

private theorem initialized_tape_tail_3 (source : ℤ → Fin (a+4)) (ss originalP originalE ps es ws : List Bool) :
    (bank (q := q) source ss originalP originalE (some ps) (some es) (some ws)).tape (Fin.natAdd ((RadixDigitMoveCore.count q+RadixDigitMoveCore.count q)+4) (3 : Fin 16)) = ((RadixDigitMoveBlockExecution.bank (Q := q) source ps ss es).append (tail ws originalP originalE)).tape (Fin.natAdd ((RadixDigitMoveCore.count q+RadixDigitMoveCore.count q)+4) (3 : Fin 16)) := by
  simp only [bank,tail,RadixDigitMoveBlockExecution.bank,RadixDigitMoveBlockPlacement.bank,
    RadixDigitMoveBlockPlacement.controls,RadixDigitMoveBlockPlacement.tail,CyclicRowCopy.payload,
    SharedBank.empty,Tapes.append,Fin.addCases_left,Fin.addCases_right,
    prefixSlot,suffixSlot,baseSlot,spectatorSlot,originalPrefixSlot,originalSuffixSlot,
    Fin.val_castAdd,Fin.val_natAdd,Fin.val_zero,Fin.val_ofNat,RadixDigitMoveCore.count]
  repeat' (split_ifs <;> (try simp_all only [false_or,or_false,not_false_eq_true]) <;> (try omega) <;> (try rfl))
  all_goals first | contradiction | omega | rfl

private theorem initialized_tape_tail_4 (source : ℤ → Fin (a+4)) (ss originalP originalE ps es ws : List Bool) :
    (bank (q := q) source ss originalP originalE (some ps) (some es) (some ws)).tape (Fin.natAdd ((RadixDigitMoveCore.count q+RadixDigitMoveCore.count q)+4) (4 : Fin 16)) = ((RadixDigitMoveBlockExecution.bank (Q := q) source ps ss es).append (tail ws originalP originalE)).tape (Fin.natAdd ((RadixDigitMoveCore.count q+RadixDigitMoveCore.count q)+4) (4 : Fin 16)) := by
  simp only [bank,tail,RadixDigitMoveBlockExecution.bank,RadixDigitMoveBlockPlacement.bank,
    RadixDigitMoveBlockPlacement.controls,RadixDigitMoveBlockPlacement.tail,CyclicRowCopy.payload,
    SharedBank.empty,Tapes.append,Fin.addCases_left,Fin.addCases_right,
    prefixSlot,suffixSlot,baseSlot,spectatorSlot,originalPrefixSlot,originalSuffixSlot,
    Fin.val_castAdd,Fin.val_natAdd,Fin.val_zero,Fin.val_ofNat,RadixDigitMoveCore.count]
  repeat' (split_ifs <;> (try simp_all only [false_or,or_false,not_false_eq_true]) <;> (try omega) <;> (try rfl))
  all_goals first | contradiction | omega | rfl

private theorem initialized_tape_tail_5 (source : ℤ → Fin (a+4)) (ss originalP originalE ps es ws : List Bool) :
    (bank (q := q) source ss originalP originalE (some ps) (some es) (some ws)).tape (Fin.natAdd ((RadixDigitMoveCore.count q+RadixDigitMoveCore.count q)+4) (5 : Fin 16)) = ((RadixDigitMoveBlockExecution.bank (Q := q) source ps ss es).append (tail ws originalP originalE)).tape (Fin.natAdd ((RadixDigitMoveCore.count q+RadixDigitMoveCore.count q)+4) (5 : Fin 16)) := by
  simp only [bank,tail,RadixDigitMoveBlockExecution.bank,RadixDigitMoveBlockPlacement.bank,
    RadixDigitMoveBlockPlacement.controls,RadixDigitMoveBlockPlacement.tail,CyclicRowCopy.payload,
    SharedBank.empty,Tapes.append,Fin.addCases_left,Fin.addCases_right,
    prefixSlot,suffixSlot,baseSlot,spectatorSlot,originalPrefixSlot,originalSuffixSlot,
    Fin.val_castAdd,Fin.val_natAdd,Fin.val_zero,Fin.val_ofNat,RadixDigitMoveCore.count]
  repeat' (split_ifs <;> (try simp_all only [false_or,or_false,not_false_eq_true]) <;> (try omega) <;> (try rfl))
  all_goals first | contradiction | omega | rfl

private theorem initialized_tape_tail_6 (source : ℤ → Fin (a+4)) (ss originalP originalE ps es ws : List Bool) :
    (bank (q := q) source ss originalP originalE (some ps) (some es) (some ws)).tape (Fin.natAdd ((RadixDigitMoveCore.count q+RadixDigitMoveCore.count q)+4) (6 : Fin 16)) = ((RadixDigitMoveBlockExecution.bank (Q := q) source ps ss es).append (tail ws originalP originalE)).tape (Fin.natAdd ((RadixDigitMoveCore.count q+RadixDigitMoveCore.count q)+4) (6 : Fin 16)) := by
  simp only [bank,tail,RadixDigitMoveBlockExecution.bank,RadixDigitMoveBlockPlacement.bank,
    RadixDigitMoveBlockPlacement.controls,RadixDigitMoveBlockPlacement.tail,CyclicRowCopy.payload,
    SharedBank.empty,Tapes.append,Fin.addCases_left,Fin.addCases_right,
    prefixSlot,suffixSlot,baseSlot,spectatorSlot,originalPrefixSlot,originalSuffixSlot,
    Fin.val_castAdd,Fin.val_natAdd,Fin.val_zero,Fin.val_ofNat,RadixDigitMoveCore.count]
  repeat' (split_ifs <;> (try simp_all only [false_or,or_false,not_false_eq_true]) <;> (try omega) <;> (try rfl))
  all_goals first | contradiction | omega | rfl

private theorem initialized_tape_tail_7 (source : ℤ → Fin (a+4)) (ss originalP originalE ps es ws : List Bool) :
    (bank (q := q) source ss originalP originalE (some ps) (some es) (some ws)).tape (Fin.natAdd ((RadixDigitMoveCore.count q+RadixDigitMoveCore.count q)+4) (7 : Fin 16)) = ((RadixDigitMoveBlockExecution.bank (Q := q) source ps ss es).append (tail ws originalP originalE)).tape (Fin.natAdd ((RadixDigitMoveCore.count q+RadixDigitMoveCore.count q)+4) (7 : Fin 16)) := by
  simp only [bank,tail,RadixDigitMoveBlockExecution.bank,RadixDigitMoveBlockPlacement.bank,
    RadixDigitMoveBlockPlacement.controls,RadixDigitMoveBlockPlacement.tail,CyclicRowCopy.payload,
    SharedBank.empty,Tapes.append,Fin.addCases_left,Fin.addCases_right,
    prefixSlot,suffixSlot,baseSlot,spectatorSlot,originalPrefixSlot,originalSuffixSlot,
    Fin.val_castAdd,Fin.val_natAdd,Fin.val_zero,Fin.val_ofNat,RadixDigitMoveCore.count]
  repeat' (split_ifs <;> (try simp_all only [false_or,or_false,not_false_eq_true]) <;> (try omega) <;> (try rfl))
  all_goals first | contradiction | omega | rfl

private theorem initialized_tape_tail_8 (source : ℤ → Fin (a+4)) (ss originalP originalE ps es ws : List Bool) :
    (bank (q := q) source ss originalP originalE (some ps) (some es) (some ws)).tape (Fin.natAdd ((RadixDigitMoveCore.count q+RadixDigitMoveCore.count q)+4) (8 : Fin 16)) = ((RadixDigitMoveBlockExecution.bank (Q := q) source ps ss es).append (tail ws originalP originalE)).tape (Fin.natAdd ((RadixDigitMoveCore.count q+RadixDigitMoveCore.count q)+4) (8 : Fin 16)) := by
  simp only [bank,tail,RadixDigitMoveBlockExecution.bank,RadixDigitMoveBlockPlacement.bank,
    RadixDigitMoveBlockPlacement.controls,RadixDigitMoveBlockPlacement.tail,CyclicRowCopy.payload,
    SharedBank.empty,Tapes.append,Fin.addCases_left,Fin.addCases_right,
    prefixSlot,suffixSlot,baseSlot,spectatorSlot,originalPrefixSlot,originalSuffixSlot,
    Fin.val_castAdd,Fin.val_natAdd,Fin.val_zero,Fin.val_ofNat,RadixDigitMoveCore.count]
  repeat' (split_ifs <;> (try simp_all only [false_or,or_false,not_false_eq_true]) <;> (try omega) <;> (try rfl))
  all_goals first | contradiction | omega | rfl

private theorem initialized_tape_tail_9 (source : ℤ → Fin (a+4)) (ss originalP originalE ps es ws : List Bool) :
    (bank (q := q) source ss originalP originalE (some ps) (some es) (some ws)).tape (Fin.natAdd ((RadixDigitMoveCore.count q+RadixDigitMoveCore.count q)+4) (9 : Fin 16)) = ((RadixDigitMoveBlockExecution.bank (Q := q) source ps ss es).append (tail ws originalP originalE)).tape (Fin.natAdd ((RadixDigitMoveCore.count q+RadixDigitMoveCore.count q)+4) (9 : Fin 16)) := by
  simp only [bank,tail,RadixDigitMoveBlockExecution.bank,RadixDigitMoveBlockPlacement.bank,
    RadixDigitMoveBlockPlacement.controls,RadixDigitMoveBlockPlacement.tail,CyclicRowCopy.payload,
    SharedBank.empty,Tapes.append,Fin.addCases_left,Fin.addCases_right,
    prefixSlot,suffixSlot,baseSlot,spectatorSlot,originalPrefixSlot,originalSuffixSlot,
    Fin.val_castAdd,Fin.val_natAdd,Fin.val_zero,Fin.val_ofNat,RadixDigitMoveCore.count]
  repeat' (split_ifs <;> (try simp_all only [false_or,or_false,not_false_eq_true]) <;> (try omega) <;> (try rfl))
  all_goals first | contradiction | omega | rfl

private theorem initialized_tape_tail_10 (source : ℤ → Fin (a+4)) (ss originalP originalE ps es ws : List Bool) :
    (bank (q := q) source ss originalP originalE (some ps) (some es) (some ws)).tape (Fin.natAdd ((RadixDigitMoveCore.count q+RadixDigitMoveCore.count q)+4) (10 : Fin 16)) = ((RadixDigitMoveBlockExecution.bank (Q := q) source ps ss es).append (tail ws originalP originalE)).tape (Fin.natAdd ((RadixDigitMoveCore.count q+RadixDigitMoveCore.count q)+4) (10 : Fin 16)) := by
  simp only [bank,tail,RadixDigitMoveBlockExecution.bank,RadixDigitMoveBlockPlacement.bank,
    RadixDigitMoveBlockPlacement.controls,RadixDigitMoveBlockPlacement.tail,CyclicRowCopy.payload,
    SharedBank.empty,Tapes.append,Fin.addCases_left,Fin.addCases_right,
    prefixSlot,suffixSlot,baseSlot,spectatorSlot,originalPrefixSlot,originalSuffixSlot,
    Fin.val_castAdd,Fin.val_natAdd,Fin.val_zero,Fin.val_ofNat,RadixDigitMoveCore.count]
  repeat' (split_ifs <;> (try simp_all only [false_or,or_false,not_false_eq_true]) <;> (try omega) <;> (try rfl))
  all_goals first | contradiction | omega | rfl

private theorem initialized_tape_tail_11 (source : ℤ → Fin (a+4)) (ss originalP originalE ps es ws : List Bool) :
    (bank (q := q) source ss originalP originalE (some ps) (some es) (some ws)).tape (Fin.natAdd ((RadixDigitMoveCore.count q+RadixDigitMoveCore.count q)+4) (11 : Fin 16)) = ((RadixDigitMoveBlockExecution.bank (Q := q) source ps ss es).append (tail ws originalP originalE)).tape (Fin.natAdd ((RadixDigitMoveCore.count q+RadixDigitMoveCore.count q)+4) (11 : Fin 16)) := by
  simp only [bank,tail,RadixDigitMoveBlockExecution.bank,RadixDigitMoveBlockPlacement.bank,
    RadixDigitMoveBlockPlacement.controls,RadixDigitMoveBlockPlacement.tail,CyclicRowCopy.payload,
    SharedBank.empty,Tapes.append,Fin.addCases_left,Fin.addCases_right,
    prefixSlot,suffixSlot,baseSlot,spectatorSlot,originalPrefixSlot,originalSuffixSlot,
    Fin.val_castAdd,Fin.val_natAdd,Fin.val_zero,Fin.val_ofNat,RadixDigitMoveCore.count]
  repeat' (split_ifs <;> (try simp_all only [false_or,or_false,not_false_eq_true]) <;> (try omega) <;> (try rfl))
  all_goals first | contradiction | omega | rfl

private theorem initialized_tape_tail_12 (source : ℤ → Fin (a+4)) (ss originalP originalE ps es ws : List Bool) :
    (bank (q := q) source ss originalP originalE (some ps) (some es) (some ws)).tape (Fin.natAdd ((RadixDigitMoveCore.count q+RadixDigitMoveCore.count q)+4) (12 : Fin 16)) = ((RadixDigitMoveBlockExecution.bank (Q := q) source ps ss es).append (tail ws originalP originalE)).tape (Fin.natAdd ((RadixDigitMoveCore.count q+RadixDigitMoveCore.count q)+4) (12 : Fin 16)) := by
  simp only [bank,tail,RadixDigitMoveBlockExecution.bank,RadixDigitMoveBlockPlacement.bank,
    RadixDigitMoveBlockPlacement.controls,RadixDigitMoveBlockPlacement.tail,CyclicRowCopy.payload,
    SharedBank.empty,Tapes.append,Fin.addCases_left,Fin.addCases_right,
    prefixSlot,suffixSlot,baseSlot,spectatorSlot,originalPrefixSlot,originalSuffixSlot,
    Fin.val_castAdd,Fin.val_natAdd,Fin.val_zero,Fin.val_ofNat,RadixDigitMoveCore.count]
  repeat' (split_ifs <;> (try simp_all only [false_or,or_false,not_false_eq_true]) <;> (try omega) <;> (try rfl))
  all_goals first | contradiction | omega | rfl

private theorem initialized_tape_tail_13 (source : ℤ → Fin (a+4)) (ss originalP originalE ps es ws : List Bool) :
    (bank (q := q) source ss originalP originalE (some ps) (some es) (some ws)).tape (Fin.natAdd ((RadixDigitMoveCore.count q+RadixDigitMoveCore.count q)+4) (13 : Fin 16)) = ((RadixDigitMoveBlockExecution.bank (Q := q) source ps ss es).append (tail ws originalP originalE)).tape (Fin.natAdd ((RadixDigitMoveCore.count q+RadixDigitMoveCore.count q)+4) (13 : Fin 16)) := by
  simp only [bank,tail,RadixDigitMoveBlockExecution.bank,RadixDigitMoveBlockPlacement.bank,
    RadixDigitMoveBlockPlacement.controls,RadixDigitMoveBlockPlacement.tail,CyclicRowCopy.payload,
    SharedBank.empty,Tapes.append,Fin.addCases_left,Fin.addCases_right,
    prefixSlot,suffixSlot,baseSlot,spectatorSlot,originalPrefixSlot,originalSuffixSlot,
    Fin.val_castAdd,Fin.val_natAdd,Fin.val_zero,Fin.val_ofNat,RadixDigitMoveCore.count]
  repeat' (split_ifs <;> (try simp_all only [false_or,or_false,not_false_eq_true]) <;> (try omega) <;> (try rfl))
  all_goals first | contradiction | omega | rfl

private theorem initialized_tape_tail_14 (source : ℤ → Fin (a+4)) (ss originalP originalE ps es ws : List Bool) :
    (bank (q := q) source ss originalP originalE (some ps) (some es) (some ws)).tape (Fin.natAdd ((RadixDigitMoveCore.count q+RadixDigitMoveCore.count q)+4) (14 : Fin 16)) = ((RadixDigitMoveBlockExecution.bank (Q := q) source ps ss es).append (tail ws originalP originalE)).tape (Fin.natAdd ((RadixDigitMoveCore.count q+RadixDigitMoveCore.count q)+4) (14 : Fin 16)) := by
  simp only [bank,tail,RadixDigitMoveBlockExecution.bank,RadixDigitMoveBlockPlacement.bank,
    RadixDigitMoveBlockPlacement.controls,RadixDigitMoveBlockPlacement.tail,CyclicRowCopy.payload,
    SharedBank.empty,Tapes.append,Fin.addCases_left,Fin.addCases_right,
    prefixSlot,suffixSlot,baseSlot,spectatorSlot,originalPrefixSlot,originalSuffixSlot,
    Fin.val_castAdd,Fin.val_natAdd,Fin.val_zero,Fin.val_ofNat,RadixDigitMoveCore.count]
  repeat' (split_ifs <;> (try simp_all only [false_or,or_false,not_false_eq_true]) <;> (try omega) <;> (try rfl))
  all_goals first | contradiction | omega | rfl

private theorem initialized_tape_tail_15 (source : ℤ → Fin (a+4)) (ss originalP originalE ps es ws : List Bool) :
    (bank (q := q) source ss originalP originalE (some ps) (some es) (some ws)).tape (Fin.natAdd ((RadixDigitMoveCore.count q+RadixDigitMoveCore.count q)+4) (15 : Fin 16)) = ((RadixDigitMoveBlockExecution.bank (Q := q) source ps ss es).append (tail ws originalP originalE)).tape (Fin.natAdd ((RadixDigitMoveCore.count q+RadixDigitMoveCore.count q)+4) (15 : Fin 16)) := by
  simp only [bank,tail,RadixDigitMoveBlockExecution.bank,RadixDigitMoveBlockPlacement.bank,
    RadixDigitMoveBlockPlacement.controls,RadixDigitMoveBlockPlacement.tail,CyclicRowCopy.payload,
    SharedBank.empty,Tapes.append,Fin.addCases_left,Fin.addCases_right,
    prefixSlot,suffixSlot,baseSlot,spectatorSlot,originalPrefixSlot,originalSuffixSlot,
    Fin.val_castAdd,Fin.val_natAdd,Fin.val_zero,Fin.val_ofNat,RadixDigitMoveCore.count]
  repeat' (split_ifs <;> (try simp_all only [false_or,or_false,not_false_eq_true]) <;> (try omega) <;> (try rfl))
  all_goals first | contradiction | omega | rfl

private theorem initialized_tape_tail (source : ℤ → Fin (a+4)) (ss originalP originalE ps es ws : List Bool) (j : Fin 16) :
    (bank (q := q) source ss originalP originalE (some ps) (some es) (some ws)).tape (Fin.natAdd ((RadixDigitMoveCore.count q+RadixDigitMoveCore.count q)+4) j) = ((RadixDigitMoveBlockExecution.bank (Q := q) source ps ss es).append (tail ws originalP originalE)).tape (Fin.natAdd ((RadixDigitMoveCore.count q+RadixDigitMoveCore.count q)+4) j) := by
  fin_cases j
  · exact initialized_tape_tail_0 source ss originalP originalE ps es ws
  · exact initialized_tape_tail_1 source ss originalP originalE ps es ws
  · exact initialized_tape_tail_2 source ss originalP originalE ps es ws
  · exact initialized_tape_tail_3 source ss originalP originalE ps es ws
  · exact initialized_tape_tail_4 source ss originalP originalE ps es ws
  · exact initialized_tape_tail_5 source ss originalP originalE ps es ws
  · exact initialized_tape_tail_6 source ss originalP originalE ps es ws
  · exact initialized_tape_tail_7 source ss originalP originalE ps es ws
  · exact initialized_tape_tail_8 source ss originalP originalE ps es ws
  · exact initialized_tape_tail_9 source ss originalP originalE ps es ws
  · exact initialized_tape_tail_10 source ss originalP originalE ps es ws
  · exact initialized_tape_tail_11 source ss originalP originalE ps es ws
  · exact initialized_tape_tail_12 source ss originalP originalE ps es ws
  · exact initialized_tape_tail_13 source ss originalP originalE ps es ws
  · exact initialized_tape_tail_14 source ss originalP originalE ps es ws
  · exact initialized_tape_tail_15 source ss originalP originalE ps es ws

private theorem initialized_tape (source : ℤ → Fin (a+4)) (ss originalP originalE ps es ws : List Bool) :
    (bank (q := q) source ss originalP originalE (some ps) (some es) (some ws)).tape =
      ((RadixDigitMoveBlockExecution.bank (Q := q) source ps ss es).append (tail ws originalP originalE)).tape := by
  funext i
  exact Fin.addCases (fun j => initialized_tape_core source ss originalP originalE ps es ws j)
    (fun j => initialized_tape_tail source ss originalP originalE ps es ws j) i

theorem initialized_eq (source : ℤ → Fin (a+4)) (ss originalP originalE ps es ws : List Bool) :
    bank (q := q) source ss originalP originalE (some ps) (some es) (some ws) =
      (RadixDigitMoveBlockExecution.bank (Q := q) source ps ss es).append (tail ws originalP originalE) := by
  exact congrArg₂ Tapes.mk (initialized_head _ _ _ _ _ _ _) (initialized_tape _ _ _ _ _ _ _)

end
end IntegerMultBounds.Machine.RadixHighBlockJoinBank
