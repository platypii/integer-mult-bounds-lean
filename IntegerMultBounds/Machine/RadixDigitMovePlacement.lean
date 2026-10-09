import IntegerMultBounds.Machine.RadixDigitMovePrepared
import IntegerMultBounds.Machine.RadixDigitMoveCounts
import IntegerMultBounds.Machine.InjectivePlacement

/-! The four digit-move descriptors share their existing physical tapes with
one product/constant constructor. Three appended scratch tapes are blank. -/
namespace IntegerMultBounds.Machine.RadixDigitMovePlacement
variable {Q a : ℕ}
noncomputable section
open RadixDigitMoveCore (count)

private def hd : Option (List Bool) → ℤ | none => 0 | some _ => 1
private def tp : Option (List Bool) → ℤ → Fin (a+4)
  | none => fun _ => blank
  | some bs => CountedLoopReuseAlphabet.binary bs

def controls (ss ps : List Bool) (os ts : Option (List Bool)) : Tapes 6 a :=
  ⟨![0,1,0,1,hd os,hd ts],![fun _ => blank,CountedLoopReuseAlphabet.binary ss,
    fun _ => blank,CountedLoopReuseAlphabet.binary ps,tp os,tp ts]⟩

def bank (source : ℤ → Fin (a+4)) (ss ps : List Bool) (os ts : Option (List Bool)) :
    Tapes ((count Q+count Q)+3) a :=
  (((CyclicRowCopy.payload source (fun _ : Fin Q => fun _ => blank) 0 (fun _ => 0)).append
    (controls ss ps os ts)).append (SharedBank.empty (count Q) a)).append (SharedBank.empty 3 a)

theorem prepared_bank (source : ℤ → Fin (a+4)) (ss ps os ts : List Bool) :
    bank (Q := Q) source ss ps (some os) (some ts) =
      (RadixDigitMovePrepared.bank (Q := Q) source ss ps os ts).append (SharedBank.empty 3 a) := by
  have hc : controls (a := a) ss ps (some os) (some ts) = RadixDigitMoveInitialized.controls ss ps os ts := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  simp only [bank,RadixDigitMovePrepared.bank,RadixDigitMoveInitialized.bank,hc]

def slot : Fin 7 → Fin ((count Q+count Q)+3) :=
  ![Fin.castAdd 3 (Fin.castAdd (count Q) (Fin.natAdd (1+Q) 1)),
    Fin.castAdd 3 (Fin.castAdd (count Q) (Fin.natAdd (1+Q) 3)),
    Fin.castAdd 3 (Fin.castAdd (count Q) (Fin.natAdd (1+Q) 4)),
    Fin.castAdd 3 (Fin.castAdd (count Q) (Fin.natAdd (1+Q) 5)),
    Fin.natAdd (count Q+count Q) 0,Fin.natAdd (count Q+count Q) 1,Fin.natAdd (count Q+count Q) 2]

theorem slot_injective : Function.Injective (slot (Q := Q)) := by
  intro i j he
  have hv := congrArg Fin.val he
  fin_cases i <;> fin_cases j <;> simp [slot,count] at hv ⊢ <;> omega

def placement : Fin (7+(2*Q+10)) ≃ Fin ((count Q+count Q)+3) :=
  InjectivePlacement.placement slot slot_injective (by unfold count; omega)

@[simp] theorem active_slot (i : Fin 7) :
    placement (Q := Q) (Fin.castAdd (2*Q+10) i) = slot i := InjectivePlacement.active_slot _ _ _ _

theorem active_bank (source : ℤ → Fin (a+4)) (ss ps : List Bool) (os ts : Option (List Bool)) :
    Placement.active (placement (Q := Q)) (bank source ss ps os ts) =
      RadixDigitMoveCounts.bank ss ps os ts := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals
    simp only [Placement.active,active_slot]
    fin_cases i <;>
      simp [slot,bank,Tapes.append,controls,RadixDigitMoveCounts.bank,
        RadixDigitMoveCounts.encoded_binary]
  all_goals cases os <;> cases ts <;> first | rfl | exact (RadixDigitMoveCounts.encoded_binary _).symm

private theorem extra_ne (i : Fin (2*Q+10)) (j : Fin 7) :
    placement (Q := Q) (Fin.natAdd 7 i) ≠ slot j := by
  intro he
  rw [← active_slot j] at he
  have hv := congrArg Fin.val (placement.injective he)
  simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
  have := j.isLt
  omega

theorem extra_bank (source : ℤ → Fin (a+4)) (ss ps : List Bool)
    (os ts os' ts' : Option (List Bool)) :
    Placement.extra (placement (Q := Q)) (bank source ss ps os ts) =
      Placement.extra placement (bank source ss ps os' ts') := by
  have he (i : Fin ((count Q+count Q)+3)) (hn : ∀ j, i ≠ slot j) :
      (bank source ss ps os ts).head i = (bank source ss ps os' ts').head i ∧
      (bank source ss ps os ts).tape i = (bank source ss ps os' ts').tape i := by
    revert hn
    refine Fin.addCases (m := count Q+count Q) (n := 3) ?_ ?_ i
    · intro j
      refine Fin.addCases (m := count Q) (n := count Q) ?_ ?_ j
      · intro k
        refine Fin.addCases (m := 1+Q) (n := 6) ?_ ?_ k
        · intro l hn
          simp [bank,Tapes.append]
        · intro l hn
          fin_cases l
          all_goals try simp [bank,Tapes.append,controls]
          all_goals
            exfalso
            first | exact hn 2 rfl | exact hn 3 rfl
      · intro k hn; simp only [bank,Tapes.append,Fin.addCases_left,Fin.addCases_right,and_self]
    · intro j hn; simp only [bank,Tapes.append,Fin.addCases_left,Fin.addCases_right,and_self]
  apply congrArg₂ Tapes.mk
  · funext i
    exact (he _ (extra_ne i)).1
  · funext i
    exact (he _ (extra_ne i)).2

theorem placed_hoare {s cost : ℕ} {M : Program 7 s a}
    (source : ℤ → Fin (a+4)) (ss ps : List Bool) (os ts os' ts' : Option (List Bool))
    (h : HoareTime M (fun v => v = RadixDigitMoveCounts.bank ss ps os ts)
      (fun v => v = RadixDigitMoveCounts.bank ss ps os' ts') cost) :
    HoareTime (Placement.placed M (placement (Q := Q)))
      (fun v => v = bank source ss ps os ts) (fun v => v = bank source ss ps os' ts') cost := by
  apply (Placement.hoare_at h placement (bank source ss ps os ts) (active_bank _ _ _ _ _)).consequence
    (fun _ h => h) _ le_rfl
  rintro v ⟨small,rfl,rfl⟩
  rw [Placement.replace,extra_bank source ss ps os ts os' ts',← active_bank source ss ps os' ts']
  exact Placement.view _ _

end
end IntegerMultBounds.Machine.RadixDigitMovePlacement
