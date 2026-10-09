import IntegerMultBounds.Machine.ButterflyAxisRun

/-! Only the sole common stream and eight original runtime headers are public
ports of the complete axis machine. Every other tape is blank at both endpoints,
so the whole routine can be lifted onto one shared counted-schedule caller. -/
namespace IntegerMultBounds.Machine.ButterflyAxisPorts
noncomputable section
open ButterflyAxisBank

abbrev count := 63+LocalTapes

def ports (i : Fin 9) : Fin count := Fin.castAdd LocalTapes (![56,52,53,57,58,59,60,61,62] i : Fin 63)

theorem injective : Function.Injective ports := by decide

def headers (bs ls : List Bool) (hs : Fin 6 → List Bool) : Tapes 8 2 :=
  (ButterflyStreamCleanData.headers bs ls).append (RecursiveRowsRoleBank.headers hs)

theorem payload (f : ℤ → Fin 6) (bs ls : List Bool) (hs : Fin 6 → List Bool) :
    SharedBank.payload (bank blankStreams f bs ls hs) ports=
      (CountedLoopReuseAlphabet.one f 0).append (headers bs ls hs) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def selection : Fin 9 → Fin 63 := ![56,52,53,57,58,59,60,61,62]

private theorem unselected_blank (f : ℤ → Fin 6) (bs ls : List Bool) (hs : Fin 6 → List Bool)
    (i : Fin count) (hi : ¬∃ j,ports j=i) :
    (bank blankStreams f bs ls hs).head i=0 ∧ (bank blankStreams f bs ls hs).tape i=(fun _ => blank) := by
  induction i using (Fin.addCases (m:=63) (n:=LocalTapes)) with
  | right i => simp [bank,Tapes.append,SharedBank.empty]
  | left i =>
    induction i using (Fin.addCases (m:=56) (n:=7)) with
    | left i =>
      induction i using (Fin.addCases (m:=54) (n:=2)) with
      | right i => simp [bank,common,ButterflyStreamCleanData.bank,CountedLoopHeaderClean.bank,Tapes.append,SharedBank.empty]
      | left i =>
        induction i using (Fin.addCases (m:=52) (n:=2)) with
        | right i =>
          fin_cases i
          · exact (hi ⟨1,rfl⟩).elim
          · exact (hi ⟨2,rfl⟩).elim
        | left i =>
          induction i using (Fin.addCases (m:=4) (n:=48)) with
          | left i => simp [bank,common,ButterflyStreamCleanData.bank,CountedLoopHeaderClean.bank,
              ButterflyStreamCleanData.original,data,Tapes.append]; rfl
          | right i => simp [bank,common,ButterflyStreamCleanData.bank,CountedLoopHeaderClean.bank,
              ButterflyStreamCleanData.original,data,Tapes.append,RadixLinearCombinationBootstrap.empty]
    | right i =>
      induction i using (Fin.addCases (m:=1) (n:=6)) with
      | left i => fin_cases i; exact (hi ⟨0,rfl⟩).elim
      | right i =>
        fin_cases i
        · exact (hi ⟨3,rfl⟩).elim
        · exact (hi ⟨4,rfl⟩).elim
        · exact (hi ⟨5,rfl⟩).elim
        · exact (hi ⟨6,rfl⟩).elim
        · exact (hi ⟨7,rfl⟩).elim
        · exact (hi ⟨8,rfl⟩).elim

theorem clean (f : ℤ → Fin 6) (bs ls : List Bool) (hs : Fin 6 → List Bool) :
    SharedBank.strip (bank blankStreams f bs ls hs) ports=SharedBank.empty count 2 := by
  apply congrArg₂ Tapes.mk
  · funext i
    by_cases hi : ∃ j,ports j=i
    · simp [hi]
    · simpa only [hi,ite_false] using (unselected_blank f bs ls hs i hi).1
  · funext i
    by_cases hi : ∃ j,ports j=i
    · simp [hi]
    · simpa only [hi,ite_false] using (unselected_blank f bs ls hs i hi).2

end
end IntegerMultBounds.Machine.ButterflyAxisPorts
