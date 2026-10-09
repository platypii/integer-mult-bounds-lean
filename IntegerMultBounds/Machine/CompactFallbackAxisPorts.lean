import IntegerMultBounds.Machine.ButterflyIndependentGuardRoundtrip

/-! The full original-header butterfly has only five public ports: its four
numeric inputs and sole native coefficient stream. All remaining local tapes
are physically blank, allowing a sparse-axis caller to install derived headers. -/
namespace IntegerMultBounds.Machine.CompactFallbackAxisPorts
noncomputable section

abbrev count := ButterflyAxisOriginal.count

def ports (i : Fin 5) : Fin count := Fin.castAdd ButterflyAxisPorts.count (![0,1,2,3,43] i : Fin 52)
theorem injective : Function.Injective ports := by decide

def payload (D t R p : ℕ) (f : ℤ → Fin 6) : Tapes 5 2 :=
  ⟨![1,1,1,1,0],![RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits D),
    RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits t),
    RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits R),
    RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits p),f]⟩

theorem selected (D t R p : ℕ) (f : ℤ → Fin 6) :
    SharedBank.payload (ButterflyAxisOriginal.bank D t R p f) ports=payload D t R p f := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

private theorem unselected (D t R p : ℕ) (f : ℤ → Fin 6) (i : Fin count) (hi : ¬∃ j,ports j=i) :
    (ButterflyAxisOriginal.bank D t R p f).head i=0 ∧
    (ButterflyAxisOriginal.bank D t R p f).tape i=(fun _ => blank) := by
  induction i using (Fin.addCases (m:=52) (n:=ButterflyAxisPorts.count)) with
  | right i => simp [ButterflyAxisOriginal.bank,Tapes.append,SharedBank.empty]
  | left i =>
    induction i using (Fin.addCases (m:=44) (n:=8)) with
    | right i => simp [ButterflyAxisOriginal.bank,ButterflyAxisHeadersInstall.input,Tapes.append,SharedBank.empty]
    | left i =>
      induction i using (Fin.addCases (m:=43) (n:=1)) with
      | right i => fin_cases i; exact (hi ⟨4,rfl⟩).elim
      | left i =>
        induction i using (Fin.addCases (m:=28) (n:=15)) with
        | right i => simp [ButterflyAxisOriginal.bank,ButterflyAxisHeadersInstall.input,
            ButterflyAxisHeadersInstall.caller,ActiveRepairRankHeadersCommands.bank,CleanSubbank.bank,
            Tapes.append,SharedBank.empty]
        | left i =>
          have hn : ButterflyAxisHeadersData.initial D t R p i=none := by
            fin_cases i
            · exact (hi ⟨0,rfl⟩).elim
            · exact (hi ⟨1,rfl⟩).elim
            · exact (hi ⟨2,rfl⟩).elim
            · exact (hi ⟨3,rfl⟩).elim
            all_goals rfl
          simp [ButterflyAxisOriginal.bank,ButterflyAxisHeadersInstall.input,
            ButterflyAxisHeadersInstall.caller,ActiveRepairRankHeadersCommands.bank,CleanSubbank.bank,
            ActiveRepairRankHeadersCommands.caller,Tapes.append,hn]

theorem clean (D t R p : ℕ) (f : ℤ → Fin 6) :
    SharedBank.strip (ButterflyAxisOriginal.bank D t R p f) ports=SharedBank.empty count 2 := by
  apply congrArg₂ Tapes.mk
  · funext i
    by_cases hi : ∃ j,ports j=i
    · simp [hi]
    · simpa only [hi,ite_false] using (unselected D t R p f i hi).1
  · funext i
    by_cases hi : ∃ j,ports j=i
    · simp [hi]
    · simpa only [hi,ite_false] using (unselected D t R p f i hi).2

end
end IntegerMultBounds.Machine.CompactFallbackAxisPorts
