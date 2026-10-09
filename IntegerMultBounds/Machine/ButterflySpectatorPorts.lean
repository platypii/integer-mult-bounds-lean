import IntegerMultBounds.Machine.ButterflySpectatorOriginal

/-! Six public ports of the actual spectator-preserving butterfly: immutable
bit dimension, selected bit, polynomial count, precision, outer rows, native word.
All other local tapes start and finish blank for repeated leaf execution. -/
namespace IntegerMultBounds.Machine.ButterflySpectatorPorts
noncomputable section
abbrev count := 52+ButterflyAxisPorts.count

def ports (i : Fin 6) : Fin count := Fin.castAdd ButterflyAxisPorts.count (![0,1,2,3,18,43] i : Fin 52)
theorem injective : Function.Injective ports := by decide

def payload (rows D t R p : ℕ) (f : ℤ → Fin 6) :=
  SharedBank.payload (ButterflySpectatorOriginal.bank rows D t R p f) ports

private theorem unselected (rows D t R p : ℕ) (f : ℤ → Fin 6) (i : Fin count)
    (hi : ¬∃ j,ports j=i) :
    (ButterflySpectatorOriginal.bank rows D t R p f).head i=0 ∧
    (ButterflySpectatorOriginal.bank rows D t R p f).tape i=(fun _ => blank) := by
  induction i using (Fin.addCases (m:=52) (n:=ButterflyAxisPorts.count)) with
  | right i => simp [ButterflySpectatorOriginal.bank,Tapes.append,SharedBank.empty]
  | left i =>
    induction i using (Fin.addCases (m:=44) (n:=8)) with
    | right i => simp [ButterflySpectatorOriginal.bank,ButterflyAxisHeadersInstall.input,Tapes.append,SharedBank.empty]
    | left i =>
      induction i using (Fin.addCases (m:=43) (n:=1)) with
      | right i => fin_cases i; exact (hi ⟨5,rfl⟩).elim
      | left i =>
        induction i using (Fin.addCases (m:=28) (n:=15)) with
        | right i => simp [ButterflySpectatorOriginal.bank,ButterflyAxisHeadersInstall.input,
            ButterflyAxisHeadersInstall.caller,ActiveRepairRankHeadersCommands.bank,CleanSubbank.bank,
            Tapes.append,SharedBank.empty]
        | left i =>
          have hn : ButterflySpectatorHeaders.initial rows D t R p i=none := by
            fin_cases i
            · exact (hi ⟨0,rfl⟩).elim
            · exact (hi ⟨1,rfl⟩).elim
            · exact (hi ⟨2,rfl⟩).elim
            · exact (hi ⟨3,rfl⟩).elim
            all_goals first | rfl | exact (hi ⟨4,rfl⟩).elim
          simp [ButterflySpectatorOriginal.bank,ButterflyAxisHeadersInstall.input,
            ButterflyAxisHeadersInstall.caller,ActiveRepairRankHeadersCommands.bank,CleanSubbank.bank,
            ActiveRepairRankHeadersCommands.caller,Tapes.append,hn]

theorem clean (rows D t R p : ℕ) (f : ℤ → Fin 6) :
    SharedBank.strip (ButterflySpectatorOriginal.bank rows D t R p f) ports=SharedBank.empty count 2 := by
  apply congrArg₂ Tapes.mk
  · funext i
    by_cases hi : ∃ j,ports j=i
    · simp [hi]
    · simpa only [hi,ite_false] using (unselected rows D t R p f i hi).1
  · funext i
    by_cases hi : ∃ j,ports j=i
    · simp [hi]
    · simpa only [hi,ite_false] using (unselected rows D t R p f i hi).2

end
end IntegerMultBounds.Machine.ButterflySpectatorPorts
