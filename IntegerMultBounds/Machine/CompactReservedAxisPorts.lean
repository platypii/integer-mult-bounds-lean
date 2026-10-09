import IntegerMultBounds.Machine.CompactFallbackRoundtripBudget

/-! Sparse-axis public ports expose just the original six numeric descriptors
and the complete native word. This permits global reservation controls to be
framed while all generated butterfly geometry remains private. -/
namespace IntegerMultBounds.Machine.CompactReservedAxisPorts
noncomputable section
abbrev count := 44+CompactFallbackAxisPorts.count

def ports (i : Fin 7) : Fin count :=
  Fin.castAdd CompactFallbackAxisPorts.count (![0,1,2,3,4,5,43] i : Fin 44)
theorem injective : Function.Injective ports := by decide

def payload (D K rho ell q i : ℕ) (f : ℤ → Fin 6) :=
  SharedBank.payload (CompactFallbackAxisRun.bank (CompactFallbackHeaders.initial D K rho ell q i) f) ports

private theorem unselected (D K rho ell q i : ℕ) (f : ℤ → Fin 6) (s : Fin count)
    (hs : ¬∃ j,ports j=s) :
    (CompactFallbackAxisRun.bank (CompactFallbackHeaders.initial D K rho ell q i) f).head s=0 ∧
    (CompactFallbackAxisRun.bank (CompactFallbackHeaders.initial D K rho ell q i) f).tape s=(fun _ => blank) := by
  induction s using (Fin.addCases (m:=44) (n:=CompactFallbackAxisPorts.count)) with
  | right s => simp [CompactFallbackAxisRun.bank,Tapes.append,SharedBank.empty]
  | left s =>
    induction s using (Fin.addCases (m:=43) (n:=1)) with
    | right s => fin_cases s; exact (hs ⟨6,rfl⟩).elim
    | left s =>
      induction s using (Fin.addCases (m:=28) (n:=15)) with
      | right s => simp [CompactFallbackAxisRun.bank,CompactFallbackAxisRun.common,
          ActiveRepairRankHeadersCommands.bank,CleanSubbank.bank,Tapes.append,SharedBank.empty]
      | left s =>
        have hn : CompactFallbackHeaders.initial D K rho ell q i s=none := by
          fin_cases s
          · exact (hs ⟨0,rfl⟩).elim
          · exact (hs ⟨1,rfl⟩).elim
          · exact (hs ⟨2,rfl⟩).elim
          · exact (hs ⟨3,rfl⟩).elim
          · exact (hs ⟨4,rfl⟩).elim
          · exact (hs ⟨5,rfl⟩).elim
          all_goals rfl
        simp [CompactFallbackAxisRun.bank,CompactFallbackAxisRun.common,
          ActiveRepairRankHeadersCommands.bank,CleanSubbank.bank,
          ActiveRepairRankHeadersCommands.caller,Tapes.append,hn]

theorem clean (D K rho ell q i : ℕ) (f : ℤ → Fin 6) :
    SharedBank.strip (CompactFallbackAxisRun.bank (CompactFallbackHeaders.initial D K rho ell q i) f) ports=
      SharedBank.empty count 2 := by
  apply congrArg₂ Tapes.mk
  · funext s
    by_cases hs : ∃ j,ports j=s
    · simp [hs]
    · simpa only [hs,ite_false] using (unselected D K rho ell q i f s hs).1
  · funext s
    by_cases hs : ∃ j,ports j=s
    · simp [hs]
    · simpa only [hs,ite_false] using (unselected D K rho ell q i f s hs).2

end
end IntegerMultBounds.Machine.CompactReservedAxisPorts
