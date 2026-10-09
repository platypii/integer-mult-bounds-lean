import IntegerMultBounds.Machine.CompactReservedHeaders

/-! Forward and inverse sparse bodies preserve original global geometry and
all generated interval controls, changing only ordinal and coefficient word. -/
namespace IntegerMultBounds.Machine.CompactReservedAxisRun
noncomputable section
open CompactReservedHeaders
open CompactFallbackAxisRun (Array Width word volume)

def common (st : ActiveRepairRankHeadersCommands.State) (f : ℤ → Fin 6) :=
  (ActiveRepairRankHeadersCommands.bank st).append (CountedLoopReuseAlphabet.one f 0)
def bank (st : ActiveRepairRankHeadersCommands.State) (f : ℤ → Fin 6) :=
  (common st f).append (SharedBank.empty CompactReservedAxisPorts.count 2)
def focus : Fin 7 → Fin 44 := ![0,1,2,3,4,5,43]
theorem focus_injective : Function.Injective focus := by decide

def code (inverse : Bool) : Σ s,Program (44+CompactReservedAxisPorts.count) s 2 :=
  if inverse then ⟨_,Placement.placed CompactFallbackInverseAxis.program
    (CleanSubbank.placement CompactReservedAxisPorts.ports focus focus_injective)⟩
  else ⟨_,Placement.placed CompactFallbackAxisRun.program
    (CleanSubbank.placement CompactReservedAxisPorts.ports focus focus_injective)⟩

def step (inverse : Bool) (D K rho ell q i : ℕ) (f : Array D K ell) :=
  if inverse then CompactFallbackInverseSchedule.step D K rho ell q i f
  else CompactFallbackSchedule.step D K rho ell q i f

def run (inverse : Bool) (D K rho ell q start : ℕ) : ℕ → Array D K ell → Array D K ell
  | 0,f => f
  | n+1,f => step inverse D K rho ell q (start+n) (run inverse D K rho ell q start n f)

theorem width_run (inverse : Bool) (D K rho ell q start n : ℕ) (f : Array D K ell) (hw : Width D K ell q f) :
    Width D K ell q (run inverse D K rho ell q start n f) := by
  induction n with
  | zero => exact hw
  | succ n ih =>
    cases inverse
    · simp only [run,step,Bool.false_eq_true,ite_false,CompactFallbackSchedule.step]
      split_ifs with ht
      · exact ButterflyAxisArray.width_apply _ _ _ _ ht _ ih
      · exact ih
    · simp only [run,step,ite_true,CompactFallbackInverseSchedule.step]
      split_ifs with ht
      · exact ButterflyInverseAxisArray.width_apply _ _ _ _ ht _ ih
      · exact ih

theorem payload (c m D K rho ell q d G i : ℕ) (f : ℤ → Fin 6) :
    SharedBank.payload (common (prepared c m D K rho ell q d G i) f) focus=
      CompactReservedAxisPorts.payload D K rho ell q i f := by
  apply congrArg₂ Tapes.mk <;> funext s <;> fin_cases s <;> rfl

theorem frame (c m D K rho ell q d G i j : ℕ) (f g : ℤ → Fin 6) :
    SharedBank.strip (common (prepared c m D K rho ell q d G i) f) focus=
      SharedBank.strip (common (prepared c m D K rho ell q d G j) g) focus := by
  apply congrArg₂ Tapes.mk
  · funext s; fin_cases s <;> rfl
  · funext s
    by_cases hs : ∃ j,focus j=s
    · simp only [hs,ite_true]
    · simp only [hs,ite_false]
      fin_cases s
      all_goals first | rfl | exact (hs ⟨5,rfl⟩).elim | exact (hs ⟨6,rfl⟩).elim

theorem runs (inverse : Bool) (c m D K rho ell q d G i : ℕ) (hK : 0<K) (hr : rho<K) (hi : i<D)
    (f : Array D K ell) (hw : Width D K ell q f) :
    HoareTime (code inverse).2
      (fun v => v=bank (prepared c m D K rho ell q d G i) (word f))
      (fun v => v=bank (prepared c m D K rho ell q d G (i+1)) (word (step inverse D K rho ell q i f)))
      (CompactFallbackAxisBudget.constant*volume D K ell q) := by
  have ht := CompactFallbackHeaders.selected_lt D K rho i hK hr hi
  cases inverse
  · simp only [code,Bool.false_eq_true,ite_false,step,CompactFallbackSchedule.step,dite_eq_left ht]
    have hh := CompactFallbackAxisBudget.runs_linear D K rho ell q i hK hr hi f hw
    apply CleanSubbank.realizes (c:=7) (s:=CompactReservedAxisPorts.count) (k:=44) CompactFallbackAxisRun.program
      CompactReservedAxisPorts.ports focus CompactReservedAxisPorts.injective focus_injective
      (common (prepared c m D K rho ell q d G i) (word f))
      (common (prepared c m D K rho ell q d G (i+1)) (word (CompactFallbackAxisRun.applyAxis D K rho ell q i ht f)))
      _ _ _ ?_ ?_ ?_ ?_ ?_ hh
    · exact (payload _ _ _ _ _ _ _ _ _ _ _).symm
    · exact (payload _ _ _ _ _ _ _ _ _ _ _).symm
    · exact CompactReservedAxisPorts.clean _ _ _ _ _ _ _
    · exact CompactReservedAxisPorts.clean _ _ _ _ _ _ _
    · exact frame _ _ _ _ _ _ _ _ _ _ _ _ _
  · simp only [code,ite_true,step,CompactFallbackInverseSchedule.step,dite_eq_left ht]
    have hh := CompactFallbackInverseAxis.runs_linear D K rho ell q i hK hr hi f hw
    apply CleanSubbank.realizes (c:=7) (s:=CompactReservedAxisPorts.count) (k:=44) CompactFallbackInverseAxis.program
      CompactReservedAxisPorts.ports focus CompactReservedAxisPorts.injective focus_injective
      (common (prepared c m D K rho ell q d G i) (word f))
      (common (prepared c m D K rho ell q d G (i+1)) (word (CompactFallbackInverseAxis.applyAxis D K rho ell q i ht f)))
      _ _ _ ?_ ?_ ?_ ?_ ?_ hh
    · exact (payload _ _ _ _ _ _ _ _ _ _ _).symm
    · exact (payload _ _ _ _ _ _ _ _ _ _ _).symm
    · exact CompactReservedAxisPorts.clean _ _ _ _ _ _ _
    · exact CompactReservedAxisPorts.clean _ _ _ _ _ _ _
    · exact frame _ _ _ _ _ _ _ _ _ _ _ _ _

end
end IntegerMultBounds.Machine.CompactReservedAxisRun
