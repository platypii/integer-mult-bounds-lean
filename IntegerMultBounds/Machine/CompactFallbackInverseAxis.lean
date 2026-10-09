import IntegerMultBounds.Machine.CompactFallbackAxisBudget

/-! Negative-phase sparse-axis execution reuses the frozen physical header
synthesis and cleanup, replacing only the paid coefficient axis program. -/
namespace IntegerMultBounds.Machine.CompactFallbackInverseAxis
noncomputable section
open CompactFallbackHeaders
open CompactFallbackAxisRun (Array Width word common bank focus focus_injective headerProgram payload frame volume cost)

def axisProgram := Placement.placed ButterflyInverseAxisOriginal.program
  (CleanSubbank.placement CompactFallbackAxisPorts.ports focus focus_injective)
def program := seq (seq (headerProgram setup) axisProgram) (headerProgram cleanup)

def applyAxis (D K rho ell q i : ℕ) (ht : selected K rho i<bits D K) (f : Array D K ell) :=
  ButterflyInverseAxisArray.applyAxis (bits D K) (selected K rho i) (polynomials ell) (reservation D K q) ht f

theorem axis_runs (D K rho ell q i : ℕ) (ht : selected K rho i<bits D K)
    (f : Array D K ell) (hw : Width D K ell q f) :
    HoareTime axisProgram
      (fun v => v=bank (prepared D K rho ell q i 0) (word f))
      (fun v => v=bank (prepared D K rho ell q i 1) (word (applyAxis D K rho ell q i ht f)))
      (ButterflyAxisOriginal.constant*ButterflyAxisHeadersBudget.logicalVolume (bits D K) (polynomials ell) (reservation D K q)) := by
  have hh := ButterflyInverseAxisArray.runs (bits D K) (selected K rho i) (polynomials ell) (reservation D K q)
    ht (pow_pos (by decide) ell) f hw
  apply CleanSubbank.realizes (c:=5) (s:=CompactFallbackAxisPorts.count) (k:=44) ButterflyInverseAxisOriginal.program
    CompactFallbackAxisPorts.ports focus CompactFallbackAxisPorts.injective focus_injective
    (common (prepared D K rho ell q i 0) (word f))
    (common (prepared D K rho ell q i 1) (word (applyAxis D K rho ell q i ht f))) _ _ _ ?_ ?_ ?_ ?_ ?_ hh
  · rw [CompactFallbackAxisPorts.selected,payload]; rfl
  · rw [CompactFallbackAxisPorts.selected,payload]; rfl
  · exact CompactFallbackAxisPorts.clean _ _ _ _ _
  · exact CompactFallbackAxisPorts.clean _ _ _ _ _
  · exact frame D K rho ell q i _ _

theorem runs (D K rho ell q i : ℕ) (ht : selected K rho i<bits D K)
    (f : Array D K ell) (hw : Width D K ell q f) :
    HoareTime program (fun v => v=bank (initial D K rho ell q i) (word f))
      (fun v => v=bank (initial D K rho ell q (i+1)) (word (applyAxis D K rho ell q i ht f)))
      (cost D K rho ell q i) := by
  have hD : 0<D := by
    by_contra h
    have hd : D=0 := by omega
    simp [bits,hd] at ht
  have hK : 0<K := by
    by_contra h
    have hk : K=0 := by omega
    simp [bits,hk] at ht
  have h0 := hoare_extend_eq (hoare_extend_eq (setup_runs D K rho ell q i hD hK)
    (CountedLoopReuseAlphabet.one (word f) 0)) (SharedBank.empty CompactFallbackAxisPorts.count 2)
  have h1 := axis_runs D K rho ell q i ht f hw
  have h2 := hoare_extend_eq (hoare_extend_eq (cleanup_runs D K rho ell q i)
    (CountedLoopReuseAlphabet.one (word (applyAxis D K rho ell q i ht f)) 0)) (SharedBank.empty CompactFallbackAxisPorts.count 2)
  exact ((h0.seq h1).seq h2).consequence (fun _ h => h) (fun _ h => h) (by unfold cost volume; omega)


theorem runs_linear (D K rho ell q i : ℕ) (hK : 0<K) (hr : rho<K) (hi : i<D)
    (f : Array D K ell) (hw : Width D K ell q f) :
    HoareTime program (fun v => v=bank (initial D K rho ell q i) (word f))
      (fun v => v=bank (initial D K rho ell q (i+1))
        (word (applyAxis D K rho ell q i (selected_lt D K rho i hK hr hi) f)))
      (CompactFallbackAxisBudget.constant*volume D K ell q) :=
  (runs D K rho ell q i (selected_lt D K rho i hK hr hi) f hw).consequence
    (fun _ h => h) (fun _ h => h) (CompactFallbackAxisBudget.cost_linear D K rho ell q i hK hr hi)

end
end IntegerMultBounds.Machine.CompactFallbackInverseAxis
