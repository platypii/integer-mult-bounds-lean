import IntegerMultBounds.Machine.CompactFallbackHeaders

/-! One fixed sparse-axis fallback body computes its own original-header
butterfly inputs, executes the complete native coefficient machine, erases all
derived headers and increments the original chunk ordinal. Spectator bits and
all polynomial coefficients remain in the same literal global stream. -/
namespace IntegerMultBounds.Machine.CompactFallbackAxisRun
noncomputable section
open CompactFallbackHeaders
open ButterflyStreamData (full)

abbrev Array (D K ell : ℕ) := ButterflyAxisArray.Array (bits D K) (polynomials ell)
abbrev Width (D K ell q : ℕ) (f : Array D K ell) :=
  ButterflyAxisArray.Width (bits D K) (polynomials ell) (reservation D K q) f

def word {D K ell : ℕ} (f : Array D K ell) := full (fun _ => blank) 0 f

def common (st : ActiveRepairRankHeadersCommands.State) (f : ℤ → Fin 6) :=
  (ActiveRepairRankHeadersCommands.bank st).append (CountedLoopReuseAlphabet.one f 0)
def bank (st : ActiveRepairRankHeadersCommands.State) (f : ℤ → Fin 6) :=
  (common st f).append (SharedBank.empty CompactFallbackAxisPorts.count 2)

def focus : Fin 5 → Fin 44 := ![6,7,8,9,43]
theorem focus_injective : Function.Injective focus := by decide

def axisProgram := Placement.placed ButterflyAxisOriginal.program
  (CleanSubbank.placement CompactFallbackAxisPorts.ports focus focus_injective)
def headerProgram (ops : List ButterflyAxisHeadersArithmetic.Op) :=
  extend (extend (ButterflyAxisHeadersArithmetic.compile (a:=2) ops).2 1) CompactFallbackAxisPorts.count
def program := seq (seq (headerProgram setup) axisProgram) (headerProgram cleanup)

def applyAxis (D K rho ell q i : ℕ) (ht : selected K rho i<bits D K) (f : Array D K ell) :=
  ButterflyAxisArray.applyAxis (bits D K) (selected K rho i) (polynomials ell) (reservation D K q) ht f

theorem payload (D K rho ell q i shift : ℕ) (f : ℤ → Fin 6) :
    SharedBank.payload (common (prepared D K rho ell q i shift) f) focus=
      CompactFallbackAxisPorts.payload (bits D K) (selected K rho i+shift) (polynomials ell) (reservation D K q) f := by
  apply congrArg₂ Tapes.mk <;> funext s <;> fin_cases s <;> rfl

theorem frame (D K rho ell q i : ℕ) (f g : ℤ → Fin 6) :
    SharedBank.strip (common (prepared D K rho ell q i 0) f) focus=
      SharedBank.strip (common (prepared D K rho ell q i 1) g) focus := by
  apply congrArg₂ Tapes.mk
  · funext s; fin_cases s <;> rfl
  · funext s
    by_cases hs : ∃ j,focus j=s
    · simp only [hs,ite_true]
    · simp only [hs,ite_false]
      fin_cases s
      all_goals first | rfl | exact (hs ⟨1,rfl⟩).elim | exact (hs ⟨4,rfl⟩).elim

theorem axis_runs (D K rho ell q i : ℕ) (ht : selected K rho i<bits D K)
    (f : Array D K ell) (hw : Width D K ell q f) :
    HoareTime axisProgram
      (fun v => v=bank (prepared D K rho ell q i 0) (word f))
      (fun v => v=bank (prepared D K rho ell q i 1) (word (applyAxis D K rho ell q i ht f)))
      (ButterflyAxisOriginal.constant*ButterflyAxisHeadersBudget.logicalVolume (bits D K) (polynomials ell) (reservation D K q)) := by
  have hh := ButterflyAxisArray.runs (bits D K) (selected K rho i) (polynomials ell) (reservation D K q)
    ht (pow_pos (by decide) ell) f hw
  apply CleanSubbank.realizes (c:=5) (s:=CompactFallbackAxisPorts.count) (k:=44) ButterflyAxisOriginal.program
    CompactFallbackAxisPorts.ports focus CompactFallbackAxisPorts.injective focus_injective
    (common (prepared D K rho ell q i 0) (word f))
    (common (prepared D K rho ell q i 1) (word (applyAxis D K rho ell q i ht f))) _ _ _ ?_ ?_ ?_ ?_ ?_ hh
  · rw [CompactFallbackAxisPorts.selected,payload]; rfl
  · rw [CompactFallbackAxisPorts.selected,payload]; rfl
  · exact CompactFallbackAxisPorts.clean _ _ _ _ _
  · exact CompactFallbackAxisPorts.clean _ _ _ _ _
  · exact frame D K rho ell q i _ _

def volume (D K ell q : ℕ) := ButterflyAxisHeadersBudget.logicalVolume (bits D K) (polynomials ell) (reservation D K q)
def cost (D K rho ell q i : ℕ) :=
  ButterflyAxisHeadersArithmetic.scheduleCost setup (initial D K rho ell q i)+
    ButterflyAxisOriginal.constant*volume D K ell q+
    ButterflyAxisHeadersArithmetic.scheduleCost cleanup (prepared D K rho ell q i 1)+2

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

end
end IntegerMultBounds.Machine.CompactFallbackAxisRun
