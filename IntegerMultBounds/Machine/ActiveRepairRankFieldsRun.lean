import IntegerMultBounds.Machine.ActiveRepairRankFieldsBank

/-! Four literal field extractions reuse one counter and scratch bank, then
actual selected-source extraction reads the fourth full source word. All
runtime offsets, widths and original selection headers are retained. -/
namespace IntegerMultBounds.Machine.ActiveRepairRankFieldsRun
noncomputable section
open ActiveRepairRankFieldsBank
open SelectedSourceBitsScan (word)
open SharedPlacementAlphabet (setTape)

def empty : Fin 5 → List Bool := fun _ => []
def first (cs : List Bool) (starts widths : Fin 4 → ℕ) := Function.update empty 0 (Gather.field cs (starts 0) (widths 0))
def second (cs : List Bool) (starts widths : Fin 4 → ℕ) := Function.update (first cs starts widths) 1 (Gather.field cs (starts 1) (widths 1))
def third (cs : List Bool) (starts widths : Fin 4 → ℕ) := Function.update (second cs starts widths) 2 (Gather.field cs (starts 2) (widths 2))
def fourth (cs : List Bool) (starts widths : Fin 4 → ℕ) := Function.update (third cs starts widths) 3 (Gather.field cs (starts 3) (widths 3))

def source (cs : List Bool) (starts widths : Fin 4 → ℕ) := Gather.field cs (starts 3) (widths 3)
def outputs (cs : List Bool) (starts widths : Fin 4 → ℕ) : Fin 5 → List Bool :=
  ![Gather.field cs (starts 0) (widths 0),Gather.field cs (starts 1) (widths 1),
    Gather.field cs (starts 2) (widths 2),source cs starts widths,[]]

theorem fourth_eq (cs : List Bool) (starts widths : Fin 4 → ℕ) : fourth cs starts widths=outputs cs starts widths := by
  funext i
  fin_cases i <;> simp [fourth,third,second,first,empty,outputs,source]

def fieldsProgram := seq (seq (seq (stage 0) (stage 1)) (stage 2)) (stage 3)
def fieldsCost (starts widths : Fin 4 → ℕ) :=
  200*(starts 0+widths 0+1)+200*(starts 1+widths 1+1)+
    200*(starts 2+widths 2+1)+200*(starts 3+widths 3+1)+3

variable (cs : List Bool) (starts widths : Fin 4 → ℕ) (hs : Fin 8 → List Bool) (ss : Fin 4 → List Bool)
variable (hv0 : ∀ i, Counter.value (hs (offsetSlot i))=starts i)
variable (hv1 : ∀ i, Counter.value (hs (widthSlot i))=widths i)
variable (hc : ∀ i, GrowingCounterData.Canonical (hs i))

include hv0 hv1 hc in
theorem fields_run :
    HoareTime fieldsProgram (fun v => v=CleanSubbank.bank (s := 9) (bank cs empty hs ss))
      (fun v => v=CleanSubbank.bank (s := 9) (bank cs (outputs cs starts widths) hs ss))
      (fieldsCost starts widths) := by
  have h0 := field_runs cs empty hs ss 0 rfl (starts 0) (widths 0) (hv0 0) (hv1 0) (hc _) (hc _)
  have h1 := field_runs cs (first cs starts widths) hs ss 1 (by simp [first,empty])
    (starts 1) (widths 1) (hv0 1) (hv1 1) (hc _) (hc _)
  have h2 := field_runs cs (second cs starts widths) hs ss 2 (by simp [second,first,empty])
    (starts 2) (widths 2) (hv0 2) (hv1 2) (hc _) (hc _)
  have h3 := field_runs cs (third cs starts widths) hs ss 3 (by simp [third,second,first,empty])
    (starts 3) (widths 3) (hv0 3) (hv1 3) (hc _) (hc _)
  have h := ((h0.seq h1).seq h2).seq h3
  have he : Function.update (third cs starts widths) (Fin.castAdd 1 (3 : Fin 4))
      (Gather.field cs (starts 3) (widths 3))=outputs cs starts widths := fourth_eq cs starts widths
  rw [he] at h
  exact h.consequence (fun _ h => h) (fun _ h => h) (by unfold fieldsCost; omega)

def selectionFocus : Fin 6 → Fin 18 := ![4,5,14,15,16,17]
theorem selectionFocus_injective : Function.Injective selectionFocus := by decide

def selectionProgram := SelectedSourceBitsPlaced.program (a := 1) selectionFocus selectionFocus_injective

def finished (cs : List Bool) (starts widths : Fin 4 → ℕ) (q rho n : ℕ) :=
  Function.update (outputs cs starts widths) 4 (SelectedSourceBitsData.selected (source cs starts widths) q rho n)

theorem selection_sources (xs : List Bool) (ws : Fin 5 → List Bool) (hs : Fin 8 → List Bool)
    (ss : Fin 4 → List Bool) (cs : List Bool) (h3 : ws 3=xs) (h4 : ws 4=[]) :
    SharedBank.payload (bank cs ws hs ss) selectionFocus=SelectedSourceBitsPlaced.sources xs ss := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals first | rfl | exact congrArg (word (a := 1)) h3 | exact congrArg (word (a := 1)) h4 | exact CountedLoopReuseAlphabet.encoding_binary _

theorem selection_result (ws : Fin 5 → List Bool) (hs : Fin 8 → List Bool)
    (ss : Fin 4 → List Bool) (cs xs : List Bool) :
    setTape (bank cs ws hs ss) (selectionFocus 1) (word xs) 0=
      bank cs (Function.update ws 4 xs) hs ss := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals simp [bank,selectionFocus,Function.update]

theorem selection_run (q rho n f : ℕ) (hwidth : widths 3=f*q) (hnf : n+1=f) (hr : rho<q)
    (sv : ∀ i, Counter.value (ss i)=SelectedSourceBitsRun.values q n rho f i)
    (sc : ∀ i, GrowingCounterData.Canonical (ss i)) :
    HoareTime selectionProgram
      (fun v => v=CleanSubbank.bank (s := 9) (bank cs (outputs cs starts widths) hs ss))
      (fun v => v=CleanSubbank.bank (s := 9) (bank cs (finished cs starts widths q rho n) hs ss))
      (400*(widths 3)) := by
  have h := SelectedSourceBitsPlaced.runs (bank cs (outputs cs starts widths) hs ss)
    selectionFocus selectionFocus_injective (source cs starts widths) ss q rho n f
    (selection_sources _ _ _ _ _ rfl rfl) (by simp [source,hwidth]) hnf hr sv sc
  unfold SelectedSourceBitsPlaced.result at h
  rw [selection_result] at h
  simpa only [source,Gather.field_length,finished,selectionProgram] using h

def program := seq fieldsProgram selectionProgram

include hv0 hv1 hc in
theorem runs (q rho n f : ℕ) (hwidth : widths 3=f*q) (hnf : n+1=f) (hr : rho<q)
    (sv : ∀ i, Counter.value (ss i)=SelectedSourceBitsRun.values q n rho f i)
    (sc : ∀ i, GrowingCounterData.Canonical (ss i)) :
    HoareTime program (fun v => v=CleanSubbank.bank (s := 9) (bank cs empty hs ss))
      (fun v => v=CleanSubbank.bank (s := 9) (bank cs (finished cs starts widths q rho n) hs ss))
      (fieldsCost starts widths+400*(widths 3)+1) := by
  have h := (fields_run cs starts widths hs ss hv0 hv1 hc).seq
    (selection_run cs starts widths hs ss q rho n f hwidth hnf hr sv sc)
  exact h.consequence (fun _ h => h) (fun _ h => h) (by omega)

theorem cost_linear (A : ℕ) (hfit : ∀ i, starts i+widths i≤A) :
    fieldsCost starts widths+400*(widths 3)+1≤1200*(A+1)+4 := by
  have h0 := hfit 0
  have h1 := hfit 1
  have h2 := hfit 2
  have h3 := hfit 3
  unfold fieldsCost
  omega

include hv0 hv1 hc in
theorem runs_linear (q rho n f A : ℕ) (hwidth : widths 3=f*q) (hnf : n+1=f) (hr : rho<q)
    (sv : ∀ i, Counter.value (ss i)=SelectedSourceBitsRun.values q n rho f i)
    (sc : ∀ i, GrowingCounterData.Canonical (ss i)) (hfit : ∀ i, starts i+widths i≤A) :
    HoareTime program (fun v => v=CleanSubbank.bank (s := 9) (bank cs empty hs ss))
      (fun v => v=CleanSubbank.bank (s := 9) (bank cs (finished cs starts widths q rho n) hs ss))
      (1200*(A+1)+4) :=
  (runs cs starts widths hs ss hv0 hv1 hc q rho n f hwidth hnf hr sv sc).consequence
    (fun _ h => h) (fun _ h => h) (cost_linear starts widths A hfit)

end
end IntegerMultBounds.Machine.ActiveRepairRankFieldsRun
