import IntegerMultBounds.Machine.ActiveRepairRankParserPlaced
import IntegerMultBounds.Machine.ActiveRepairEarlyFieldsPlaced

/-! Actual original-rank parsing feeds the inverse/guard/ideal computation.
Current source controls are physically extracted, not supplied as a common
word for the stream. Runtime field descriptors remain explicit originals. -/
namespace IntegerMultBounds.Machine.ActiveRepairEarlySourceRun
noncomputable section
open ActiveRepairRankFieldsBank (offsetSlot widthSlot)
open SharedPlacementAlphabet (setTape)

def bank (cs : List Bool) (ws : Fin 5 → List Bool) (hs : Fin 8 → List Bool)
    (ss : Fin 4 → List Bool) (bs : List Bool) : Tapes 22 1 :=
  (ActiveRepairRankFieldsBank.bank cs ws hs ss).append
    (⟨![1,0,0,0],![RadixZeroFill.encodedBinary bs,fun _ => blank,fun _ => blank,fun _ => blank]⟩ : Tapes 4 1)

def parseFocus : Fin 18 → Fin 22 := Fin.castAdd 4
def repairFocus : Fin 10 → Fin 22 := ![1,2,5,14,18,15,0,19,20,21]
theorem parse_injective : Function.Injective parseFocus := Fin.castAdd_injective _ _
theorem repair_injective : Function.Injective repairFocus := by decide

def repairHeaders (ss : Fin 4 → List Bool) (bs : List Bool) : Fin 3 → List Bool := ![ss 0,bs,ss 1]
def parsed (cs : List Bool) (starts widths : Fin 4 → ℕ) (q rho n : ℕ)
    (hs : Fin 8 → List Bool) (ss : Fin 4 → List Bool) (bs : List Bool) :=
  bank cs (ActiveRepairRankFieldsRun.finished cs starts widths q rho n) hs ss bs

def fullBank (v : Tapes 22 1) := CleanSubbank.bank (s := 30) v

def parseProgram := extend (ActiveRepairRankParserPlaced.program parseFocus parse_injective) 3

def program := seq parseProgram (ActiveRepairEarlyFieldsPlaced.program repairFocus repair_injective)

theorem pad (v : Tapes 22 1) :
    (CleanSubbank.bank (s := 27) v).append (SharedBank.empty 3 1)=fullBank v := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem parse_sources (cs : List Bool) (hs : Fin 8 → List Bool) (ss : Fin 4 → List Bool) (bs : List Bool) :
    SharedBank.payload (bank cs ActiveRepairRankFieldsRun.empty hs ss bs) parseFocus=
      ActiveRepairRankParserPlaced.sources cs hs ss := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem parse_result (cs : List Bool) (hs : Fin 8 → List Bool) (ss : Fin 4 → List Bool)
    (bs : List Bool) (ws : Fin 5 → List Bool) :
    ActiveRepairRankParserPlaced.result (bank cs ActiveRepairRankFieldsRun.empty hs ss bs) parseFocus ws=
      bank cs ws hs ss bs := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem repair_sources (cs : List Bool) (starts widths : Fin 4 → ℕ) (q rho n : ℕ)
    (hs : Fin 8 → List Bool) (ss : Fin 4 → List Bool) (bs : List Bool) :
    SharedBank.payload (parsed cs starts widths q rho n hs ss bs) repairFocus=
      ActiveRepairEarlyFieldsPlaced.sources
        (Gather.field cs (starts 0) (widths 0)) (Gather.field cs (starts 1) (widths 1))
        (SelectedSourceBitsData.selected (Gather.field cs (starts 3) (widths 3)) q rho n) cs (repairHeaders ss bs) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem runs (cs : List Bool) (starts widths : Fin 4 → ℕ) (hs : Fin 8 → List Bool)
    (ss : Fin 4 → List Bool) (bs : List Bool)
    (hv0 : ∀ i, Counter.value (hs (offsetSlot i))=starts i)
    (hv1 : ∀ i, Counter.value (hs (widthSlot i))=widths i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (q b rho n f A : ℕ) (hb : 1≤b) (hbq : b+1≤q) (hbq3 : b+3≤q)
    (hwidth : widths 3=f*q) (hV : widths 0=n*q) (hT : widths 1=n*b)
    (hnf : n+1=f) (hr : rho<q)
    (sv : ∀ i, Counter.value (ss i)=SelectedSourceBitsRun.values q n rho f i)
    (sc : ∀ i, GrowingCounterData.Canonical (ss i))
    (bv : Counter.value bs=b) (bc : GrowingCounterData.Canonical bs)
    (hfit : ∀ i, starts i+widths i≤A) :
    HoareTime program
      (fun z => z=fullBank (bank cs ActiveRepairRankFieldsRun.empty hs ss bs))
      (fun z => z=fullBank (ActiveRepairEarlyFieldsPlaced.result
        (parsed cs starts widths q rho n hs ss bs) repairFocus q b hb hbq
        (Gather.field cs (starts 0) (widths 0)) (Gather.field cs (starts 1) (widths 1))
        (SelectedSourceBitsData.selected (Gather.field cs (starts 3) (widths 3)) q rho n)))
      (1200*(A+1)+5+4400*((n+1)*(q+b+1))) := by
  have h0 := ActiveRepairRankParserPlaced.runs _ parseFocus parse_injective cs starts widths hs ss
    (parse_sources cs hs ss bs) hv0 hv1 hc q rho n f A hwidth hnf hr sv sc hfit
  rw [parse_result] at h0
  have h0' := hoare_extend_eq h0 (SharedBank.empty 3 1)
  simp only [pad] at h0'
  have h1 := ActiveRepairEarlyFieldsPlaced.runs _ repairFocus repair_injective q b hb hbq hbq3
    (Gather.field cs (starts 0) (widths 0)) (Gather.field cs (starts 1) (widths 1))
    (SelectedSourceBitsData.selected (Gather.field cs (starts 3) (widths 3)) q rho n) cs (repairHeaders ss bs)
    (repair_sources cs starts widths q rho n hs ss bs)
    (by simp [hV]) (by simp [hT])
    (by intro i; fin_cases i; exact sv 0; exact bv;
        change Counter.value (ss 1)=(SelectedSourceBitsData.selected
          (Gather.field cs (starts 3) (widths 3)) q rho n).length
        rw [SelectedSourceBitsData.selected_length]
        exact sv 1)
    (by intro i; fin_cases i; exact sc 0; exact bc; exact sc 1)
  simpa only [program,parseProgram,parsed,fullBank,SelectedSourceBitsData.selected_length] using h0'.seq h1

theorem runs_linear (cs : List Bool) (starts widths : Fin 4 → ℕ) (hs : Fin 8 → List Bool)
    (ss : Fin 4 → List Bool) (bs : List Bool)
    (hv0 : ∀ i, Counter.value (hs (offsetSlot i))=starts i)
    (hv1 : ∀ i, Counter.value (hs (widthSlot i))=widths i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (q b rho n f A : ℕ) (hb : 1≤b) (hbq : b+1≤q) (hbq3 : b+3≤q)
    (hwidth : widths 3=f*q) (hV : widths 0=n*q) (hT : widths 1=n*b)
    (hnf : n+1=f) (hr : rho<q)
    (sv : ∀ i, Counter.value (ss i)=SelectedSourceBitsRun.values q n rho f i)
    (sc : ∀ i, GrowingCounterData.Canonical (ss i))
    (bv : Counter.value bs=b) (bc : GrowingCounterData.Canonical bs)
    (hfit : ∀ i, starts i+widths i≤A) :
    HoareTime program
      (fun z => z=fullBank (bank cs ActiveRepairRankFieldsRun.empty hs ss bs))
      (fun z => z=fullBank (ActiveRepairEarlyFieldsPlaced.result
        (parsed cs starts widths q rho n hs ss bs) repairFocus q b hb hbq
        (Gather.field cs (starts 0) (widths 0)) (Gather.field cs (starts 1) (widths 1))
        (SelectedSourceBitsData.selected (Gather.field cs (starts 3) (widths 3)) q rho n)))
      (27600*(A+1)+5) := by
  have h0 := runs cs starts widths hs ss bs hv0 hv1 hc q b rho n f A hb hbq hbq3 hwidth hV hT hnf hr sv sc bv bc hfit
  have hsource : f*q≤A := by have := hfit 3; rw [hwidth] at this; omega
  have hnq : n*q≤A := by have := hfit 0; rw [hV] at this; omega
  have hnb : n*b≤A := by have := hfit 1; rw [hT] at this; omega
  have hq : q≤A := (Nat.le_mul_of_pos_left q (by omega : 0<f)).trans hsource
  have hbA : b≤A := by omega
  have hn : n≤A := (Nat.le_mul_of_pos_right n (by omega : 0<q)).trans hnq
  have hstride : (n+1)*(q+b+1)≤6*(A+1) := by nlinarith
  exact h0.consequence (fun _ h => h) (fun _ h => h) (by nlinarith)

end
end IntegerMultBounds.Machine.ActiveRepairEarlySourceRun
