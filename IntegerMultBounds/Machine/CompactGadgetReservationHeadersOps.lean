import IntegerMultBounds.Machine.CompactGadgetReservationHeadersWords

/-! A finite instruction compiler for the concrete reservation headers.
Instructions carry only static tape slots and fixed constants; every runtime
quantity is read from a physical canonical descriptor. -/
namespace IntegerMultBounds.Machine.CompactGadgetReservationHeadersOps
noncomputable section
open CompactGadgetReservationHeadersWords
open CompactGadgetReservationHeadersCore
open CompactGadgetReservationHeadersPowerRound
variable {a : ℕ}

inductive Op where
  | constant (N : ℕ) (dst : Fin 25)
  | erase (dst : Fin 25)
  | product (focus : Fin 3 → Fin 25) (hf : Function.Injective focus)
  | difference (focus : Fin 3 → Fin 25) (hf : Function.Injective focus)
  | round (focus : Fin 3 → Fin 25) (hf : Function.Injective focus)
  | power (focus : Fin 2 → Fin 25) (hf : Function.Injective focus)

def Ready : Op → Words → Prop
  | .constant _ i,xs => xs i = none
  | .erase i,xs => Source xs i
  | .product f _,xs => Source xs (f 0) ∧ Source xs (f 1) ∧ xs (f 2) = none ∧ 0 < value xs (f 0)
  | .difference f _,xs => Source xs (f 0) ∧ Source xs (f 1) ∧ xs (f 2) = none ∧ value xs (f 1) ≤ value xs (f 0)
  | .round f _,xs => Source xs (f 0) ∧ Source xs (f 1) ∧ xs (f 2) = none ∧ 0 < value xs (f 0) ∧ 0 < value xs (f 1)
  | .power f _,xs => Source xs (f 0) ∧ xs (f 1) = none

def transform : Op → Words → Words
  | .constant N i,xs => install xs i N
  | .erase i,xs => Function.update xs i none
  | .product f _,xs => install xs (f 2) (value xs (f 1)*value xs (f 0))
  | .difference f _,xs => install xs (f 2) (value xs (f 0)-value xs (f 1))
  | .round f _,xs => install xs (f 2) (RoundedRowDescriptor.rounded (value xs (f 0)) (value xs (f 1)))
  | .power f _,xs => install xs (f 1) (2^value xs (f 0))

def cost : Op → Words → ℕ
  | .constant N _,_ => RecursiveChildQuotientsConstant.cost N
  | .erase i,xs => 2*(word xs i).length+4
  | .product f _,xs => 53*(value xs (f 1)*value xs (f 0))+28
  | .difference f _,xs => 6*value xs (f 0)+27
  | .round f _,xs => 4096*RoundedRowDescriptor.rounded (value xs (f 0)) (value xs (f 1))
  | .power f _,xs => FixedBasePowerDescriptor.constant 2*2^value xs (f 0)

def code : Op → Sigma (fun q => Program 40 q a)
  | .constant N i => ⟨_,Placement.placed (RecursiveChildQuotientsConstant.program (a := a) N)
      (FiniteReturnStackAt.placement (Fin.castAdd 15 i))⟩
  | .erase i => ⟨_,BinaryDescriptorCleanupList.oneProgram (a := a) (Fin.castAdd 15 i)⟩
  | .product f hf => ⟨_,productProgram (a := a) f hf⟩
  | .difference f hf => ⟨_,differenceProgram (a := a) f hf⟩
  | .round f hf => ⟨_,roundProgram (a := a) f hf⟩
  | .power f hf => ⟨_,powerProgram (a := a) f hf⟩

theorem one (op : Op) (xs : Words) (h : Ready op xs) :
    HoareTime (code (a := a) op).2
      (fun u => u = CompactGadgetReservationHeadersWords.bank xs)
      (fun u => u = CompactGadgetReservationHeadersWords.bank (transform op xs)) (cost op xs) := by
  cases op with
  | constant N i =>
    have ha : Placement.active (FiniteReturnStackAt.placement (Fin.castAdd 15 i))
        (CompactGadgetReservationHeadersWords.bank (a := a) xs) =
        FiniteReturnStack.bank (fun _ => blank) 0 := by
      rw [FiniteReturnStackAt.active_bank]
      simp only [CompactGadgetReservationHeadersWords.bank,CompactGadgetReservationHeadersCore.bank,
        CleanSubbank.bank,Tapes.append,Fin.addCases_left]
      rw [absent_tape xs i h,absent_head xs i h]
    have hr := Placement.hoare_at (RecursiveChildQuotientsConstant.initialize_hoare (a := a) N)
      (FiniteReturnStackAt.placement (Fin.castAdd 15 i))
      (CompactGadgetReservationHeadersWords.bank xs) ha
    refine hr.consequence (fun _ h => h) ?_ (le_refl _)
    rintro u ⟨small,rfl,rfl⟩
    rw [FiniteReturnStackAt.replace_bank,BinaryDescriptorStackRoundtrip.descriptor_encoded]
    rw [CompactGadgetReservationHeadersWords.bank,CompactGadgetReservationHeadersCore.bank,
      CleanSubbank.bank,SharedPlacementAlphabet.setTape_append_left]
    rw [← installs]
    rfl
  | erase i =>
    have ht : (CompactGadgetReservationHeadersWords.bank (a := a) xs).tape (Fin.castAdd 15 i) =
        BinaryDescriptorStack.descriptor (word xs i) := by
      simp only [CompactGadgetReservationHeadersWords.bank,CompactGadgetReservationHeadersCore.bank,
        CleanSubbank.bank,Tapes.append,Fin.addCases_left]
      rw [source_tape xs i h,BinaryDescriptorStackRoundtrip.descriptor_encoded]
    have hh : (CompactGadgetReservationHeadersWords.bank (a := a) xs).head (Fin.castAdd 15 i) = 1 := by
      simpa only [CompactGadgetReservationHeadersWords.bank,CompactGadgetReservationHeadersCore.bank,
        CleanSubbank.bank,Tapes.append,Fin.addCases_left] using source_head (a := a) xs i h
    have hr := BinaryDescriptorCleanupList.one_hoare (Fin.castAdd 15 i)
      (CompactGadgetReservationHeadersWords.bank xs) (word xs i) ht hh
    simpa only [code,transform,cost,CompactGadgetReservationHeadersWords.bank,
      CompactGadgetReservationHeadersCore.bank,CleanSubbank.bank,
      SharedPlacementAlphabet.setTape_append_left,erases] using hr
  | product f hf =>
    rcases h with ⟨hx,hy,hz,hpos⟩
    have hr := CompactGadgetReservationHeadersCore.product (common (a := a) xs) f hf
      (word xs (f 0)) (word xs (f 1)) (value xs (f 1)) (value xs (f 0)) hpos rfl rfl hx.2 hy.2
      (source_tape _ _ hx) (source_head _ _ hx) (source_tape _ _ hy) (source_head _ _ hy)
      (absent_tape _ _ hz) (absent_head _ _ hz)
    simpa only [code,transform,cost,CompactGadgetReservationHeadersWords.bank,installs] using hr
  | difference f hf =>
    rcases h with ⟨hx,hy,hz,hle⟩
    have hr := CompactGadgetReservationHeadersCore.difference (common (a := a) xs) f hf
      (word xs (f 0)) (word xs (f 1)) hle hx.2 hy.2
      (source_tape _ _ hx) (source_head _ _ hx) (source_tape _ _ hy) (source_head _ _ hy)
      (absent_tape _ _ hz) (absent_head _ _ hz)
    simpa only [code,transform,cost,CompactGadgetReservationHeadersWords.bank,installs,value] using hr
  | round f hf =>
    rcases h with ⟨hx,hy,hz,hxpos,hypos⟩
    have hr := CompactGadgetReservationHeadersPowerRound.round (common (a := a) xs) f hf
      (word xs (f 0)) (word xs (f 1)) (value xs (f 0)) (value xs (f 1)) hxpos hypos rfl rfl hx.2 hy.2
      (source_tape _ _ hx) (source_head _ _ hx) (source_tape _ _ hy) (source_head _ _ hy)
      (absent_tape _ _ hz) (absent_head _ _ hz)
    simpa only [code,transform,cost,CompactGadgetReservationHeadersWords.bank,installs] using hr
  | power f hf =>
    rcases h with ⟨hx,hz⟩
    have hr := CompactGadgetReservationHeadersPowerRound.power (common (a := a) xs) f hf
      (word xs (f 0)) (value xs (f 0)) rfl hx.2
      (source_tape _ _ hx) (source_head _ _ hx) (absent_tape _ _ hz) (absent_head _ _ hz)
    simpa only [code,transform,cost,CompactGadgetReservationHeadersWords.bank,installs] using hr

def states : List Op → ℕ
  | [] => 1
  | op::ops => (code (a := a) op).1+states ops
def program : (ops : List Op) → Program 40 (states (a := a) ops) a
  | [] => skip 40 a (by decide)
  | op::ops => seq (code op).2 (program ops)
def execute : List Op → Words → Words
  | [],xs => xs
  | op::ops,xs => execute ops (transform op xs)
def bound : List Op → Words → ℕ
  | [],_ => 0
  | op::ops,xs => cost op xs+1+bound ops (transform op xs)
def ReadyList : List Op → Words → Prop
  | [],_ => True
  | op::ops,xs => Ready op xs ∧ ReadyList ops (transform op xs)

theorem runs (ops : List Op) (xs : Words) (h : ReadyList ops xs) :
    HoareTime (program (a := a) ops)
      (fun u => u = CompactGadgetReservationHeadersWords.bank xs)
      (fun u => u = CompactGadgetReservationHeadersWords.bank (execute ops xs)) (bound ops xs) := by
  induction ops generalizing xs with
  | nil => exact skip_hoare (by decide) _
  | cons op ops ih => exact (one op xs h.1).seq (ih _ h.2)

end
end IntegerMultBounds.Machine.CompactGadgetReservationHeadersOps
