import IntegerMultBounds.Machine.CompactGadgetReservationHeadersDivision
import IntegerMultBounds.Machine.CompactGadgetReservationHeadersPowerRound
import IntegerMultBounds.Machine.CompactRowPaddingRound
import IntegerMultBounds.Machine.RecursiveRowsQuotient

/-! Original row count to the padded per-role row count. The static role count
is physically installed, the rounded row count is physically divided, and all
work descriptors are erased. The original row tape and the frame survive. -/
namespace IntegerMultBounds.Machine.CompactGadgetReservationHeadersRows
noncomputable section
open CompactGadgetReservationHeadersCore
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)
variable {t a : ℕ}

def writeProgram (c : ℕ) (i : Fin t) := Placement.placed
  (RecursiveChildQuotientsConstant.program (a := a) c)
  (FiniteReturnStackAt.placement (Fin.castAdd 15 i))
def eraseProgram (i : Fin t) := BinaryDescriptorCleanupList.oneProgram (a := a) (Fin.castAdd 15 i)

theorem writes (v : Tapes t a) (c : ℕ) (i : Fin t)
    (ht : v.tape i = fun _ => blank) (hh : v.head i = 0) :
    HoareTime (writeProgram (a := a) c i) (fun u => u = bank v)
      (fun u => u = bank (setTape v i (RadixZeroFill.encodedBinary (bits c)) 1))
      (RecursiveChildQuotientsConstant.cost c) := by
  have ha : Placement.active (FiniteReturnStackAt.placement (Fin.castAdd 15 i)) (bank v) =
      FiniteReturnStack.bank (fun _ => blank) 0 := by
    rw [FiniteReturnStackAt.active_bank]
    simp only [bank,CleanSubbank.bank,Tapes.append,Fin.addCases_left,ht,hh]
  have hr := Placement.hoare_at (RecursiveChildQuotientsConstant.initialize_hoare (a := a) c)
    (FiniteReturnStackAt.placement (Fin.castAdd 15 i)) (bank v) ha
  refine hr.consequence (fun _ h => h) ?_ (le_refl _)
  rintro u ⟨small,rfl,rfl⟩
  rw [FiniteReturnStackAt.replace_bank,BinaryDescriptorStackRoundtrip.descriptor_encoded]
  exact SharedPlacementAlphabet.setTape_append_left _ _ _ _ _

theorem erases (v : Tapes t a) (i : Fin t) (xs : List Bool)
    (ht : v.tape i = RadixZeroFill.encodedBinary xs) (hh : v.head i = 1) :
    HoareTime (eraseProgram (a := a) i) (fun u => u = bank v)
      (fun u => u = bank (setTape v i (fun _ => blank) 0)) (2*xs.length+4) := by
  have ht' : (bank v).tape (Fin.castAdd 15 i) = BinaryDescriptorStack.descriptor xs := by
    simpa only [bank,CleanSubbank.bank,Tapes.append,Fin.addCases_left,
      BinaryDescriptorStackRoundtrip.descriptor_encoded] using ht
  have hh' : (bank v).head (Fin.castAdd 15 i) = 1 := by
    simpa only [bank,CleanSubbank.bank,Tapes.append,Fin.addCases_left] using hh
  simpa only [eraseProgram,bank,CleanSubbank.bank,SharedPlacementAlphabet.setTape_append_left]
    using BinaryDescriptorCleanupList.one_hoare (Fin.castAdd 15 i) (bank v) xs ht' hh'

def roundFocus (f : Fin 4 → Fin t) : Fin 3 → Fin t := fun i => f (![0,1,2] i)
def divideFocus (f : Fin 4 → Fin t) : Fin 3 → Fin t := fun i => f (![2,1,3] i)
theorem roundFocus_injective (f : Fin 4 → Fin t) (hf : Function.Injective f) :
    Function.Injective (roundFocus f) := by
  intro i j h
  have hh := hf h
  fin_cases i <;> fin_cases j <;> simp_all [roundFocus]
theorem divideFocus_injective (f : Fin 4 → Fin t) (hf : Function.Injective f) :
    Function.Injective (divideFocus f) := by
  intro i j h
  have hh := hf h
  fin_cases i <;> fin_cases j <;> simp_all [divideFocus]

def program (c : ℕ) (f : Fin 4 → Fin t) (hf : Function.Injective f) :=
  seq (seq (seq (seq (writeProgram (a := a) c (f 1))
    (CompactGadgetReservationHeadersPowerRound.roundProgram (roundFocus f) (roundFocus_injective f hf)))
    (CompactGadgetReservationHeadersDivision.program (divideFocus f) (divideFocus_injective f hf)))
    (eraseProgram (f 1))) (eraseProgram (f 2))
def cost (r c : ℕ) := RecursiveChildQuotientsConstant.cost c +
    4096*RoundedRowDescriptor.rounded r c +
    BinaryDescriptorDivision.cost (bits (RoundedRowDescriptor.rounded r c)) (bits c) +
    (2*(bits c).length+4) + (2*(bits (RoundedRowDescriptor.rounded r c)).length+4) + 4

theorem constructs (v : Tapes t a) (c : ℕ) (f : Fin 4 → Fin t) (hf : Function.Injective f)
    (rs : List Bool) (r : ℕ) (hr : Counter.value rs = r) (cr : GrowingCounterData.Canonical rs)
    (hR : 0 < r) (hc : 0 < c)
    (ht : v.tape (f 0) = RadixZeroFill.encodedBinary rs) (hh : v.head (f 0) = 1)
    (hblank : ∀ i : Fin 4, i ≠ 0 → v.tape (f i) = (fun _ => blank) ∧ v.head (f i) = 0) :
    HoareTime (program (a := a) c f hf) (fun u => u = bank v)
      (fun u => u = bank (setTape v (f 3)
        (RadixZeroFill.encodedBinary (bits (IntegerMultBounds.Compact.Layout.paddedRows r c / c))) 1))
      (cost r c) := by
  have heq (i j : Fin 4) : f i = f j ↔ i = j := ⟨fun h => hf h,congrArg f⟩
  let R := RoundedRowDescriptor.rounded r c
  let v1 := setTape v (f 1) (RadixZeroFill.encodedBinary (bits c)) 1
  let v2 := setTape v1 (f 2) (RadixZeroFill.encodedBinary (bits R)) 1
  let v3 := setTape v2 (f 3) (RadixZeroFill.encodedBinary (bits (R/c))) 1
  let v4 := setTape v3 (f 1) (fun _ => blank) 0
  have h1 := writes v c (f 1) (hblank 1 (by decide)).1 (hblank 1 (by decide)).2
  have h2 : HoareTime
      (CompactGadgetReservationHeadersPowerRound.roundProgram (a := a) (roundFocus f) (roundFocus_injective f hf))
      (fun u => u = bank v1) (fun u => u = bank v2) (4096*R) := by
    apply CompactGadgetReservationHeadersPowerRound.round v1 (roundFocus f) (roundFocus_injective f hf)
      rs (bits c) r c hR hc hr (RecursiveChildQuotientsConstant.bits_value c) cr
      (RecursiveChildQuotientsConstant.bits_canonical c)
    all_goals simp [v1,roundFocus,setTape,ht,hh,heq,hblank 2 (by decide)]
  have h3 : HoareTime
      (CompactGadgetReservationHeadersDivision.program (a := a) (divideFocus f) (divideFocus_injective f hf))
      (fun u => u = bank v2) (fun u => u = bank v3)
      (BinaryDescriptorDivision.cost (bits R) (bits c)) := by
    have hd : 0 < Counter.value (bits c) := by simpa only [RecursiveChildQuotientsConstant.bits_value] using hc
    have hz := CompactGadgetReservationHeadersDivision.divides v2 (divideFocus f) (divideFocus_injective f hf)
      (bits R) (bits c) hd
    simp only [RecursiveChildQuotientsConstant.bits_value] at hz
    apply hz
    all_goals simp [v2,v1,divideFocus,setTape,heq,hblank 3 (by decide)]
  have h4 : HoareTime (eraseProgram (a := a) (f 1)) (fun u => u = bank v3)
      (fun u => u = bank v4) (2*(bits c).length+4) := by
    apply erases v3 (f 1) (bits c)
    all_goals simp [v3,v2,v1,setTape,heq]
  have h5 := erases v4 (f 2) (bits R)
    (by simp [v4,v3,v2,setTape,heq])
    (by simp [v4,v3,v2,setTape,heq])
  have hfinal : setTape v4 (f 2) (fun _ => blank) 0 =
      setTape v (f 3) (RadixZeroFill.encodedBinary (bits (R/c))) 1 := by
    apply congrArg₂ Tapes.mk <;> funext i
    all_goals by_cases h3 : i = f 3
    all_goals first
      | (subst i; simp [v4,v3,v2,v1,setTape,heq])
      | skip
    all_goals by_cases h2 : i = f 2
    all_goals first
      | (subst i; simp [v4,v3,v2,v1,setTape,heq,hblank 2 (by decide)])
      | skip
    all_goals by_cases h1 : i = f 1
    all_goals first
      | (subst i; simp [v4,v3,v2,v1,setTape,heq,hblank 1 (by decide)])
      | simp [v4,v3,v2,v1,setTape,h1,h2,h3]
  have h := (((h1.seq h2).seq h3).seq h4).seq h5
  rw [hfinal] at h
  have he : R = IntegerMultBounds.Compact.Layout.paddedRows r c := CompactRowPaddingRound.rounded_eq r c hR hc
  rw [he] at h
  exact h.consequence (fun _ h => h) (fun _ h => h) (by
    unfold cost
    rw [CompactRowPaddingRound.rounded_eq r c hR hc]
    omega)

def constant (c : ℕ) := (RecursiveRowsQuotient.constant c+4106)*(c+1)

theorem cost_linear (r c : ℕ) (hr : 0 < r) (hc : 0 < c) :
    cost r c ≤ constant c*r := by
  let R := RoundedRowDescriptor.rounded r c
  have hR : 0 < R := lt_of_lt_of_le hr (RoundedRowDescriptor.rows_le r c hr hc)
  have hd := RecursiveRowsQuotient.cost_linear c (fun _ => bits R) R hR
    (RecursiveChildQuotientsConstant.bits_canonical R) (by simp [RecursiveChildQuotientsConstant.bits_value])
  have hlen := GrowingCounterData.canonical_width (bits R) (RecursiveChildQuotientsConstant.bits_canonical R)
  rw [RecursiveChildQuotientsConstant.bits_value] at hlen
  have hlog := Nat.log2_le_self R
  have hcost : cost r c ≤ (RecursiveRowsQuotient.constant c+4106)*R := by
    unfold cost RecursiveChildQuotientsConstant.cost RecursiveRowsQuotient.cost at *
    change BinaryDescriptorDivision.cost (bits R) (bits c)+5*(bits c).length+12 ≤
      RecursiveRowsQuotient.constant c*R at hd
    dsimp only [R] at *
    nlinarith
  have hbound : R ≤ (c+1)*r := by
    have hlt := RoundedRowDescriptor.rounded_lt r c hr
    dsimp only [R]
    nlinarith
  exact hcost.trans (by unfold constant; nlinarith)

end
end IntegerMultBounds.Machine.CompactGadgetReservationHeadersRows
