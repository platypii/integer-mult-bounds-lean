import IntegerMultBounds.Machine.UnitPhasePolynomialStreamLoop
import IntegerMultBounds.Machine.UnitPhaseStreamAddressReset

/-! Physically close a polynomial phase traversal: erase raw address/live
counter, generated full-address count, and polynomial multiplicity. All
inner and outer loop work is already blank; coefficient streams persist. -/
namespace IntegerMultBounds.Machine.UnitPhasePolynomialStreamClean
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open ActivePrefixStageHeadersData (Order)
open DelimitedRadixRecord (Context)
open CountedLoopReuseAlphabet (binary)
open BinaryAddressTableData (row)
variable {s : Shape}

def address := extend UnitPhaseStreamAddressReset.program 5
def slots : List (Fin 65) := [59,60]
def descriptors := BinaryDescriptorCleanupList.program (a := 2) (by decide : 0<65) slots
def program := seq address descriptors

def base (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (m : ℕ)
    (ws : List (ZMod 4)) (ctx : ℕ → ℕ → Context 2) (z : Tapes 4 2) (R N : ℕ) :=
  (SparsePhaseFlagsCaller.input order v rows axis (row s.bits (N-1)) (SharedBank.empty 6 2)).append
    (UnitPhasePolynomialStreamLoop.tails order v rows axis m ws ctx z R N)
def extra (R : ℕ) := (UnitPhasePolynomialRecord.multiplicity R).append (SharedBank.empty 4 2)
def afterAddress (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (m : ℕ)
    (ws : List (ZMod 4)) (ctx : ℕ → ℕ → Context 2) (z : Tapes 4 2) (R N : ℕ) :=
  (UnitPhaseStreamAddressReset.output (base order v rows axis m ws ctx z R N) (row s.bits (N-1))).append (extra R)
def output (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (m : ℕ)
    (ws : List (ZMod 4)) (ctx : ℕ → ℕ → Context 2) (z : Tapes 4 2) (R N : ℕ) :=
  BinaryDescriptorCleanupList.cleared slots (afterAddress order v rows axis m ws ctx z R N)
def words (N R : ℕ) (i : Fin 65) :=
  if i=59 then RecursiveChildQuotientsConstant.bits N else RecursiveChildQuotientsConstant.bits R

theorem reassociate (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (m : ℕ)
    (ws : List (ZMod 4)) (ctx : ℕ → ℕ → Context 2) (z : Tapes 4 2) (R N : ℕ) :
    CountedLoopHeaderClean.bank (UnitPhasePolynomialStreamLoop.state order v rows axis m ws ctx z R N)=
      (base order v rows axis m ws ctx z R N).append (extra R) := by
  apply congrArg₂ Tapes.mk <;> funext j <;> fin_cases j <;> rfl

theorem runs (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (m : ℕ)
    (ws : List (ZMod 4)) (ctx : ℕ → ℕ → Context 2) (z : Tapes 4 2) (R N : ℕ)
    (hc : z.tape 1=binary (row s.bits 0) ∧ z.head 1=1)
    (hn : z.tape 3=RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits N) ∧ z.head 3=1) :
    HoareTime program
      (fun t => t=CountedLoopHeaderClean.bank (UnitPhasePolynomialStreamLoop.state order v rows axis m ws ctx z R N))
      (fun t => t=output order v rows axis m ws ctx z R N)
      (5*s.bits+11+BinaryDescriptorCleanupList.cost slots (words N R)+1) := by
  have hcount := UnitPhasePolynomialStreamLoop.count order v rows axis m ws ctx z R N
  have hcounter := UnitPhasePolynomialStreamLoop.counter order v rows axis m ws ctx z R hc N
  have h0 := UnitPhaseStreamAddressReset.runs (base order v rows axis m ws ctx z R N)
    (row s.bits (N-1)) (row s.bits N) ⟨rfl,rfl⟩ ⟨rfl,rfl⟩ hcounter
  simp only [BinaryAddressTableData.row_length] at h0
  have he := hoare_extend_eq h0 (extra R)
  have hd : ∀ i ∈ slots,(afterAddress order v rows axis m ws ctx z R N).head i=1 ∧
      (afterAddress order v rows axis m ws ctx z R N).tape i=BinaryDescriptorStack.descriptor (words N R i) := by
    intro i hi
    simp only [slots,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl
    · constructor
      · change (UnitPhasePolynomialStreamLoop.tails order v rows axis m ws ctx z R N).head 3=1
        rw [hcount.2,hn.2]
      · change (UnitPhasePolynomialStreamLoop.tails order v rows axis m ws ctx z R N).tape 3=_
        rw [hcount.1,hn.1]
        exact BinaryDescriptorStackRoundtrip.descriptor_encoded _ |>.symm
    · exact ⟨rfl,BinaryDescriptorStackRoundtrip.descriptor_encoded _ |>.symm⟩
  have h1 := BinaryDescriptorCleanupList.cleanup_hoare (a := 2) (by decide : 0<65)
    slots (by decide) (words N R) (afterAddress order v rows axis m ws ctx z R N) hd
  rw [← reassociate] at he
  exact (he.seq h1).consequence (fun _ h => h) (fun _ h => h) (by omega)

end
end IntegerMultBounds.Machine.UnitPhasePolynomialStreamClean
