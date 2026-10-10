import IntegerMultBounds.Machine.CompactComplexScalarLifecycleGrid

/-! Actual scalar lifecycle outputs are genuine native polynomial row streams
for the next physical event. Flattening and unflattening only rename positions;
no serialization conversion, copying or prepared source equality is required. -/
namespace IntegerMultBounds.Machine.CompactComplexScalarNativeEndpoint
noncomputable section
open ButterflyStreamData (Coefficient)
open CompactComplexScalarRowBlock (wireCount)
open CompactComplexScalarIntegerRows (RowIndex)
open CompactComplexScalarCountLifecycle (output scalarOutput counted liveProof storedHeader header_ne_live)
open CompactComplexScalarRolePorts (roleIndex)
open ActivePrefixStageNativePolynomial (flattenArray)
variable {s : ℕ}
attribute [local irreducible] Networks.ComplexRank25.program CompactComplexScalarIntegerRows.gates

def unflatten {X : Type*} {N R : ℕ} (data : Fin (N*R) → X) (i : Fin N) (j : Fin R) : X :=
  data (finProdFinEquiv (i,j))

theorem flatten_unflatten {X : Type*} {N R : ℕ} (data : Fin (N*R) → X) :
    flattenArray (unflatten data)=data := by
  funext i
  change data (finProdFinEquiv (finProdFinEquiv.symm i))=data i
  rw [Equiv.apply_symm_apply]

theorem unflatten_flatten {X : Type*} {N R : ℕ} (xs : Fin N → Fin R → X) :
    unflatten (flattenArray xs)=xs := by
  funext i j
  simp only [flattenArray,unflatten,Equiv.symm_apply_apply]

theorem unflatten_width {N R w : ℕ} (data : Fin (N*R) → Coefficient)
    (hw : ∀ i,(data i).1.length=w ∧ (data i).2.length=w) :
    ∀ i j,(unflatten data i j).1.length=w ∧ (unflatten data i j).2.length=w :=
  fun i j => hw (finProdFinEquiv (i,j))

/-- Count erasure preserves the literal rewritten permanent role stream. -/
theorem output_source {N : ℕ} (hs : 7<s) (header : Fin s) (hh : header.val≠7)
    (v : Tapes (CompactComplexScalarCountLifecycle.publicTapes s) 2)
    (data : Fin wireCount → Fin N → Coefficient) (d : ℕ) (a : Fin wireCount) :
    (output hs header v data d).head
      (CompactComplexNativeRoleBridge.roleSlot (s:=s+43) (roleIndex a))=0 ∧
    (output hs header v data d).tape
      (CompactComplexNativeRoleBridge.roleSlot (s:=s+43) (roleIndex a))=
        ButterflyStreamData.full (fun _ => blank) 0 (data a) := by
  have h := (CompactComplexScalarRolePorts.output_ready (liveProof hs) (storedHeader header)
    (header_ne_live header hh) (counted header v N) data d).1 a
  rw [CompactComplexScalarRolePorts.source_port] at h
  have he := CompactComplexScalarCountLifecycle.output_outside_count hs header v data d
    (CompactComplexNativeRoleBridge.roleSlot (s:=s+43) (roleIndex a))
    (CompactComplexScalarCountRootBank.role_ne_count header (roleIndex a))
  exact ⟨he.1.trans h.1,he.2.trans h.2⟩

/-- The native descriptors, geometric stacks, target stack and immutable
scalar descriptor are unchanged wherever they lie outside the actual role,
count and live-denominator ports. -/
theorem output_frame {N : ℕ} (hs : 7<s) (header : Fin s)
    (v : Tapes (CompactComplexScalarCountLifecycle.publicTapes s) 2)
    (data : Fin wireCount → Fin N → Coefficient) (d : ℕ)
    (i : Fin (CompactComplexScalarCountLifecycle.publicTapes s))
    (hc : i≠CompactComplexScalarCountRootBank.countSlot header)
    (hl : i≠CompactComplexScalarCountRootBank.countSlot ⟨7,hs⟩)
    (hr : ∀ a,CompactComplexNativeRoleBridge.roleSlot (s:=s+43) (roleIndex a)≠i) :
    (output hs header v data d).head i=v.head i ∧
      (output hs header v data d).tape i=v.tape i := by
  have hi : ¬∃ j,CompactComplexScalarRolePorts.common (liveProof hs) (storedHeader header) j=i := by
    rintro ⟨j,hj⟩
    induction j using Fin.addCases with
    | left a =>
      rw [CompactComplexScalarRolePorts.source_port] at hj
      exact hr a hj
    | right b =>
      fin_cases b
      · change CompactComplexScalarRolePorts.common (liveProof hs) (storedHeader header)
          (Fin.natAdd wireCount (0 : Fin 2))=i at hj
        rw [CompactComplexScalarRolePorts.count_port] at hj
        change CompactComplexScalarCountRootBank.countSlot header=i at hj
        exact hc hj.symm
      · change CompactComplexScalarRolePorts.common (liveProof hs) (storedHeader header)
          (Fin.natAdd wireCount (1 : Fin 2))=i at hj
        rw [CompactComplexScalarRolePorts.live_port] at hj
        change CompactComplexScalarCountRootBank.countSlot ⟨7,hs⟩=i at hj
        exact hl hj.symm
  have hscalar := CompactComplexScalarRolePorts.output_outside (liveProof hs) (storedHeader header)
    (counted header v N) data d i hi
  have hsetup := CompactComplexScalarCountRootBank.output_frame header v N i hc
  have hcleanup := CompactComplexScalarCountLifecycle.output_outside_count hs header v data d i hc
  exact ⟨hcleanup.1.trans (hscalar.1.trans hsetup.1),
    hcleanup.2.trans (hscalar.2.trans hsetup.2)⟩

/-- The next native operation receives the actual emitted polynomial rows,
with their original geometric row count and exact field width. -/
theorem output_native {sh : CompactGadgetReservationShape.Shape} {R w : ℕ}
    (inp : ActivePrefixStageFullData.Inputs sh) (hs : 7<s) (header : Fin s) (hh : header.val≠7)
    (v : Tapes (CompactComplexScalarCountLifecycle.publicTapes s) 2)
    (data : Fin wireCount → Fin (ActivePrefixStageTripleWords.count inp*R) → Coefficient)
    (hw : ∀ a i,(data a i).1.length=w ∧ (data a i).2.length=w)
    (d : ℕ) (a : Fin wireCount) :
    (output hs header v data d).head
      (CompactComplexNativeRoleBridge.roleSlot (s:=s+43) (roleIndex a))=0 ∧
    (output hs header v data d).tape
      (CompactComplexNativeRoleBridge.roleSlot (s:=s+43) (roleIndex a))=
        SymbolTripleClean.word (List.ofFn (ActivePrefixStageNativeRows.flat
          (ActivePrefixStageNativePolynomial.rows inp (unflatten (data a))
            (unflatten_width (data a) (hw a))))) := by
  have h := output_source hs header hh v data d a
  have hword := CompactComplexScalarRolePorts.native_word inp (unflatten (data a))
    (unflatten_width (data a) (hw a))
  rw [flatten_unflatten] at hword
  exact ⟨h.1,h.2.trans hword⟩

/-- Genuine native arrays emitted by the actual scalar schedule. -/
def executed {N R : ℕ} (ops : List RowIndex)
    (xs : Fin wireCount → Fin N → Fin R → Coefficient) :=
  fun a => unflatten
    (CompactComplexScalarPolynomialSequence.execute ops (fun j => flattenArray (xs j)) a)

theorem executed_flat {N R : ℕ} (ops : List RowIndex)
    (xs : Fin wireCount → Fin N → Fin R → Coefficient) :
    (fun a => flattenArray (executed ops xs a))=
      CompactComplexScalarPolynomialSequence.execute ops (fun a => flattenArray (xs a)) := by
  funext a
  exact flatten_unflatten _

theorem executed_width {N R w : ℕ} (ops : List RowIndex)
    (xs : Fin wireCount → Fin N → Fin R → Coefficient)
    (hw : ∀ a i j,(xs a i j).1.length=w ∧ (xs a i j).2.length=w) :
    ∀ a i j,(executed ops xs a i j).1.length=w ∧ (executed ops xs a i j).2.length=w := by
  have hf : ∀ a i,(flattenArray (xs a) i).1.length=w ∧ (flattenArray (xs a) i).2.length=w := by
    intro a i
    exact hw a (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
  have he := CompactComplexScalarLifecycleGrid.output_width ops
    (fun a => flattenArray (xs a)) w hf
  intro a i j
  exact he a (finProdFinEquiv (i,j))

/-- The literal executed endpoint is the next native caller's original row
format at the same retained dimensions and polynomial field widths. -/
theorem output_executed_native {sh : CompactGadgetReservationShape.Shape} {R w : ℕ}
    (inp : ActivePrefixStageFullData.Inputs sh) (hs : 7<s) (header : Fin s) (hh : header.val≠7)
    (v : Tapes (CompactComplexScalarCountLifecycle.publicTapes s) 2) (ops : List RowIndex)
    (xs : Fin wireCount → Fin (ActivePrefixStageTripleWords.count inp) → Fin R → Coefficient)
    (hw : ∀ a i j,(xs a i j).1.length=w ∧ (xs a i j).2.length=w)
    (d : ℕ) (a : Fin wireCount) :
    let data := CompactComplexScalarPolynomialSequence.execute ops (fun a => flattenArray (xs a))
    (output hs header v data (d+ops.length)).head
      (CompactComplexNativeRoleBridge.roleSlot (s:=s+43) (roleIndex a))=0 ∧
    (output hs header v data (d+ops.length)).tape
      (CompactComplexNativeRoleBridge.roleSlot (s:=s+43) (roleIndex a))=
        SymbolTripleClean.word (List.ofFn (ActivePrefixStageNativeRows.flat
          (ActivePrefixStageNativePolynomial.rows inp (executed ops xs a)
            (executed_width ops xs hw a)))) := by
  dsimp only
  have h := output_source hs header hh v
    (CompactComplexScalarPolynomialSequence.execute ops (fun a => flattenArray (xs a)))
    (d+ops.length) a
  have hword := CompactComplexScalarRolePorts.native_word inp (executed ops xs a)
    (executed_width ops xs hw a)
  rw [congrFun (executed_flat ops xs) a] at hword
  exact ⟨h.1,h.2.trans hword⟩

end
end IntegerMultBounds.Machine.CompactComplexScalarNativeEndpoint
