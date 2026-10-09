import IntegerMultBounds.Machine.BinaryDescriptorCleanupList
import IntegerMultBounds.Machine.CompactGadgetReservationHeadersCarvedVolume

/-! Paid physical erasure of the twelve generated early headers, with exact framing. -/
namespace IntegerMultBounds.Machine.PackedEarlyHeaderCleanup
noncomputable section
open CompactGadgetReservationShape
open CompactGadgetReservationHeadersCarvedData
variable {t a : ℕ}

def slots : Fin 12 → Fin 25 := ![5,7,8,9,10,11,12,13,14,21,23,24]
theorem slots_injective : Function.Injective slots := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [slots,Fin.ext_iff]

def ports (focus : Fin 12 → Fin t) := (List.finRange 12).map focus

theorem ports_nodup (focus : Fin 12 → Fin t) (hf : Function.Injective focus) :
    (ports focus).Nodup := List.Nodup.map hf (List.nodup_finRange 12)

def program (ht : 0 < t) (focus : Fin 12 → Fin t) :=
  BinaryDescriptorCleanupList.program (a := a) ht (ports focus)

theorem runs (ht : 0 < t) (focus : Fin 12 → Fin t) (hf : Function.Injective focus)
    (xs : Fin t → List Bool) (v : Tapes t a) (V : ℕ) (hV : 0 < V)
    (hs : ∀ i, v.head (focus i)=1 ∧ v.tape (focus i)=BinaryDescriptorStack.descriptor (xs (focus i)))
    (hc : ∀ i, GrowingCounterData.Canonical (xs (focus i)))
    (hv : ∀ i, Counter.value (xs (focus i)) ≤ V) :
    HoareTime (program ht focus) (fun w => w=v)
      (fun w => w=BinaryDescriptorCleanupList.cleared (ports focus) v) (108*V) := by
  have h := BinaryDescriptorCleanupList.cleanup_hoare ht (ports focus) (ports_nodup focus hf) xs v (by
    intro j hj
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hj
    exact hs i)
  apply h.consequence (fun _ h => h) (fun _ h => h)
  have hcst := BinaryDescriptorCleanupList.cost_le (ports focus) xs (2*V) (by
    intro j hj
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hj
    exact CompactGadgetReservationHeadersCost.length_bound _ (hc i) V (hv i) hV)
  simp only [ports,List.length_map,List.length_finRange] at hcst
  change BinaryDescriptorCleanupList.cost ((List.finRange 12).map focus) xs ≤ 108*V
  nlinarith

theorem restored (focus : Fin 12 → Fin t) (hf : Function.Injective focus)
    (initial ready : Tapes t a)
    (hz : ∀ i, initial.head (focus i)=0 ∧ initial.tape (focus i)=fun _ => blank)
    (hframe : ∀ j, j ∉ ports focus → ready.head j=initial.head j ∧ ready.tape j=initial.tape j) :
    BinaryDescriptorCleanupList.cleared (ports focus) ready=initial := by
  change Tapes.mk _ _ = Tapes.mk initial.head initial.tape
  apply congrArg₂ Tapes.mk
  · funext j
    by_cases hj : j ∈ ports focus
    · obtain ⟨i,_,rfl⟩ := List.mem_map.mp hj
      exact (BinaryDescriptorCleanupList.cleared_slot _ (ports_nodup focus hf) ready _
        (List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩)).1.trans (hz i).1.symm
    · exact (BinaryDescriptorCleanupList.cleared_frame _ ready j hj).1.trans (hframe j hj).1
  · funext j
    by_cases hj : j ∈ ports focus
    · obtain ⟨i,_,rfl⟩ := List.mem_map.mp hj
      exact (BinaryDescriptorCleanupList.cleared_slot _ (ports_nodup focus hf) ready _
        (List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩)).2.trans (hz i).2.symm
    · exact (BinaryDescriptorCleanupList.cleared_frame _ ready j hj).2.trans (hframe j hj).2

def headerFocus (t : ℕ) (i : Fin 12) : Fin ((25+t)+15) :=
  Fin.castAdd 15 (Fin.castAdd t (slots i))
theorem headerFocus_injective (t : ℕ) : Function.Injective (headerFocus t) := by
  intro i j h
  apply slots_injective
  apply Fin.ext
  have hh := congrArg Fin.val h
  exact hh

def values (s : Shape) (rows nq nb : ℕ) : Fin 12 → ℕ :=
  ![rows,2^(s.H-nq),2^(s.H-nq)*2^nb*gap s nb .control,rows,nb,
    gap s nq .temp,suffix s nq,nq,gap s nb .control,rows*2^s.H,
    gap s nb .control,suffix s nb]

theorem values_bound (s : Shape) (rows nq nb : ℕ) (hr : 0 < rows)
    (hp : 0 < s.payload) (hq : nq ≤ s.H) (hb : nb ≤ s.H) :
    ∀ i, values s rows nq nb i ≤ rows*s.recordWidth := by
  have hrec : s.recordWidth ≤ rows*s.recordWidth := Nat.le_mul_of_pos_left _ hr
  have hpw : 2^s.bits ≤ s.recordWidth := Nat.le_mul_of_pos_right _ hp
  have hH : s.H ≤ s.bits := by unfold Shape.bits; omega
  have hpow (k : ℕ) (hk : k ≤ s.bits) : 2^k ≤ rows*s.recordWidth :=
    (Nat.pow_le_pow_right (by decide : 0 < 2) hk).trans (hpw.trans hrec)
  have hbits : s.bits ≤ rows*s.recordWidth :=
    (Nat.lt_pow_self (n := s.bits) (by decide : 1 < 2)).le.trans (hpw.trans hrec)
  have hgap (w : ℕ) (hw : w ≤ s.H) (f : Front) : gap s w f ≤ rows*s.recordWidth := by
    apply hpow
    cases f <;> simp only [gapBits,Shape.bits] <;> omega
  have hsuf (w : ℕ) (hw : w ≤ s.H) : suffix s w ≤ rows*s.recordWidth := by
    have he : afterBits s w ≤ s.bits := by unfold afterBits Shape.bits; omega
    exact (Nat.mul_le_mul_right s.payload
      (Nat.pow_le_pow_right (by decide : 0 < 2) he)).trans hrec
  have hm : 2^(s.H-nq)*2^nb*gap s nb .control ≤ rows*s.recordWidth := by
    unfold gap
    rw [← pow_add,← pow_add]
    apply hpow
    simp only [gapBits,Shape.bits]
    omega
  have hrpow : rows*2^s.H ≤ rows*s.recordWidth :=
    Nat.mul_le_mul_left rows ((Nat.pow_le_pow_right (by decide : 0 < 2) hH).trans hpw)
  have hr' : rows ≤ rows*s.recordWidth := by
    have hp' : 0 < s.recordWidth := by unfold Shape.recordWidth; positivity
    exact Nat.le_mul_of_pos_right _ hp'
  intro i
  fin_cases i
  all_goals dsimp only [values]
  all_goals first
    | exact hr'
    | exact hpow _ (by omega)
    | exact hm
    | exact hb.trans (hH.trans hbits)
    | exact hq.trans (hH.trans hbits)
    | exact hgap nq hq .temp
    | exact hgap nb hb .control
    | exact hsuf nq hq
    | exact hsuf nb hb
    | exact hrpow

theorem header_original_not_selected (t : ℕ) (i : Fin 25) (hi : i.val ≤ 4 ∨ i.val=6) :
    Fin.castAdd 15 (Fin.castAdd t i) ∉ ports (headerFocus t) := by
  intro hm
  obtain ⟨j,_,he⟩ := List.mem_map.mp hm
  have hv := congrArg Fin.val he
  fin_cases j <;> dsimp [headerFocus,slots] at hv <;> omega

theorem runs_headers (t : ℕ) (s : Shape) (rows nq nb : ℕ)
    (hr : 0 < rows) (hp : 0 < s.payload) (hq : nq ≤ s.H) (hb : nb ≤ s.H)
    (xs : Fin ((25+t)+15) → List Bool) (initial ready : Tapes ((25+t)+15) a)
    (hs : ∀ i, ready.head (headerFocus t i)=1 ∧ ready.tape (headerFocus t i)=
      BinaryDescriptorStack.descriptor (xs (headerFocus t i)))
    (hc : ∀ i, GrowingCounterData.Canonical (xs (headerFocus t i)))
    (hv : ∀ i, Counter.value (xs (headerFocus t i))=values s rows nq nb i)
    (hz : ∀ i, initial.head (headerFocus t i)=0 ∧ initial.tape (headerFocus t i)=fun _ => blank)
    (hframe : ∀ j, j ∉ ports (headerFocus t) →
      ready.head j=initial.head j ∧ ready.tape j=initial.tape j) :
    HoareTime (program (by omega : 0 < (25+t)+15) (headerFocus t))
      (fun w => w=ready) (fun w => w=initial) (108*(rows*s.recordWidth)) := by
  have hV : 0 < rows*s.recordWidth := by unfold Shape.recordWidth; positivity
  have h := runs (by omega) (headerFocus t) (headerFocus_injective t) xs ready _ hV hs hc (by
    intro i
    rw [hv i]
    exact values_bound s rows nq nb hr hp hq hb i)
  rw [restored (headerFocus t) (headerFocus_injective t) initial ready hz hframe] at h
  exact h

end
end IntegerMultBounds.Machine.PackedEarlyHeaderCleanup
