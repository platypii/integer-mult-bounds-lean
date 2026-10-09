import IntegerMultBounds.Machine.ActiveRepairLayoutKeysFields

/-! The physically generated original-layout early key is the membership
flag and complete destination rank of the concrete global permutations. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutKeysEarly
noncomputable section
attribute [local instance] Classical.propDecidable
open CompactGadgetReservationShape CompactActiveTargetLayout
open ActiveRepairRankHeadersEndpoint ActiveRepairLayoutPermutationFiber
open ActiveRepairEarlyKeyOriginalData ActiveRepairEarlyKeyOriginalValid
open IntegerMultBounds.Compact IntegerMultBounds.Compact.PowerTwo

variable (d : Data) (h : Valid d) (s : Shape) (before after rows offset width rowBits : ℕ)
variable (he : d.geom=geometry s (d.n*d.b) (d.n*d.q) before after offset width rowBits)
variable (hw : d.n*d.b≤s.H) (ha : before+d.n*d.q+after=s.active*s.chunk) (hp : s.payload=1)
variable (hf : sourceFits d.side before after offset width)
variable (x : Address s (d.n*d.b) (d.n*d.q) before after rows)
variable (hc : Counter.value d.cs=(index s (d.n*d.b) (d.n*d.q) before after rows hw ha x).val)

include he hw ha hp hf hc in
theorem fields :
    d.key.V=BinaryAddressTableData.row (d.n*d.q) x.target.val ∧
    d.key.T=BinaryAddressTableData.row (d.n*d.b) x.t.val ∧
    d.key.U=BinaryAddressTableData.row (d.n*d.b) x.u.val ∧
    d.key.Z=controlWord before after d.q d.rho d.n offset width d.side (x.activeBefore,x.activeAfter) := by
  obtain ⟨hv,ht,hu,hsource⟩ := ActiveRepairLayoutKeysFields.parsed_fields s (d.n*d.b) (d.n*d.q)
    before after rows offset width rowBits d.side hw ha hp hf x d.cs hc
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [ActiveRepairEarlyKeyData.Data.V,Data.key,he] using hv
  · simpa only [ActiveRepairEarlyKeyData.Data.T,Data.key,he] using ht
  · simpa only [ActiveRepairEarlyKeyData.Data.U,Data.key,he] using hu
  · change SelectedSourceBitsData.selected (Gather.field d.cs _ _) d.q d.rho d.n = _
    simpa only [controlWord,Data.key,he] using congrArg (fun xs => SelectedSourceBitsData.selected xs d.q d.rho d.n) hsource

theorem positive (d : Data) : 1≤d.q := by have := d.hbq; omega

local notation "EA" => ActiveRepairLayoutPermutation.earlyActual s d.q d.b d.n before after rows d.rho offset width d.side (positive d)
local notation "EI" => ActiveRepairLayoutPermutation.earlyIdeal s d.q d.b d.n before after rows d.rho offset width d.side (positive d)
local notation "EB" => ActiveRepairLayoutPermutation.earlyBad s d.q d.b d.n before after rows d.rho offset width d.side (positive d)
local notation "E" => indexEquiv s (d.n*d.b) (d.n*d.q) before after rows hw ha

include h he hw ha hp hf hc in
theorem flag : d.key.flag=rankFlag E EB (E x).val := by
  obtain ⟨hv,ht,_,hz⟩ := fields d s before after rows offset width rowBits he hw ha hp hf x hc
  rw [rankFlag_fin,Equiv.symm_apply_apply]
  have hh := ActiveRepairLayoutPermutationWords.early_flag d.q d.b d.n d.hb h.hbq3
    (controlWord before after d.q d.rho d.n offset width d.side (x.activeBefore,x.activeAfter))
    (BinaryAddressTableData.row (d.n*d.q) x.target.val)
    (BinaryAddressTableData.row (d.n*d.b) x.t.val)
    (SelectedSourceBitsData.selected_length _ _ _ _) (by simp) (by simp)
  change ActiveRepairEarlyFieldsBank.flag d.q d.b d.key.V d.key.T d.key.Z = _
  rw [hv,ht,hz]
  simp only [ActiveRepairLayoutPermutationWords.earlyWords,
    ActiveRepairLayoutPermutationWords.wordFin_row,ActiveRepairLayoutPermutation.earlyBad,
    ActiveRepairLayoutPermutation.earlyFiber,ActiveRepairLayoutPermutationFiber.earlyEquiv,
    Equiv.coe_fn_mk,VaryingControlRepairPacked.earlyBad] at hh ⊢
  rw [hh]
  exact decide_eq_decide.mpr Iff.rfl

include h he hw ha hp hf hc in
theorem destination_address :
    EI ((EA).symm x)={x with
      target:=ActiveRepairLayoutPermutationWords.wordFin (d.n*d.q) d.key.target
        ((ActiveRepairEarlyKeyRun.lengths d.key (key_valid d h)).1.trans (key_valid d h).hV),
      t:=ActiveRepairLayoutPermutationWords.wordFin (d.n*d.b) d.key.recoveredT
        ((ActiveRepairEarlyKeyRun.lengths d.key (key_valid d h)).2.1.trans (key_valid d h).hT)} := by
  obtain ⟨hv,ht,_,hz⟩ := fields d s before after rows offset width rowBits he hw ha hp hf x hc
  rw [ActiveRepairLayoutPermutationDestination.early_address,
    ActiveRepairLayoutPermutationDestination.early_words s d.q d.b d.n before after rows d.rho offset width d.side
      (positive d) d.hb d.hbq]
  simp only [←hv,←ht,←hz,ActiveRepairLayoutPermutationWords.earlyRepaired,
    ActiveRepairLayoutPermutationWords.earlyWords,ActiveRepairEarlyKeyData.Data.target,
    ActiveRepairEarlyKeyData.Data.recoveredT,Data.key]

include h he hw ha hp hf hc in
theorem destination (hr : rows≤2^rowBits) :
    d.key.destination=rankKey E EA EI (s.bits+rowBits) (E x).val := by
  have hk := key_valid d h
  have hv : d.key.target.length=d.n*d.q := (ActiveRepairEarlyKeyRun.lengths d.key hk).1.trans hk.hV
  have ht : d.key.recoveredT.length=d.n*d.b := (ActiveRepairEarlyKeyRun.lengths d.key hk).2.1.trans hk.hT
  let v := ActiveRepairLayoutPermutationWords.wordFin _ d.key.target hv
  let t := ActiveRepairLayoutPermutationWords.wordFin _ d.key.recoveredT ht
  obtain ⟨_,_,hu,_⟩ := fields d s before after rows offset width rowBits he hw ha hp hf x hc
  have hvr : d.key.target=BinaryAddressTableData.row (d.n*d.q) v.val := by
    simpa only [hv,v,ActiveRepairLayoutPermutationWords.wordFin_val] using ActiveRepairEarlyKeyValue.word_row d.key.target
  have htr : d.key.recoveredT=BinaryAddressTableData.row (d.n*d.b) t.val := by
    simpa only [ht,t,ActiveRepairLayoutPermutationWords.wordFin_val] using ActiveRepairEarlyKeyValue.word_row d.key.recoveredT
  rw [rankKey_fin,destRank,Equiv.symm_apply_apply,destination_address d h s before after rows offset width rowBits he hw ha hp hf x hc]
  change d.key.destination=rankBits (s.bits+rowBits)
    (index s (d.n*d.b) (d.n*d.q) before after rows hw ha
      (ActiveRepairDestinationPatchGeometry.replaced s (d.n*d.b) (d.n*d.q) before after rows x v t x.u)).val
  have hA : d.key.A=s.bits+rowBits := by simp only [Data.key,he,geometry]
  have hsv : d.key.sv=ActiveRepairRankFieldsGeometry.targetStart s after := by
    change ActiveRepairRankHeadersData.targetStart d.geom=_
    rw [he]
    exact congrFun (patch_values s (d.n*d.b) (d.n*d.q) before after offset width rowBits hw) 2
  have hst : d.key.st=ActiveRepairRankFieldsGeometry.tStart s (d.n*d.b) (d.n*d.q) before after := by
    change ActiveRepairRankHeadersData.tStart d.geom=_
    rw [he]
    exact congrFun (patch_values s (d.n*d.b) (d.n*d.q) before after offset width rowBits hw) 4
  have hsu : d.key.su=ActiveRepairRankFieldsGeometry.uStart s (d.n*d.b) (d.n*d.q) before after := by
    change ActiveRepairRankHeadersData.uStart d.geom=_
    rw [he]
    exact congrFun (patch_values s (d.n*d.b) (d.n*d.q) before after offset width rowBits hw) 6
  unfold ActiveRepairEarlyKeyData.Data.destination
  rw [hA,hsv,hst,hsu,hvr,htr,hu]
  rw [ActiveRepairLayoutKeysFields.rankBits_row]
  exact ActiveRepairDestinationPatchEndpoint.generated_word s (d.n*d.b) (d.n*d.q) before after rows rowBits
    hw ha hp hr x d.cs hc v t x.u

end
end IntegerMultBounds.Machine.ActiveRepairLayoutKeysEarly
