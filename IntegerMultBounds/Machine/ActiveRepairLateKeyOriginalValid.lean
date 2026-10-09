import IntegerMultBounds.Machine.ActiveRepairLateKeyOriginalData

/-! Generated header values satisfy the complete later-key execution contract.
All start positions are functions of the original geometric widths. -/
namespace IntegerMultBounds.Machine.ActiveRepairLateKeyOriginalValid
noncomputable section
open ActiveRepairLateKeyOriginalData ActiveRepairRankHeadersData
open RecursiveChildQuotientsConstant (bits_value bits_canonical)

structure Valid (d : Data) : Prop where
  hw : d.geom.w≤d.geom.H
  hv : ∀ i, Counter.value (d.originals i)=originalValues d.geom i
  hc : ∀ i, GrowingCounterData.Canonical (d.originals i)
  bounded : ∀ i, originalValues d.geom i≤d.geom.addressBits
  hbq3 : d.b+3≤d.q
  hwidth : d.geom.sourceWidth=d.f*d.q
  hV : d.geom.m=d.n*d.q
  hT : d.geom.w=d.n*d.b
  hnf : d.n+1=d.f
  hr : d.rho<d.q
  sv : ∀ i, Counter.value (d.ss i)=SelectedSourceBitsRun.values d.q d.n d.rho d.f i
  sc : ∀ i, GrowingCounterData.Canonical (d.ss i)
  bv : Counter.value d.bs=d.b
  bc : GrowingCounterData.Canonical d.bs
  fit : ∀ i, d.key.starts i+d.key.widths i≤d.geom.addressBits

theorem key_valid (d : Data) (h : Valid d) : ActiveRepairLateKeyRun.Valid d.key where
  hv0 := fun _ => bits_value _
  hv1 := fun _ => bits_value _
  hc := fun _ => bits_canonical _
  hbq3 := h.hbq3
  hwidth := h.hwidth
  hV := h.hV
  hT := h.hT
  hU := h.hT
  hnf := h.hnf
  hr := h.hr
  sv := h.sv
  sc := h.sc
  bv := h.bv
  bc := h.bc
  hfit := h.fit
  pz := bits_value _
  pA := bits_value _
  psv := bits_value _
  pv := bits_value _
  pst := bits_value _
  pt := bits_value _
  psu := bits_value _
  pc := fun _ => bits_canonical _
  fv := h.fit 0
  ft := h.fit 1
  fu := h.fit 2

end
end IntegerMultBounds.Machine.ActiveRepairLateKeyOriginalValid
