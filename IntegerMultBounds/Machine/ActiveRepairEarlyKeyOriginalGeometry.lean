import IntegerMultBounds.Machine.ActiveRepairEarlyKeyOriginalRun

/-! Both original source geometries imply every generated descriptor fit.
No runtime field start or prefix-dependent source-control word is supplied. -/
namespace IntegerMultBounds.Machine.ActiveRepairEarlyKeyOriginalGeometry
noncomputable section
open ActiveRepairEarlyKeyOriginalData ActiveRepairEarlyKeyOriginalValid
open ActiveRepairRankHeadersData ActiveRepairRankHeadersEndpoint
open CompactGadgetReservationShape

theorem geometry_fits (d : Data) (s : Shape) (w m before after offset width rowBits : ℕ)
    (he : d.geom=geometry s w m before after offset width rowBits)
    (hw : w≤s.H) (ha : before+m+after=s.active*s.chunk)
    (hf : sourceFits d.side before after offset width) :
    ∀ i, d.key.starts i+d.key.widths i≤d.geom.addressBits := by
  intro i
  change parserValues d.side d.geom (ActiveRepairRankFieldsBank.offsetSlot i)+
    parserValues d.side d.geom (ActiveRepairRankFieldsBank.widthSlot i)≤d.geom.addressBits
  rw [he]
  cases hs : d.side with
  | before =>
    obtain ⟨h0,h1⟩ := parser_before_values s w m before after offset width rowBits hw i
    rw [h0,h1]
    exact (ActiveRepairRankFieldsEndpoint.before_fits s w m before after hw ha offset width
      (by simpa only [sourceFits,hs] using hf) i).trans (Nat.le_add_right _ _)
  | after =>
    obtain ⟨h0,h1⟩ := parser_after_values s w m before after offset width rowBits hw i
    rw [h0,h1]
    exact (ActiveRepairRankFieldsEndpoint.after_fits s w m before after hw ha offset width
      (by simpa only [sourceFits,hs] using hf) i).trans (Nat.le_add_right _ _)

theorem geometry_valid (d : Data) (s : Shape) (w m before after offset width rowBits : ℕ)
    (he : d.geom=geometry s w m before after offset width rowBits)
    (hw : w≤s.H) (ha : before+m+after=s.active*s.chunk)
    (hf : sourceFits d.side before after offset width)
    (hv : ∀ i, Counter.value (d.originals i)=originalValues d.geom i)
    (hc : ∀ i, GrowingCounterData.Canonical (d.originals i))
    (hbq3 : d.b+3≤d.q) (hwidth : width=d.f*d.q) (hV : m=d.n*d.q) (hT : w=d.n*d.b)
    (hnf : d.n+1=d.f) (hr : d.rho<d.q)
    (sv : ∀ i, Counter.value (d.ss i)=SelectedSourceBitsRun.values d.q d.n d.rho d.f i)
    (sc : ∀ i, GrowingCounterData.Canonical (d.ss i))
    (bv : Counter.value d.bs=d.b) (bc : GrowingCounterData.Canonical d.bs) : Valid d where
  hw := by simpa only [he,geometry] using hw
  hv := hv
  hc := hc
  bounded := by rw [he]; exact geometry_bounded d.side s w m before after offset width rowBits hw ha hf
  hbq3 := hbq3
  hwidth := by simpa only [he,geometry] using hwidth
  hV := by simpa only [he,geometry] using hV
  hT := by simpa only [he,geometry] using hT
  hnf := hnf
  hr := hr
  sv := sv
  sc := sc
  bv := bv
  bc := bc
  fit := geometry_fits d s w m before after offset width rowBits he hw ha hf

theorem retained (d : Data) (i : Fin 42) (hi : i≠30) :
    d.output.head i=d.input.head i ∧ d.output.tape i=d.input.tape i := by
  simp [Data.output,SharedPlacementAlphabet.setTape,hi]

theorem key_tape (d : Data) : d.output.tape 30=
    FlagCopy.keyTape (FlagCopy.keyWord d.key.flag d.key.destination) := rfl

end
end IntegerMultBounds.Machine.ActiveRepairEarlyKeyOriginalGeometry
