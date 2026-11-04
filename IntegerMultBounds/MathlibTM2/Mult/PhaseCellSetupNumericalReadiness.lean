module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFormattedClassSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFormattedClassCallerReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationCallerReady

/-! Ordinary global words and the consumer layout determine the selected
master values and numerical readiness. No generated word is an input fact. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.FormattedClassSetup
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  CommonClassGeometry ScalarPlacement ScalarPlacement.ComputedClassBanks
variable {T A D p u l target s t B W N radius width : ℕ} {S : Stacks T A}

private theorem global_seed_prefix (j : Fin 10) :
    globalValues p u l target s t B W N radius width (Fin.castAdd 1 j) =
      seedValues p u l target s t B W N radius width (Fin.castAdd 3 j) := by
  fin_cases j <;> rfl

private theorem prefix_index (j : Fin 12) (h10 : j ≠ 10) (h11 : j ≠ 11) :
    ∃ i : Fin 10, Fin.castAdd 2 i = j := by
  have hj : j.val < 10 := by
    have := j.isLt
    have h10' : j.val ≠ 10 := by intro h; exact h10 (Fin.ext h)
    have h11' : j.val ≠ 11 := by intro h; exact h11 (Fin.ext h)
    omega
  exact ⟨⟨j.val,hj⟩,Fin.ext rfl⟩

/-- The global ABI supplies the entire retained part of the master bank. -/
theorem masterPrefix (c : FormattedClassSetup D p u l target s t B W N radius width S)
    {masters : Fin 12 → Fin T} {numerical exposure routing : Fin T} {Vg Vr L : ℕ}
    (layout : c.ConsumerLayout masters numerical exposure routing Vg Vr L)
    (j : Fin 12) (h10 : j ≠ 10) (h11 : j ≠ 11) :
    S.R (masters j) = binSyms D
      (seedValues p u l target s t B W N radius width (Fin.castAdd 1 j)) := by
  obtain ⟨i,hji⟩ := prefix_index j h10 h11
  rw [←hji,layout.globalPrefix,c.globalWords,c.values,global_seed_prefix]
  have hcast : Fin.castAdd 1 (Fin.castAdd 2 i) = Fin.castAdd 3 i := Fin.ext rfl
  rw [hcast]

/-- The semantic value assignment changes only the two generated master slots. -/
def classValues (c : FormattedClassSetup D p u l target s t B W N radius width S) : Fin T → ℕ :=
  Function.update (Function.update c.value c.core (coreRows c.clipped s width))
    c.halo (haloRows c.clipped s width radius)

theorem classValues_masters (c : FormattedClassSetup D p u l target s t B W N radius width S)
    {masters : Fin 12 → Fin T} {numerical exposure routing : Fin T} {Vg Vr L : ℕ}
    (layout : c.ConsumerLayout masters numerical exposure routing Vg Vr L)
    (hinj : Function.Injective masters) :
    ∀ j, c.classValues (masters j) = commonInputValues p u l target s t B W N radius L j := by
  intro j
  rw [layout.classLength]
  by_cases h10 : j = 10
  · subst j
    simp [classValues,layout.coreSource,c.coreHalo,commonInputValues,Matrix.vecAppend_eq_ite,haloRows]
  by_cases h11 : j = 11
  · subst j
    simp [classValues,layout.haloSource,commonInputValues,Matrix.vecAppend_eq_ite]
  have hc : masters j ≠ c.core := by rw [←layout.coreSource]; exact hinj.ne h10
  have hh : masters j ≠ c.halo := by rw [←layout.haloSource]; exact hinj.ne h11
  simp only [classValues,Function.update_of_ne hc,Function.update_of_ne hh]
  obtain ⟨i,hji⟩ := prefix_index j h10 h11
  rw [←hji,layout.globalPrefix,c.values,global_seed_prefix]
  exact seed_prefix c.clipped p u l target s t B W N radius width (Fin.castAdd 2 i)
    (by simpa only [hji] using h10) (by simpa only [hji] using h11)

theorem classValues_fit (c : FormattedClassSetup D p u l target s t B W N radius width S)
    {masters : Fin 12 → Fin T} {numerical exposure routing : Fin T} {Vg Vr L : ℕ}
    (layout : c.ConsumerLayout masters numerical exposure routing Vg Vr L)
    (hinj : Function.Injective masters) : ∀ j, c.classValues (masters j) < 2^D := by
  intro j
  have hcore := coreRows_le c.clipped s width c.widthPositive
  have hfit := c.geometryFit
  by_cases h10 : j = 10
  · subst j
    simp only [classValues,layout.coreSource,Function.update_of_ne c.coreHalo,Function.update_self]
    omega
  by_cases h11 : j = 11
  · subst j
    simp only [classValues,layout.haloSource,Function.update_self,haloRows]
    omega
  have hc : masters j ≠ c.core := by rw [←layout.coreSource]; exact hinj.ne h10
  have hh : masters j ≠ c.halo := by rw [←layout.haloSource]; exact hinj.ne h11
  simp only [classValues,Function.update_of_ne hc,Function.update_of_ne hh]
  obtain ⟨i,hji⟩ := prefix_index j h10 h11
  rw [←hji,layout.globalPrefix]
  exact c.fit (Fin.castAdd 1 i)

theorem wordBits_positive (c : FormattedClassSetup D p u l target s t B W N radius width S) : 0 < D := by
  by_contra hn
  have hd : D = 0 := by omega
  have hg := c.geometryFit
  have hw := c.widthPositive
  simp only [hd,pow_zero] at hg
  omega

private theorem nonempty_ne_blank (k q : Fin T) (n : ℕ) (hn : 0 < n)
    (hlen : (S.R k).length = n) (hblank : S.R q = []) : k ≠ q := by
  intro h
  rw [h,hblank] at hlen
  simp only [List.length_nil] at hlen
  omega

/-- Positive-length retained inputs are automatically outside the initially
blank owned words, so their preservation needs no extra separation premise. -/
theorem portOff_of_length (c : FormattedClassSetup D p u l target s t B W N radius width S)
    {masters : Fin 12 → Fin T} {numerical exposure routing : Fin T} {Vg Vr L : ℕ}
    (layout : c.ConsumerLayout masters numerical exposure routing Vg Vr L)
    (k : Fin T) (n : ℕ) (hn : 0 < n) (hlen : (S.R k).length = n) :
    classInputPortOff masters c.formats k := by
  refine ⟨?_,?_,?_⟩
  · rw [layout.coreSource]; exact nonempty_ne_blank k c.core n hn hlen c.coreBlank
  · rw [layout.haloSource]; exact nonempty_ne_blank k c.halo n hn hlen c.haloBlank
  · intro r hr
    exact (nonempty_ne_blank k r.2 n hn hlen (c.headersBlank r hr)).symm

/-- Readiness comes from ordinary global headers and fresh work banks. The
layout and setup supply all master words and the fourth geometry header. -/
theorem numericalReady (c : FormattedClassSetup D p u l target s t B W N radius width S)
    (bank : ComputedClassBank → Fin T) (rg : TblR 12 → Fin T)
    (src : Fin 4 → Fin T) (masters : Fin 12 → Fin T) (hinj : Function.Injective masters)
    {exposure routing : Fin T} {Vg Vr L : ℕ}
    (layout : c.ConsumerLayout masters (src 3) exposure routing Vg Vr L)
    (hB : 0 < B)
    (hgeometry : ∀ j, j ≠ 3 → S.R (src j) = binSyms B (![s,width,radius,L] j))
    (hzeroOff : classInputPortOff masters c.formats c.zero)
    (htableOff : ∀ r, classInputPortOff masters c.formats (rg r))
    (hbankOff : ∀ j, classInputPortOff masters c.formats (bank j))
    (htable : ∀ r, S.R (rg r) = [])
    (hbank : ∀ j, j ≠ .control .source → S.R (bank j) = [])
    (hleft : ∀ j, S.L (recovery bank (.work j)) = []) :
    ClassCallerReady bank rg src masters c.widthMaster c.zero B D s width radius L c.classValues c.loaded := by
  have hprefix := c.masterPrefix layout
  have hmastersOff (j : Fin 12) (r) (hr : r ∈ c.formats) : r.2 ≠ masters j := by
    by_cases h10 : j = 10
    · subst j; rw [layout.coreSource]; exact (c.headerOff r hr).1
    by_cases h11 : j = 11
    · subst j; rw [layout.haloSource]; exact (c.headerOff r hr).2
    have hlen : (S.R (masters j)).length = D := by rw [hprefix j h10 h11]; exact length_binSyms _ _
    exact (c.portOff_of_length layout (masters j) D c.wordBits_positive hlen).2.2 r hr
  have hready := classCallerReady_of_formats bank rg src masters hinj c.widthMaster c.zero c.formats
    c.destinations c.bits B D c.clipped p u l target s t W N radius width c.classValues S
    (by simpa only [layout.classLength] using c.classValues_masters layout hinj)
    hprefix layout.numericalHeader
    (by intro j hj; apply c.portOff_of_length layout (src j) B hB
        rw [hgeometry j hj]; exact length_binSyms _ _)
    (by simpa only [layout.classLength] using hgeometry)
    hmastersOff c.headersBlank
    (c.portOff_of_length layout c.widthMaster D c.wordBits_positive c.widthWord)
    hzeroOff htableOff hbankOff c.widthWord c.zeroWord htable hbank hleft
  simpa only [loaded,layout.coreSource,layout.haloSource,←layout.classLength] using hready

/-- Only pre-setup geometry inputs and fresh numerical storage are retained.
The class-specific geometry header and all twelve master words are derived. -/
structure NumericalInput (c : FormattedClassSetup D p u l target s t B W N radius width S)
    (bank : ComputedClassBank → Fin T) (rg : TblR 12 → Fin T)
    (src : Fin 4 → Fin T) (masters : Fin 12 → Fin T) : Prop where
  mastersInjective : Function.Injective masters
  geometryWords : ∀ j : Fin 3, S.R (src (Fin.castAdd 1 j)) = binSyms B (![s,width,radius] j)
  zeroOff : classInputPortOff masters c.formats c.zero
  tableOff : ∀ r, classInputPortOff masters c.formats (rg r)
  bankOff : ∀ j, classInputPortOff masters c.formats (bank j)
  tableBlank : ∀ r, S.R (rg r) = []
  numericalBlank : ∀ j, j ≠ .control .source → S.R (bank j) = []
  leftBlank : ∀ j, S.L (recovery bank (.work j)) = []

namespace NumericalInput

theorem ready {c : FormattedClassSetup D p u l target s t B W N radius width S}
    {bank : ComputedClassBank → Fin T} {rg : TblR 12 → Fin T}
    {src : Fin 4 → Fin T} {masters : Fin 12 → Fin T}
    (input : NumericalInput c bank rg src masters)
    {exposure routing : Fin T} {Vg Vr L : ℕ}
    (layout : c.ConsumerLayout masters (src 3) exposure routing Vg Vr L) (hB : 0 < B) :
    ClassCallerReady bank rg src masters c.widthMaster c.zero B D s width radius L c.classValues c.loaded := by
  apply c.numericalReady bank rg src masters input.mastersInjective layout hB
    _ input.zeroOff input.tableOff input.bankOff input.tableBlank input.numericalBlank input.leftBlank
  intro j hj
  fin_cases j
  · exact input.geometryWords 0
  · exact input.geometryWords 1
  · exact input.geometryWords 2
  · exact False.elim (hj rfl)

end NumericalInput

/-- Publication freshness is a baseline fact; setup preserves it outside its
owned master and format destinations. Left stacks are unchanged everywhere. -/
theorem publicationReady (c : FormattedClassSetup D p u l target s t B W N radius width S)
    {masters : Fin 12 → Fin T} {numerical exposure routing : Fin T} {Vg Vr L : ℕ}
    (layout : c.ConsumerLayout masters numerical exposure routing Vg Vr L)
    (src : Fin 10 → Fin T) (placement : Fin PackedTranspose.tapeCount → Fin T)
    (input : PublicationCallerReady src placement S)
    (hoff : ∀ j ∈ [(0 : Fin 10),1,2,4,6,8,9], classInputPortOff masters c.formats (src j)) :
    PublicationCallerReady src placement c.loaded := by
  constructor
  · intro j hj
    have hport := hoff j hj
    have hc : src j ≠ c.core := by simpa only [←layout.coreSource] using hport.1
    have hh : src j ≠ c.halo := by simpa only [←layout.haloSource] using hport.2.1
    exact (c.loaded_off (src j) hc hh hport.2.2).trans (input.ownedBlank j hj)
  · intro i
    change c.loaded.L (placement i) = []
    unfold loaded formattedClassLoaded
    exact input.leftBlank i

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.FormattedClassSetup
