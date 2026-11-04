module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFormattedClassInputs

/-! Ordinary inputs and physical layout for an initialized class prefix.
Execution is derived from these data; no execution field is stored. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv CommonClassGeometry
variable {T Q A : ℕ} {P U : Type}

structure FormattedClassSetup (D p u l target s t B W N radius width : ℕ) (S : Stacks T A) where
  rg : TblR 13 → Fin T
  injective : Function.Injective rg
  globals : Fin 11 → Fin T
  zero : Fin T
  widthMaster : Fin T
  core : Fin T
  halo : Fin T
  saved : Fin T
  tmp : Fin T
  formats : List (Fin T × Fin T)
  bits : Fin T → ℕ
  value : Fin T → ℕ
  clipped : Bool
  widthOff : ∀ r, rg r ≠ widthMaster
  zeroOff : ∀ r, rg r ≠ zero
  globalOff : ∀ j r, rg r ≠ globals j
  globalsNonzero : ∀ j, globals j ≠ zero
  coreHalo : core ≠ halo
  coreOff : ∀ r, rg r ≠ core
  haloOff : ∀ r, rg r ≠ halo
  copyRegs : ∀ r ∈ formats, [r.1,halo,r.2,saved,tmp].Nodup
  copySep : ∀ r ∈ formats, ∀ q ∈ formats, r.2 ≠ q.1
  destinations : (formats.map Prod.snd).Nodup
  headerOff : ∀ r ∈ formats, r.2 ≠ core ∧ r.2 ≠ halo
  workOff : ∀ k ∈ formats.map Prod.fst ++ [saved,tmp], k ≠ core ∧ k ≠ halo
  bitsFit : ∀ r ∈ formats, bits r.1 ≤ D
  values : ∀ j, value (globals j) = globalValues p u l target s t B W N radius width j
  fit : ∀ j, value (globals j) < 2^D
  widthPositive : 0 < width
  geometryFit : width+2*radius < 2^D
  widthWord : (S.R widthMaster).length = D
  zeroWord : S.R zero = []
  globalWords : ∀ j, S.R (globals j) = binSyms D (value (globals j))
  seedBlank : ∀ r, S.R (rg r) = []
  coreBlank : S.R core = []
  haloBlank : S.R halo = []
  headersBlank : ∀ r ∈ formats, S.R r.2 = []
  counts : ∀ r ∈ formats, (S.R r.1).length = bits r.1
  savedBlank : S.R saved = []
  tmpBlank : S.R tmp = []

namespace FormattedClassSetup
variable {D p u l target s t B W N radius width : ℕ} {S : Stacks T A}

/-- The selected call consumes this setup's global prefix and generated words. -/
structure ConsumerLayout (c : FormattedClassSetup D p u l target s t B W N radius width S)
    (masters : Fin 12 → Fin T) (numerical exposure routing : Fin T) (Vg Vr L : ℕ) : Prop where
  globalPrefix : ∀ j : Fin 10, masters (Fin.castAdd 2 j) = c.globals (Fin.castAdd 1 j)
  coreSource : masters 10 = c.core
  haloSource : masters 11 = c.halo
  classLength : L = haloRows c.clipped s width radius
  numericalHeader : ∃ r ∈ c.formats, r.2 = numerical ∧ c.bits r.1 = B
  exposureHeader : ∃ r ∈ c.formats, r.2 = exposure ∧ c.bits r.1 = Vg
  routingHeader : ∃ r ∈ c.formats, r.2 = routing ∧ c.bits r.1 = Vr

@[irreducible] def loaded (c : FormattedClassSetup D p u l target s t B W N radius width S) : Stacks T A :=
  formattedClassLoaded c.core c.halo D c.clipped s width radius c.bits c.formats S

def program (c : FormattedClassSetup D p u l target s t B W N radius width S) : Pr P T Q A U :=
  .seq (prepareMasters c.rg c.globals c.zero c.widthMaster c.clipped c.core c.halo)
    (copyBinaryFormats c.halo c.saved c.tmp c.formats)

def timeCost (c : FormattedClassSetup D p u l target s t B W N radius width S) :=
  prepareMastersTimeCost D+binaryFormatsCost c.bits c.formats

def stock (c : FormattedClassSetup D p u l target s t B W N radius width S) :=
  prepareMastersStock D+3*binaryFormatsCost c.bits c.formats

def retire (c : FormattedClassSetup D p u l target s t B W N radius width S) : Pr P T Q A U :=
  .seq (clearWords (c.formats.map Prod.snd)) (clearWords [c.core,c.halo])

def retireCost (c : FormattedClassSetup D p u l target s t B W N radius width S) :=
  (2*(c.formats.map (fun r => c.bits r.1)).sum+2*c.formats.length+1)+(4*D+5)

theorem loaded_off (c : FormattedClassSetup D p u l target s t B W N radius width S)
    (output : Fin T) (hc : output ≠ c.core) (hh : output ≠ c.halo)
    (hoff : ∀ r ∈ c.formats, r.2 ≠ output) : c.loaded.R output = S.R output := by
  unfold loaded
  change copyWordHeadersR _ c.formats (masterLoaded c.core c.halo D c.clipped s width radius S).R output = _
  rw [copyWordHeadersR_off _ _ _ output hoff]
  simp only [masterLoaded,Function.update_of_ne hc,Function.update_of_ne hh]

theorem exec_within (body : P → Pr P T Q A U)
    (c : FormattedClassSetup D p u l target s t B W N radius width S) (v : HS T Q A U) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ c.timeCost ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+c.stock) depth c.program
        (Host.mk v S) n (Host.mk v' c.loaded) := by
  unfold loaded
  exact prepareFormattedClass_exec_within body c.rg c.injective c.globals c.zero c.widthMaster c.core c.halo
    c.widthOff c.zeroOff c.globalOff c.globalsNonzero c.coreHalo c.coreOff c.haloOff c.formats c.saved c.tmp
    c.bits c.copyRegs c.copySep c.destinations c.headerOff c.workOff c.clipped D p u l target s t B W N radius width
    c.value c.bitsFit c.values c.fit c.widthPositive c.geometryFit v S c.widthWord c.zeroWord c.globalWords
    c.seedBlank c.coreBlank c.haloBlank c.headersBlank c.counts c.savedBlank c.tmpBlank depth

theorem retire_exec_within (body : P → Pr P T Q A U)
    (c : FormattedClassSetup D p u l target s t B W N radius width S)
    (output : Fin T) (houtCore : output ≠ c.core) (houtHalo : output ≠ c.halo)
    (hout : ∀ r ∈ c.formats, r.2 ≠ output) (ys : List (Fin (A+4)))
    (v : HS T Q A U) (depth : ℕ) :
    let F := {c.loaded with R := Function.update c.loaded.R output ys}
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v F)+depth+0) depth c.retire
        (Host.mk v F) c.retireCost (Host.mk v' {S with R := Function.update S.R output ys}) := by
  unfold loaded
  exact retireFormattedClass_exec_within body c.core c.halo output c.coreHalo houtCore houtHalo
    c.formats c.destinations c.headerOff hout c.bits D c.clipped s width radius ys v S c.coreBlank c.haloBlank
    c.headersBlank depth

end FormattedClassSetup
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
