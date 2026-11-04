module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFormattedClassSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSetupNumericalReadiness
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedGatherReadiness
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGatherInputTable

/-! Complete ordinary retained gather inputs on the initialized class endpoint.
The two class halo fields come from the actual format exports. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.FormattedClassSetup
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  CommonClassGeometry ScalarPlacement ScalarPlacement.ComputedClassBanks PackedTranspose
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

/-- Every exported format is read from the shared computed halo. -/
theorem headerWord {T A D p u l target s t B W N radius width : ℕ} {S : Stacks T A}
    (c : FormattedClassSetup D p u l target s t B W N radius width S)
    (r : Fin T × Fin T) (hr : r ∈ c.formats) :
    c.loaded.R r.2 = binSyms (c.bits r.1) (haloRows c.clipped s width radius) := by
  let M := masterLoaded c.core c.halo D c.clipped s width radius S
  have hb : M.R r.2 = [] := by
    simpa only [M,masterLoaded,Function.update_of_ne (c.headerOff r hr).1,
      Function.update_of_ne (c.headerOff r hr).2] using c.headersBlank r hr
  have hh := copyWordHeadersR_get (fun k => binSyms (c.bits k) (haloRows c.clipped s width radius))
    c.formats c.destinations M.R r hr
  unfold loaded formattedClassLoaded
  simpa only [hb,List.append_nil] using hh

variable {T Q K V D p u l target s t B W N radius width L : ℕ}
  {bank : ComputedClassBank → Fin T} {Fs : List (ZMod s → GaussianInt)}
  {borrowed : List (Fin (prime+K+4))} {S : Stacks ((T+175)+tapeCount) (prime+K)}
noncomputable section

/-- Caller-prefix coverage keeps the temporary exposure and routing banks fresh.
Only the ordinary input fields of the gather seed are transported. -/
def gatherReady (c : FormattedClassSetup D p u l target s t B W N radius width S)
    (g : RestoringGatherSeed (Q := Q) bank V s width radius L W Fs borrowed S)
    (masters : Fin 12 → Fin ((T+175)+tapeCount)) (numerical : Fin ((T+175)+tapeCount))
    (layout : c.ConsumerLayout masters numerical (classCallerRegister (g.exposeSrc 3))
      (classCallerRegister (g.routeSrc 3)) V g.D L)
    (outputs : List (Fin T))
    (hcore : ∃ output ∈ outputs, classCallerRegister output = c.core)
    (hhalo : ∃ output ∈ outputs, classCallerRegister output = c.halo)
    (hformats : ∀ r ∈ c.formats, ∃ output ∈ outputs, classCallerRegister output = r.2)
    (hExpose : ∀ j, j ≠ 3 → ∀ output ∈ outputs, g.exposeSrc j ≠ output)
    (hInput : ∀ output ∈ outputs, g.input ≠ output)
    (hRoute : ∀ j, j ≠ 3 → ∀ output ∈ outputs, g.routeSrc j ≠ output)
    (hOutput : ∀ output ∈ outputs, bank (.control .source) ≠ output) :
    RestoringGatherData (Q := Q) bank V s width radius L W Fs borrowed c.loaded := by
  let seed := g.reframe c.loaded outputs
    (by
      intro k hk
      apply c.loaded_off k
      · obtain ⟨output,ho,heq⟩ := hcore
        simpa only [heq] using hk output ho
      · obtain ⟨output,ho,heq⟩ := hhalo
        simpa only [heq] using hk output ho
      · intro r hr
        obtain ⟨output,ho,heq⟩ := hformats r hr
        simpa only [heq] using (hk output ho).symm)
    (by unfold loaded formattedClassLoaded; rfl) hExpose hInput hRoute hOutput
  exact {
    toRestoringGatherSeed := seed
    hL := by
      change c.loaded.R (classCallerRegister (g.exposeSrc 3)) = binSyms V L
      obtain ⟨r,hr,hdst,hbits⟩ := layout.exposureHeader
      rw [←hdst,c.headerWord r hr,hbits,←layout.classLength]
    hRL := by
      change c.loaded.R (classCallerRegister (g.routeSrc 3)) = binSyms g.D L
      obtain ⟨r,hr,hdst,hbits⟩ := layout.routingHeader
      rw [←hdst,c.headerWord r hr,hbits,←layout.classLength]}

/-- Static port coverage and separation for setup and numerical table loading.
The seed supplies ordinary retained words, not initialized class halo headers. -/
structure GatherInput (c : FormattedClassSetup D p u l target s t B W N radius width S)
    (g : RestoringGatherSeed (Q := Q) bank V s width radius L W Fs borrowed S)
    (rg : TblR 12 → Fin ((T+175)+tapeCount))
    (masters : Fin 12 → Fin ((T+175)+tapeCount)) (numerical : Fin ((T+175)+tapeCount)) where
  consumers : c.ConsumerLayout masters numerical (classCallerRegister (g.exposeSrc 3))
    (classCallerRegister (g.routeSrc 3)) V g.D L
  ownedPorts : List (Fin T)
  coreCovered : ∃ output ∈ ownedPorts, classCallerRegister output = c.core
  haloCovered : ∃ output ∈ ownedPorts, classCallerRegister output = c.halo
  formatsCovered : ∀ r ∈ c.formats, ∃ output ∈ ownedPorts, classCallerRegister output = r.2
  exposeOff : ∀ j, j ≠ 3 → ∀ output ∈ ownedPorts, g.exposeSrc j ≠ output
  inputOff : ∀ output ∈ ownedPorts, g.input ≠ output
  routeOff : ∀ j, j ≠ 3 → ∀ output ∈ ownedPorts, g.routeSrc j ≠ output
  outputOff : ∀ output ∈ ownedPorts, bank (.control .source) ≠ output
  tablePorts : List (Fin T)
  tableCovered : ∀ r, ∃ output ∈ tablePorts, classCallerRegister output = rg r
  tableExposeOff : ∀ j output, output ∈ tablePorts → g.exposeSrc j ≠ output
  tableInputOff : ∀ output ∈ tablePorts, g.input ≠ output
  tableRouteOff : ∀ j output, output ∈ tablePorts → g.routeSrc j ≠ output
  tableOutputOff : ∀ output ∈ tablePorts, bank (.control .source) ≠ output

namespace GatherInput
variable {c : FormattedClassSetup D p u l target s t B W N radius width S}
  {g : RestoringGatherSeed (Q := Q) bank V s width radius L W Fs borrowed S}
  {rg : TblR 12 → Fin ((T+175)+tapeCount)}
  {masters : Fin 12 → Fin ((T+175)+tapeCount)} {numerical : Fin ((T+175)+tapeCount)}

def ready (input : GatherInput c g rg masters numerical) :
    RestoringGatherData (Q := Q) bank V s width radius L W Fs borrowed
      (loadedInputTable rg masters D c.classValues c.loaded) :=
  (c.gatherReady g masters numerical input.consumers input.ownedPorts input.coreCovered input.haloCovered
    input.formatsCovered input.exposeOff input.inputOff input.routeOff input.outputOff).loadInputTable
      rg input.tablePorts input.tableCovered masters D c.classValues input.tableExposeOff input.tableInputOff
      input.tableRouteOff input.tableOutputOff

theorem routeTableOff (input : GatherInput c g rg masters numerical) :
    ∀ j r, rg r ≠ classCallerRegister (input.ready.routeSrc j) := by
  intro j r
  obtain ⟨output,ho,heq⟩ := input.tableCovered r
  rw [←heq]
  exact classCallerRegister_injective.ne (input.tableRouteOff j output ho).symm

end GatherInput

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.FormattedClassSetup
