module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerPorts

/-! Instantiate the actual class setup on the fixed caller bank. The input
contract contains ordinary scalar words, width rulers and fresh owned storage. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  CommonClassGeometry ScalarPlacement ScalarPlacement.ComputedClassBanks PackedTranspose
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section

variable {T A D p u l target s t B W N radius width Vg Vr : ℕ}

def formatWidths (B Vg Vr : ℕ) : Fin 3 → ℕ := ![B,Vg,Vr]

def rulers (T : ℕ) (f : Fin 3) : Fin (MachineTapes T) := fullHeader T (.ruler f)

theorem rulers_injective (T : ℕ) : Function.Injective (rulers T) := by
  intro i j h
  exact Role.ruler.inj (fullHeader_injective T h)

def scalarValues (T p u l target s t B W N radius width : ℕ) : Fin (MachineTapes T) → ℕ :=
  Function.extend (globals T) (globalValues p u l target s t B W N radius width) (fun _ => 0)

theorem scalarValues_global (i : Fin 11) :
    scalarValues T p u l target s t B W N radius width (globals T i) =
      globalValues p u l target s t B W N radius width i :=
  (globals_injective T).extend_apply _ _ i

def formatBits (T B Vg Vr : ℕ) : Fin (MachineTapes T) → ℕ :=
  Function.extend (rulers T) (formatWidths B Vg Vr) (fun _ => 0)

theorem formatBits_ruler (f : Fin 3) :
    formatBits T B Vg Vr (rulers T f) = formatWidths B Vg Vr f :=
  (rulers_injective T).extend_apply _ _ f

structure SetupInput (T A D p u l target s t B W N radius width Vg Vr : ℕ)
    (S : Stacks (MachineTapes T) A) : Prop where
  scalarWords : ∀ i, S.R (globals T i) = binSyms D (globalValues p u l target s t B W N radius width i)
  rulerLengths : ∀ f, (S.R (rulers T f)).length = formatWidths B Vg Vr f
  ownedBlank : ∀ r ∈ ownedRoles, S.R (fullHeader T r) = []
  zeroBlank : S.R (fullHeader T .zero) = []
  routingBlank : ∀ i, S.R (Fin.natAdd ((T+headerCount)+175) i) = []

/-- Construct the concrete setup; no execution or generated-word field is an
input. The inherited execution theorem runs its actual initialized program. -/
def makeSetup {S : Stacks (MachineTapes T) A}
    (input : SetupInput T A D p u l target s t B W N radius width Vg Vr S)
    (clipped : Bool) (hwidth : 0 < width) (hgeometry : width+2*radius < 2^D)
    (hfit : ∀ i, globalValues p u l target s t B W N radius width i < 2^D)
    (hbits : ∀ f, formatWidths B Vg Vr f ≤ D) :
    FormattedClassSetup D p u l target s t B W N radius width S := by
  refine {
    rg := seedReg T
    injective := seedReg_injective T
    globals := globals T
    zero := fullHeader T .zero
    widthMaster := globals T 0
    core := fullHeader T .core
    halo := fullHeader T .halo
    saved := seedReg T (.z 0)
    tmp := seedReg T (.z 1)
    formats := formats T
    bits := formatBits T B Vg Vr
    value := scalarValues T p u l target s t B W N radius width
    clipped := clipped
    widthOff := fun r => (fullHeader_ne_seed T (.scalar 0) r).symm
    zeroOff := fun r => (fullHeader_ne_seed T .zero r).symm
    globalOff := fun i r => (fullHeader_ne_seed T (.scalar i) r).symm
    globalsNonzero := ?_
    coreHalo := (fullHeader_injective T).ne (by intro h; cases h)
    coreOff := fun r => (fullHeader_ne_seed T .core r).symm
    haloOff := fun r => (fullHeader_ne_seed T .halo r).symm
    copyRegs := formats_copyRegs T
    copySep := ?_
    destinations := formats_nodup T
    headerOff := ?_
    workOff := ?_
    bitsFit := ?_
    values := scalarValues_global
    fit := ?_
    widthPositive := hwidth
    geometryFit := hgeometry
    widthWord := ?_
    zeroWord := input.zeroBlank
    globalWords := ?_
    seedBlank := ?_
    coreBlank := input.ownedBlank .core core_mem_owned
    haloBlank := input.ownedBlank .halo halo_mem_owned
    headersBlank := ?_
    counts := ?_
    savedBlank := ?_
    tmpBlank := ?_}
  · intro i
    exact (fullHeader_injective T).ne (by intro h; cases h)
  · intro r hr q hq
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hq
    exact (fullHeader_injective T).ne (by intro h; cases h)
  · intro r hr
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
    exact ⟨(fullHeader_injective T).ne (by intro h; cases h),
      (fullHeader_injective T).ne (by intro h; cases h)⟩
  · intro k hk
    rcases List.mem_append.mp hk with hk | hk
    · obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hk
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
      exact ⟨(fullHeader_injective T).ne (by intro h; cases h),
        (fullHeader_injective T).ne (by intro h; cases h)⟩
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl
      all_goals exact ⟨(fullHeader_ne_seed T .core _).symm,(fullHeader_ne_seed T .halo _).symm⟩
  · intro r hr
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
    change formatBits T B Vg Vr (rulers T i) ≤ D
    rw [formatBits_ruler]
    exact hbits i
  · intro i
    rw [scalarValues_global]
    exact hfit i
  · rw [input.scalarWords 0]
    exact length_binSyms _ _
  · intro i
    rw [scalarValues_global]
    exact input.scalarWords i
  · intro r
    exact input.routingBlank _
  · intro r hr
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
    exact input.ownedBlank (.haloFormat i) (format_mem_owned i)
  · intro r hr
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
    change (S.R (rulers T i)).length = formatBits T B Vg Vr (rulers T i)
    rw [formatBits_ruler]
    exact input.rulerLengths i
  · exact input.routingBlank _
  · exact input.routingBlank _

theorem formats_cost : binaryFormatsCost (formatBits T B Vg Vr) (formats T) =
    10*(B+Vg+Vr)+31 := by
  change binaryFormatsCost (formatBits T B Vg Vr)
    (classHaloFormats (rulers T) (fun f => fullHeader T (.haloFormat f))) = _
  rw [classHaloFormats_cost]
  simp [formatBits_ruler,formatWidths]

theorem setupConsumers {S : Stacks (MachineTapes T) A}
    (input : SetupInput T A D p u l target s t B W N radius width Vg Vr S)
    (clipped : Bool) (hwidth : 0 < width) (hgeometry : width+2*radius < 2^D)
    (hfit : ∀ i, globalValues p u l target s t B W N radius width i < 2^D)
    (hbits : ∀ f, formatWidths B Vg Vr f ≤ D) :
    let c := makeSetup input clipped hwidth hgeometry hfit hbits
    c.ConsumerLayout (masterSources T) (geometrySources T 3)
      (classCallerRegister (exposure T 3)) (classCallerRegister (routing T 3)) Vg Vr
      (haloRows clipped s width radius) := by
  exact consumerLayout (T := T) (A := A) (makeSetup input clipped hwidth hgeometry hfit hbits)
    rfl rfl (fun _ => rfl) rfl Vg Vr (haloRows clipped s width radius)
    (fun f => formatBits_ruler f) rfl

/-- Execute the fixed caller setup, with its three-format export bill closed. -/
theorem setup_exec_within {Q : ℕ} {P U : Type} {S : Stacks (MachineTapes T) A}
    (body : P → Pr P (MachineTapes T) Q A U)
    (input : SetupInput T A D p u l target s t B W N radius width Vg Vr S)
    (clipped : Bool) (hwidth : 0 < width) (hgeometry : width+2*radius < 2^D)
    (hfit : ∀ i, globalValues p u l target s t B W N radius width i < 2^D)
    (hbits : ∀ f, formatWidths B Vg Vr f ≤ D)
    (v : HS (MachineTapes T) Q A U) (depth : ℕ) :
    let c := makeSetup input clipped hwidth hgeometry hfit hbits
    ∃ v' n, v'.user = v.user ∧ n ≤ prepareMastersTimeCost D+(10*(B+Vg+Vr)+31) ∧
      Stack.ExecWithin body (fun d z => Fast.Main.mnSize z+d ≤ Fast.Main.mnSize (Host.mk v S)+depth+
        (prepareMastersStock D+3*(10*(B+Vg+Vr)+31))) depth c.program
        (Host.mk v S) n (Host.mk v' c.loaded) := by
  dsimp only
  obtain ⟨v',n,hu,hn,he⟩ := (makeSetup input clipped hwidth hgeometry hfit hbits).exec_within body v depth
  refine ⟨v',n,hu,?_,?_⟩
  · simpa only [FormattedClassSetup.timeCost,makeSetup,formats_cost] using hn
  · simpa only [FormattedClassSetup.stock,makeSetup,formats_cost] using he

theorem setupNumericalInput {S : Stacks (MachineTapes T) A}
    (input : SetupInput T A D p u l target s t B W N radius width Vg Vr S)
    (clipped : Bool) (hwidth : 0 < width) (hgeometry : width+2*radius < 2^D)
    (hfit : ∀ i, globalValues p u l target s t B W N radius width i < 2^D)
    (hbits : ∀ f, formatWidths B Vg Vr f ≤ D)
    (b : ComputedClassBank → Fin T)
    (hgeometryWords : ∀ j : Fin 3, S.R (geometrySources T (Fin.castAdd 1 j)) = binSyms B (![s,width,radius] j))
    (htable : ∀ r, S.R (numericTable T r) = [])
    (hbank : ∀ j, j ≠ .control .source → S.R (fullExposedClassBank (bank b) j) = [])
    (hleft : ∀ j, S.L (recovery (fullExposedClassBank (bank b)) (.work j)) = []) :
    let c := makeSetup input clipped hwidth hgeometry hfit hbits
    c.NumericalInput (fullExposedClassBank (bank b)) (numericTable T) (geometrySources T) (masterSources T) := by
  exact numericalInput (T := T) (A := A) (makeSetup input clipped hwidth hgeometry hfit hbits)
    b rfl rfl hgeometryWords htable hbank hleft

/-- The routing width is read from the retained ruler; it is not an additional
layout assumption. Both halo formats come from this concrete setup. -/
def setupGatherInput {Q K : ℕ} {S : Stacks (MachineTapes T) (prime+K)}
    {Fs : List (ZMod s → GaussianInt)} {borrowed : List (Fin (prime+K+4))}
    (input : SetupInput T (prime+K) D p u l target s t B W N radius width Vg Vr S)
    (clipped : Bool) (hwidth : 0 < width) (hgeometry : width+2*radius < 2^D)
    (hfit : ∀ i, globalValues p u l target s t B W N radius width i < 2^D)
    (hbits : ∀ f, formatWidths B Vg Vr f ≤ D)
    (b : ComputedClassBank → Fin T)
    (g : RestoringGatherSeed (Q := Q) (bank b) Vg s width radius (haloRows clipped s width radius) W Fs borrowed S)
    (hExpose : g.exposeSrc = exposure T) (hRoute : g.routeSrc = routing T)
    (hInput : g.input = header T .input) :
    let c := makeSetup input clipped hwidth hgeometry hfit hbits
    c.GatherInput g (numericTable T) (masterSources T) (geometrySources T 3) := by
  have hR := g.hRV
  rw [hRoute] at hR
  change (S.R (rulers T 2)).length = g.D at hR
  have hD : g.D = Vr := hR.symm.trans (input.rulerLengths 2)
  apply gatherInput (T := T) (Q := Q) (K := K) (makeSetup input clipped hwidth hgeometry hfit hbits)
    b g hExpose hRoute hInput rfl rfl (fun _ => rfl) rfl _ rfl
  intro f
  rw [hD]
  exact formatBits_ruler f

namespace SetupInput

/-- Publishing a class changes only the ambient role, so the same setup input
contract serves the next class without rebuilding the retained word bank. -/
theorem updateOutput {S : Stacks (MachineTapes T) A}
    (input : SetupInput T A D p u l target s t B W N radius width Vg Vr S)
    (ys : List (Fin (A+4))) :
    SetupInput T A D p u l target s t B W N radius width Vg Vr
      {S with R := Function.update S.R (fullHeader T .output) ys} := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i
    change Function.update S.R (fullHeader T .output) ys (fullHeader T (.scalar i)) = _
    rw [Function.update_of_ne ((fullHeader_injective T).ne (by intro h; cases h))]
    exact input.scalarWords i
  · intro f
    change (Function.update S.R (fullHeader T .output) ys (fullHeader T (.ruler f))).length = _
    rw [Function.update_of_ne ((fullHeader_injective T).ne (by intro h; cases h))]
    exact input.rulerLengths f
  · intro r hr
    have hne : fullHeader T r ≠ fullHeader T .output :=
      ((fullHeader_injective T).ne (retained_ne_owned .output rfl r hr)).symm
    change Function.update S.R (fullHeader T .output) ys (fullHeader T r) = []
    rw [Function.update_of_ne hne]
    exact input.ownedBlank r hr
  · change Function.update S.R (fullHeader T .output) ys (fullHeader T .zero) = []
    rw [Function.update_of_ne ((fullHeader_injective T).ne (by intro h; cases h))]
    exact input.zeroBlank
  · intro i
    have hne : Fin.natAdd ((T+headerCount)+175) i ≠ fullHeader T .output :=
      (prefix_ne_routing (Fin.castAdd 175 (header T .output)) i).symm
    change Function.update S.R (fullHeader T .output) ys (Fin.natAdd ((T+headerCount)+175) i) = []
    rw [Function.update_of_ne hne]
    exact input.routingBlank i

end SetupInput

theorem setupProgram_updateOutput {Q : ℕ} {P U : Type} {S : Stacks (MachineTapes T) A}
    (input : SetupInput T A D p u l target s t B W N radius width Vg Vr S)
    (clipped : Bool) (hwidth : 0 < width) (hgeometry : width+2*radius < 2^D)
    (hfit : ∀ i, globalValues p u l target s t B W N radius width i < 2^D)
    (hbits : ∀ f, formatWidths B Vg Vr f ≤ D) (ys : List (Fin (A+4))) :
    (makeSetup (input.updateOutput ys) clipped hwidth hgeometry hfit hbits).program (P := P) (Q := Q) (U := U) =
      (makeSetup input clipped hwidth hgeometry hfit hbits).program := rfl

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
