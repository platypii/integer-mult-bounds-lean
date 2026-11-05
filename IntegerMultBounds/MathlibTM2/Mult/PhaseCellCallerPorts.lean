module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerLayout
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExposedClassGeometryFrame
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAllocatedCommonClassMasters
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFormattedClassCallerReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFormattedClassSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSetupNumericalReadiness
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSetupGatherReadiness

/-! Place the caller roles in the actual exposure/routing machine. The seed
borrows the existing routing suffix; all retained headers remain in the prefix. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  ScalarPlacement ScalarPlacement.ComputedClassBanks PackedTranspose
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section

abbrev MachineTapes (T : ℕ) := ((T+headerCount)+175)+tapeCount

def fullHeader (T : ℕ) (r : Role) : Fin (MachineTapes T) := classCallerRegister (header T r)

def seedReg (T : ℕ) : TblR 13 → Fin (MachineTapes T) := commonSeedReg ((T+headerCount)+175)

theorem fullHeader_injective (T : ℕ) : Function.Injective (fullHeader T) :=
  classCallerRegister_injective.comp (header_injective T)

theorem fullHeader_ne_bank {T : ℕ} {κ : Type} (b : κ → Fin T) (r : Role) (k : κ) :
    fullHeader T r ≠ classCallerRegister (bank b k) :=
  classCallerRegister_injective.ne (header_ne_bank b r k)

theorem fullHeader_ne_numerical {T : ℕ} (b : ComputedClassBank → Fin T) (r : Role) (k : ComputedClassBank) :
    fullHeader T r ≠ fullExposedClassBank (bank b) k := by
  rw [fullExposedClassBank_apply]
  exact fullHeader_ne_bank b r k

theorem seedReg_injective (T : ℕ) : Function.Injective (seedReg T) := commonSeedReg_injective _

theorem fullHeader_ne_seed (T : ℕ) (r : Role) (k : TblR 13) : fullHeader T r ≠ seedReg T k := by
  exact (commonSeedReg_off_prefix k (Fin.castAdd 175 (header T r))).symm

def allocation (T : ℕ) : Role ⊕ TblR 13 → Fin (MachineTapes T)
  | .inl r => fullHeader T r
  | .inr k => seedReg T k

theorem allocation_injective (T : ℕ) : Function.Injective (allocation T) := by
  intro x y h
  cases x with
  | inl r =>
    cases y with
    | inl k => exact congrArg Sum.inl (fullHeader_injective T h)
    | inr k => exact False.elim (fullHeader_ne_seed T r k h)
  | inr r =>
    cases y with
    | inl k => exact False.elim (fullHeader_ne_seed T k r h.symm)
    | inr k => exact congrArg Sum.inr (seedReg_injective T h)

def globals (T : ℕ) (i : Fin 11) : Fin (MachineTapes T) := fullHeader T (.scalar i)
def masterSources (T : ℕ) : Fin 12 → Fin (MachineTapes T) := fullHeader T ∘ masterRole
def numericTable (T : ℕ) : TblR 12 → Fin (MachineTapes T) := fullHeader T ∘ tableRole
def geometrySources (T : ℕ) : Fin 4 → Fin (MachineTapes T) := fullHeader T ∘ geometryRole 0

def formats (T : ℕ) : List (Fin (MachineTapes T) × Fin (MachineTapes T)) :=
  List.ofFn (fun f : Fin 3 => (fullHeader T (.ruler f),fullHeader T (.haloFormat f)))

def ownedPorts (T : ℕ) : List (Fin (T+headerCount)) := ownedRoles.map (header T)
def tablePorts (T : ℕ) : List (Fin (T+headerCount)) := tableRoles.map (header T)

theorem globals_injective (T : ℕ) : Function.Injective (globals T) := by
  intro i j h
  exact Role.scalar.inj (fullHeader_injective T h)

theorem masterSources_injective (T : ℕ) : Function.Injective (masterSources T) :=
  (fullHeader_injective T).comp masterRole_injective

theorem numericTable_injective (T : ℕ) : Function.Injective (numericTable T) :=
  (fullHeader_injective T).comp tableRole_injective

theorem masterSources_prefix (T : ℕ) (i : Fin 10) :
    masterSources T (Fin.castAdd 2 i) = globals T (Fin.castAdd 1 i) := by
  simp only [masterSources,globals,Function.comp_apply,masterRole,Fin.val_castAdd,dite_eq_left i.isLt]
  rfl

theorem formats_nodup (T : ℕ) : ((formats T).map Prod.snd).Nodup := by
  rw [formats,List.map_ofFn]
  apply List.nodup_ofFn.mpr
  intro i j h
  exact Role.haloFormat.inj (fullHeader_injective T h)

theorem formats_copyRegs (T : ℕ) (r) (hr : r ∈ formats T) :
    [r.1,fullHeader T .halo,r.2,seedReg T (.z 0),seedReg T (.z 1)].Nodup := by
  obtain ⟨f,rfl⟩ := List.mem_ofFn.mp hr
  let roles : List (Role ⊕ TblR 13) := [.inl (.ruler f),.inl .halo,.inl (.haloFormat f),.inr (.z 0),.inr (.z 1)]
  have hn : roles.Nodup := by simp [roles,List.nodup_cons]
  exact hn.map (allocation_injective T)

theorem retained_off_class (T : ℕ) (r : Role) (hr : isOwned r = false) :
    classInputPortOff (masterSources T) (formats T) (fullHeader T r) := by
  refine ⟨?_,?_,?_⟩
  · exact (fullHeader_injective T).ne (retained_ne_owned r hr .core core_mem_owned)
  · exact (fullHeader_injective T).ne (retained_ne_owned r hr .halo halo_mem_owned)
  · intro k hk
    obtain ⟨f,rfl⟩ := List.mem_ofFn.mp hk
    exact ((fullHeader_injective T).ne (retained_ne_owned r hr (.haloFormat f) (format_mem_owned f))).symm

theorem numerical_off_class {T : ℕ} (b : ComputedClassBank → Fin T) (k : ComputedClassBank) :
    classInputPortOff (masterSources T) (formats T) (fullExposedClassBank (bank b) k) := by
  refine ⟨(fullHeader_ne_numerical b .core k).symm,(fullHeader_ne_numerical b .halo k).symm,?_⟩
  intro r hr
  obtain ⟨f,rfl⟩ := List.mem_ofFn.mp hr
  exact fullHeader_ne_numerical b (.haloFormat f) k

theorem table_covered (T : ℕ) (r : TblR 12) :
    ∃ output ∈ tablePorts T, classCallerRegister output = numericTable T r := by
  exact ⟨header T (tableRole r),List.mem_map.mpr ⟨tableRole r,tableRole_mem r,rfl⟩,rfl⟩

theorem core_covered (T : ℕ) :
    ∃ output ∈ ownedPorts T, classCallerRegister output = fullHeader T .core := by
  exact ⟨header T .core,List.mem_map.mpr ⟨.core,core_mem_owned,rfl⟩,rfl⟩

theorem halo_covered (T : ℕ) :
    ∃ output ∈ ownedPorts T, classCallerRegister output = fullHeader T .halo := by
  exact ⟨header T .halo,List.mem_map.mpr ⟨.halo,halo_mem_owned,rfl⟩,rfl⟩

theorem formats_covered (T : ℕ) (r) (hr : r ∈ formats T) :
    ∃ output ∈ ownedPorts T, classCallerRegister output = r.2 := by
  obtain ⟨f,rfl⟩ := List.mem_ofFn.mp hr
  exact ⟨header T (.haloFormat f),List.mem_map.mpr ⟨.haloFormat f,format_mem_owned f,rfl⟩,rfl⟩

private theorem origins_map {N : ℕ} (f : Role → Fin N) :
    publicationRetainedOriginSources (f ∘ routingRole) (f ∘ publicationRole) = f ∘ originRole := by
  have hz : f ∘ (Matrix.vecEmpty : Fin 0 → Role) = (Matrix.vecEmpty : Fin 0 → Fin N) := Subsingleton.elim _ _
  simp only [publicationRetainedOriginSources,originRole,Matrix.vecCons,Fin.comp_cons,hz,Function.comp_apply]

theorem origins_eq (T : ℕ) : publicationRetainedOriginSources (routing T) (publication T) = origins T := by
  exact origins_map (header T)

theorem publicationWidth (T : ℕ) : publication T 7 = origins T 4 := rfl
theorem publicationReplicas (T : ℕ) : publication T 3 = routing T 6 := rfl
theorem publicationWord (T : ℕ) : publication T 5 = routing T 5 := rfl

/-- The fixed roles instantiate the selected theorem's consumer ABI. -/
theorem consumerLayout {T A D p u l target s t B W N radius width : ℕ}
    {S : Stacks (MachineTapes T) A}
    (c : FormattedClassSetup D p u l target s t B W N radius width S)
    (hcore : c.core = fullHeader T .core) (hhalo : c.halo = fullHeader T .halo)
    (hglobals : ∀ i, c.globals i = globals T i) (hformats : c.formats = formats T)
    (Vg Vr L : ℕ)
    (hbits : ∀ f : Fin 3, c.bits (fullHeader T (.ruler f)) = ![B,Vg,Vr] f)
    (hLength : L = CommonClassGeometry.haloRows c.clipped s width radius) :
    c.ConsumerLayout (masterSources T) (geometrySources T 3)
      (classCallerRegister (exposure T 3)) (classCallerRegister (routing T 3)) Vg Vr L := by
  have hmem (f : Fin 3) : (fullHeader T (.ruler f),fullHeader T (.haloFormat f)) ∈ c.formats := by
    rw [hformats]
    exact List.mem_ofFn.mpr ⟨f,rfl⟩
  refine ⟨?_,?_,?_,hLength,?_,?_,?_⟩
  · intro i; rw [hglobals]; exact masterSources_prefix T i
  · rw [hcore]; rfl
  · rw [hhalo]; rfl
  · exact ⟨_,hmem 0,rfl,hbits 0⟩
  · exact ⟨_,hmem 1,rfl,hbits 1⟩
  · exact ⟨_,hmem 2,rfl,hbits 2⟩

/-- Typed ownership discharges the numerical caller's separation obligations.
Only ordinary geometry inputs and baseline work freshness remain as hypotheses. -/
theorem numericalInput {T A D p u l target s t B W N radius width : ℕ}
    {S : Stacks (MachineTapes T) A}
    (c : FormattedClassSetup D p u l target s t B W N radius width S)
    (b : ComputedClassBank → Fin T) (hformats : c.formats = formats T)
    (hzero : c.zero = fullHeader T .zero)
    (hgeometry : ∀ j : Fin 3, S.R (geometrySources T (Fin.castAdd 1 j)) = binSyms B (![s,width,radius] j))
    (htable : ∀ r, S.R (numericTable T r) = [])
    (hbank : ∀ j, j ≠ .control .source → S.R (fullExposedClassBank (bank b) j) = [])
    (hleft : ∀ j, S.L (recovery (fullExposedClassBank (bank b)) (.work j)) = []) :
    c.NumericalInput (fullExposedClassBank (bank b)) (numericTable T) (geometrySources T) (masterSources T) := by
  refine ⟨masterSources_injective T,hgeometry,?_,?_,?_,htable,hbank,hleft⟩
  · rw [hzero,hformats]
    exact retained_off_class T .zero rfl
  · intro r
    rw [hformats]
    exact retained_off_class T (tableRole r) (tableRole_not_owned r)
  · intro j
    rw [hformats]
    exact numerical_off_class b j

/-- Construct all gather layout obligations from the fixed caller roles. -/
def gatherInput {T Q K V D p u l target s t B W N radius width L : ℕ}
    {Fs : List (ZMod s → GaussianInt)} {borrowed : List (Fin (prime+K+4))}
    {S : Stacks (MachineTapes T) (prime+K)}
    (c : FormattedClassSetup D p u l target s t B W N radius width S)
    (b : ComputedClassBank → Fin T)
    (g : RestoringGatherSeed (Q := Q) (bank b) V s width radius L W Fs borrowed S)
    (hExpose : g.exposeSrc = exposure T) (hRoute : g.routeSrc = routing T)
    (hInput : g.input = header T .input)
    (hcore : c.core = fullHeader T .core) (hhalo : c.halo = fullHeader T .halo)
    (hglobals : ∀ i, c.globals i = globals T i) (hformats : c.formats = formats T)
    (hbits : ∀ f : Fin 3, c.bits (fullHeader T (.ruler f)) = ![B,V,g.D] f)
    (hLength : L = CommonClassGeometry.haloRows c.clipped s width radius) :
    c.GatherInput g (numericTable T) (masterSources T) (geometrySources T 3) := by
  refine {
    consumers := by
      simpa only [hExpose,hRoute] using consumerLayout c hcore hhalo hglobals hformats V g.D L hbits hLength
    ownedPorts := ownedPorts T
    coreCovered := by simpa only [hcore] using core_covered T
    haloCovered := by simpa only [hhalo] using halo_covered T
    formatsCovered := by intro r hr; rw [hformats] at hr; exact formats_covered T r hr
    exposeOff := ?_
    inputOff := ?_
    routeOff := ?_
    outputOff := ?_
    tablePorts := tablePorts T
    tableCovered := table_covered T
    tableExposeOff := ?_
    tableInputOff := ?_
    tableRouteOff := ?_
    tableOutputOff := ?_}
  · intro j hj output ho
    rw [hExpose]
    exact header_ne_portset T (exposureRole j) ownedRoles isOwned
      (exposureRole_not_owned j hj) ownedRole_isOwned output ho
  · intro output ho
    rw [hInput]
    exact header_ne_portset T .input ownedRoles isOwned rfl ownedRole_isOwned output ho
  · intro j hj output ho
    rw [hRoute]
    exact header_ne_portset T (routingRole j) ownedRoles isOwned
      (routingRole_not_owned j hj) ownedRole_isOwned output ho
  · intro output ho
    obtain ⟨r,_,rfl⟩ := List.mem_map.mp ho
    exact (header_ne_bank b r _).symm
  · intro j output ho
    rw [hExpose]
    exact header_ne_portset T (exposureRole j) tableRoles isTable
      (exposureRole_not_table j) tableRoles_isTable output ho
  · intro output ho
    rw [hInput]
    exact header_ne_portset T .input tableRoles isTable rfl tableRoles_isTable output ho
  · intro j output ho
    rw [hRoute]
    exact header_ne_portset T (routingRole j) tableRoles isTable
      (routingRole_not_table j) tableRoles_isTable output ho
  · intro output ho
    obtain ⟨r,_,rfl⟩ := List.mem_map.mp ho
    exact (header_ne_bank b r _).symm

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
