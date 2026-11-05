module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCopyBinaryHeaderBank

/-! Produce each consumer's three ordinary geometry words from the retained
scalar bank. The same list execution serves numerical, exposure and routing. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  CommonClassGeometry ScalarPlacement ScalarPlacement.ComputedClassBanks PackedTranspose
noncomputable section
variable {T A D p u l target s t B W N radius width Vg Vr : ℕ}

def geometryScalarIndex : Fin 3 → Fin 11 := ![4,10,9]

def geometryCopies (T : ℕ) (f : Fin 3) : List (Fin (MachineTapes T) × Fin (MachineTapes T)) :=
  List.ofFn fun i => (globals T (geometryScalarIndex i),fullHeader T (.geometry f i))

def geometryLoaded (f : Fin 3) (S : Stacks (MachineTapes T) A) : Stacks (MachineTapes T) A :=
  {S with R := (copyWordHeadersR
    (fun k => binSyms (formatWidths B Vg Vr f) (scalarValues T p u l target s t B W N radius width k))
    (geometryCopies T f) S.R)}

theorem geometryCopies_nodup (T : ℕ) (f : Fin 3) : ((geometryCopies T f).map Prod.snd).Nodup := by
  rw [geometryCopies,List.map_ofFn,List.nodup_ofFn]
  intro i j h
  exact (Role.geometry.inj (fullHeader_injective T h)).2

theorem geometryLoaded_header (f : Fin 3) (S : Stacks (MachineTapes T) A) (r : Role)
    (hr : ∀ i, r ≠ .geometry f i) :
    (geometryLoaded (p := p) (u := u) (l := l) (target := target) (s := s) (t := t)
      (B := B) (W := W) (N := N) (radius := radius) (width := width) (Vg := Vg) (Vr := Vr) f S).R
        (fullHeader T r) = S.R (fullHeader T r) := by
  apply copyWordHeadersR_off
  intro q hq
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
  exact ((fullHeader_injective T).ne (hr i)).symm

theorem geometryLoaded_word (f i : Fin 3) (S : Stacks (MachineTapes T) A)
    (hblank : S.R (fullHeader T (.geometry f i)) = []) :
    (geometryLoaded (p := p) (u := u) (l := l) (target := target) (s := s) (t := t)
      (B := B) (W := W) (N := N) (radius := radius) (width := width) (Vg := Vg) (Vr := Vr) f S).R
        (fullHeader T (.geometry f i)) = binSyms (formatWidths B Vg Vr f) (![s,width,radius] i) := by
  change copyWordHeadersR
    (fun k => binSyms (formatWidths B Vg Vr f) (scalarValues T p u l target s t B W N radius width k))
    (geometryCopies T f) S.R (fullHeader T (.geometry f i)) = _
  rw [copyWordHeadersR_get _ _ (geometryCopies_nodup T f) S.R
    (globals T (geometryScalarIndex i),fullHeader T (.geometry f i)) (List.mem_ofFn.mpr ⟨i,rfl⟩)]
  rw [hblank,List.append_nil,scalarValues_global]
  fin_cases i <;> rfl

namespace SetupInput

/-- Preparing a consumer's geometry preserves the retained setup contract. -/
theorem prepareGeometry {S : Stacks (MachineTapes T) A}
    (input : SetupInput T A D p u l target s t B W N radius width Vg Vr S) (f : Fin 3) :
    SetupInput T A D p u l target s t B W N radius width Vg Vr
      (geometryLoaded (p := p) (u := u) (l := l) (target := target) (s := s) (t := t)
        (B := B) (W := W) (N := N) (radius := radius) (width := width) (Vg := Vg) (Vr := Vr) f S) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i
    rw [show globals T i = fullHeader T (.scalar i) from rfl,
      geometryLoaded_header f S (.scalar i) (by intro j h; cases h)]
    exact input.scalarWords i
  · intro i
    rw [show rulers T i = fullHeader T (.ruler i) from rfl,
      geometryLoaded_header f S (.ruler i) (by intro j h; cases h)]
    exact input.rulerLengths i
  · intro r hr
    rw [geometryLoaded_header f S r (fun i => (retained_ne_owned (.geometry f i) rfl r hr).symm)]
    exact input.ownedBlank r hr
  · rw [geometryLoaded_header f S .zero (by intro j h; cases h)]
    exact input.zeroBlank
  · intro i
    change copyWordHeadersR
      (fun k => binSyms (formatWidths B Vg Vr f) (scalarValues T p u l target s t B W N radius width k))
      (geometryCopies T f) S.R (Fin.natAdd ((T+headerCount)+175) i) = []
    rw [copyWordHeadersR_off]
    · exact input.routingBlank i
    · intro q hq
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hq
      exact prefix_ne_routing (Fin.castAdd 175 (header T (.geometry f j))) i

end SetupInput

/-- Each format is exported by the same fixed program. The retained wide
scalars and ruler survive; only the three fresh geometry words change. -/
theorem prepareGeometry_exec_within {Q : ℕ} {P U : Type}
    (body : P → Pr P (MachineTapes T) Q A U)
    {S : Stacks (MachineTapes T) A}
    (input : SetupInput T A D p u l target s t B W N radius width Vg Vr S)
    (f : Fin 3) (hbits : formatWidths B Vg Vr f ≤ D)
    (hblank : ∀ i, S.R (fullHeader T (.geometry f i)) = [])
    (v : HS (MachineTapes T) Q A U) (depth : ℕ) :
    ∃ v', v'.user = v.user ∧
      Stack.ExecWithin body (fun d z => Fast.Main.mnSize z+d ≤ Fast.Main.mnSize (Host.mk v S)+depth+
        3*(3*(10*formatWidths B Vg Vr f+10)+1)) depth
        (copyBinaryHeaderBank (rulers T f) (seedReg T (.z 0)) (seedReg T (.z 1)) (geometryCopies T f))
        (Host.mk v S) (3*(10*formatWidths B Vg Vr f+10)+1)
        (Host.mk v' (geometryLoaded (p := p) (u := u) (l := l) (target := target) (s := s) (t := t)
          (B := B) (W := W) (N := N) (radius := radius) (width := width) (Vg := Vg) (Vr := Vr) f S)) := by
  have hregs : ∀ r ∈ geometryCopies T f,
      [rulers T f,r.1,r.2,seedReg T (.z 0),seedReg T (.z 1)].Nodup := by
    intro r hr
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
    have hn : ([Sum.inl (.ruler f),Sum.inl (.scalar (geometryScalarIndex i)),Sum.inl (.geometry f i),
        Sum.inr (.z 0),Sum.inr (.z 1)] : List (Role ⊕ TblR 13)).Nodup := by simp
    exact hn.map (allocation_injective T)
  have hsep : ∀ r ∈ geometryCopies T f, ∀ q ∈ geometryCopies T f, r.2 ≠ q.1 := by
    intro r hr q hq
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hq
    exact (fullHeader_injective T).ne (by intro h; cases h)
  obtain ⟨v',hu,he⟩ := copyBinaryHeaderBank_exec_within body (rulers T f) (seedReg T (.z 0)) (seedReg T (.z 1))
    (geometryCopies T f) hregs hsep (geometryCopies_nodup T f) (formatWidths B Vg Vr f) D hbits
    (scalarValues T p u l target s t B W N radius width) v S
    (by
      intro r hr
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
      rw [scalarValues_global]
      exact input.scalarWords _)
    (input.rulerLengths f)
    (by intro r hr; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr; exact hblank i)
    (input.routingBlank _) (input.routingBlank _) depth
  exact ⟨v',hu,by simpa only [geometryLoaded,geometryCopies,List.length_ofFn] using he⟩

/-- The numerical readiness factory consumes actually exported geometry.
Its three binary words are conclusions, rather than caller hypotheses. -/
theorem preparedNumericalInput {S : Stacks (MachineTapes T) A}
    (input : SetupInput T A D p u l target s t B W N radius width Vg Vr S)
    (clipped : Bool) (hwidth : 0 < width) (hgeometry : width+2*radius < 2^D)
    (hfit : ∀ i, globalValues p u l target s t B W N radius width i < 2^D)
    (hbits : ∀ f, formatWidths B Vg Vr f ≤ D)
    (b : ComputedClassBank → Fin T)
    (hblank : ∀ i, S.R (fullHeader T (.geometry 0 i)) = [])
    (htable : ∀ r, S.R (numericTable T r) = [])
    (hbank : ∀ j, j ≠ .control .source → S.R (fullExposedClassBank (bank b) j) = [])
    (hleft : ∀ j, S.L (recovery (fullExposedClassBank (bank b)) (.work j)) = []) :
    let c := makeSetup (input.prepareGeometry 0) clipped hwidth hgeometry hfit hbits
    c.NumericalInput (fullExposedClassBank (bank b)) (numericTable T) (geometrySources T) (masterSources T) := by
  apply setupNumericalInput (input.prepareGeometry 0) clipped hwidth hgeometry hfit hbits b
  · intro j
    have hj : geometrySources T (Fin.castAdd 1 j) = fullHeader T (.geometry 0 j) := by
      fin_cases j <;> rfl
    rw [hj]
    exact geometryLoaded_word 0 j S (hblank j)
  · intro r
    rw [show numericTable T r = fullHeader T (tableRole r) from rfl,
      geometryLoaded_header 0 S (tableRole r) (by intro i h; cases r <;> cases h)]
    exact htable r
  · intro j hj
    change copyWordHeadersR
      (fun k => binSyms (formatWidths B Vg Vr 0) (scalarValues T p u l target s t B W N radius width k))
      (geometryCopies T 0) S.R (fullExposedClassBank (bank b) j) = []
    rw [copyWordHeadersR_off]
    · exact hbank j hj
    · intro q hq
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
      exact fullHeader_ne_numerical b (.geometry 0 i) j
  · exact hleft

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
