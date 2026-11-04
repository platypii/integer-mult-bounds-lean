module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCommonClassSeedLoad
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInputTableUpdate

/-! Complete restoring class-master setup from ordinary global words.
The temporary seed bank is blank again before numerical execution starts. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CommonClassGeometry
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type}

theorem loadedSeed_update_off (rg : TblR 13 → Fin T) (globals : Fin 11 → Fin T) (zero : Fin T)
    (D : ℕ) (value : Fin T → ℕ) (S : Stacks T A) (k : Fin T) (xs : List (Fin (A+4)))
    (hoff : ∀ r, rg r ≠ k) :
    loadedSeed rg globals zero D value {S with R := Function.update S.R k xs} =
      {loadedSeed rg globals zero D value S with R :=
        (Function.update (loadedSeed rg globals zero D value S).R k xs)} :=
  loadedInputTable_update_off rg (seedSources globals zero) D (sourceValue value zero) S k xs hoff

theorem loadedSeed_masterLoaded (rg : TblR 13 → Fin T) (globals : Fin 11 → Fin T) (zero : Fin T)
    (D : ℕ) (value : Fin T → ℕ) (core halo : Fin T) (clipped : Bool) (s width radius : ℕ)
    (S : Stacks T A) (hcore : ∀ r, rg r ≠ core) (hhalo : ∀ r, rg r ≠ halo) :
    loadedSeed rg globals zero D value (masterLoaded core halo D clipped s width radius S) =
      masterLoaded core halo D clipped s width radius (loadedSeed rg globals zero D value S) := by
  let C : Stacks T A := {S with R := Function.update S.R core (binSyms D (coreRows clipped s width))}
  change loadedSeed rg globals zero D value
    {C with R := Function.update C.R halo (binSyms D (haloRows clipped s width radius))} = _
  rw [loadedSeed_update_off rg globals zero D value C halo _ hhalo]
  dsimp only [C]
  rw [loadedSeed_update_off rg globals zero D value S core _ hcore]
  rfl

def prepareMasters (rg : TblR 13 → Fin T) (globals : Fin 11 → Fin T) (zero widthMaster : Fin T)
    (clipped : Bool) (core halo : Fin T) : Pr P T Q A U :=
  .seq (chirpBankLoad rg (seedSources globals zero) widthMaster zero)
    (.seq (masterProgram rg clipped core halo) (clearWords (inputTableWords rg)))

def prepareMastersTimeCost (D : ℕ) := seedLoadCost D+(masterTimeCost D+(28*D+29))

def prepareMastersStock (D : ℕ) := 3*seedLoadCost D+masterStock D

theorem prepareMasters_exec_within (body : P → Pr P T Q A U) (rg : TblR 13 → Fin T) (hinj : Function.Injective rg)
    (globals : Fin 11 → Fin T) (zero widthMaster core halo : Fin T)
    (hwidthOff : ∀ r, rg r ≠ widthMaster) (hzeroOff : ∀ r, rg r ≠ zero)
    (hglobalOff : ∀ j r, rg r ≠ globals j) (hoff : ∀ j, globals j ≠ zero)
    (hne : core ≠ halo) (hcoreOff : ∀ r, rg r ≠ core) (hhaloOff : ∀ r, rg r ≠ halo)
    (clipped : Bool) (D p u l target s t B W N radius width : ℕ) (value : Fin T → ℕ)
    (hvalues : ∀ j, value (globals j) = globalValues p u l target s t B W N radius width j)
    (hfit : ∀ j, value (globals j) < 2^D) (hwidth : 0 < width) (hgeometryFit : width+2*radius < 2^D)
    (v : HS T Q A U) (S : Stacks T A)
    (hwidthWord : (S.R widthMaster).length = D) (hzero : S.R zero = [])
    (hwords : ∀ j, S.R (globals j) = binSyms D (value (globals j)))
    (hblank : ∀ r, S.R (rg r) = []) (hcore : S.R core = []) (hhalo : S.R halo = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ prepareMastersTimeCost D ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+prepareMastersStock D) depth
        (prepareMasters rg globals zero widthMaster clipped core halo) (mk v S) n
        (mk v' (masterLoaded core halo D clipped s width radius S)) := by
  obtain ⟨v₁,hu₁,he₁,hholds,hseedFit⟩ := loadSeed_exec_within body rg hinj globals zero widthMaster
    hwidthOff hzeroOff hglobalOff hoff D p u l target s t B W N radius width value hvalues hfit
    v S hwidthWord hzero hwords hblank depth
  let M := loadedSeed rg globals zero D value S
  have hMcore : M.R core = [] := (loadedInputTable_off rg (seedSources globals zero) D (sourceValue value zero)
    S core (fun r => (hcoreOff r).symm)).trans hcore
  have hMhalo : M.R halo = [] := (loadedInputTable_off rg (seedSources globals zero) D (sourceValue value zero)
    S halo (fun r => (hhaloOff r).symm)).trans hhalo
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := master_exec_within body rg hinj core halo hne hcoreOff hhaloOff clipped D s width radius
    ⟨seedValues p u l target s t B W N radius width,[]⟩
    (by simp [seedValues]) (by simp [seedValues]) (by simp [seedValues])
    (by simp [seedValues]) (by simp [seedValues]) hwidth hgeometryFit hseedFit
    (List.replicate D tick) (by simp) v₁ M hholds hMcore hMhalo depth
  let exported := masterLoaded core halo D clipped s width radius S
  let after := masterLoaded core halo D clipped s width radius M
  have hcommute : loadedSeed rg globals zero D value exported = after :=
    loadedSeed_masterLoaded rg globals zero D value core halo clipped s width radius S hcoreOff hhaloOff
  have hblankExported (r) : exported.R (rg r) = [] := by
    simpa only [exported,masterLoaded,Function.update_of_ne (hcoreOff r),Function.update_of_ne (hhaloOff r)] using hblank r
  obtain ⟨v₃,hu₃,he₃⟩ := retireSeed_exec_within body rg hinj globals zero D value core hcoreOff
    (binSyms D (coreRows clipped s width)) v₂ exported hblankExported depth
  have hafterCore : after.R core = binSyms D (coreRows clipped s width) := by simp [after,masterLoaded,hne]
  have hstart : {loadedSeed rg globals zero D value exported with R :=
      (Function.update (loadedSeed rg globals zero D value exported).R core (binSyms D (coreRows clipped s width)))} = after := by
    rw [hcommute]
    rw [←hafterCore,Function.update_eq_self]
  have hexportedCore : exported.R core = binSyms D (coreRows clipped s width) := by simp [exported,masterLoaded,hne]
  have hend : {exported with R := Function.update exported.R core (binSyms D (coreRows clipped s width))} = exported := by
    rw [←hexportedCore,Function.update_eq_self]
  rw [hstart,hend] at he₃
  refine ⟨v₃,seedLoadCost D+(n₂+(28*D+29)),hu₃.trans (hu₂.trans hu₁),?_,?_⟩
  · exact Nat.add_le_add_left (Nat.add_le_add_right hn₂ _) _
  · simpa only [prepareMasters,prepareMastersStock,Nat.add_zero] using mn_seq_within_add he₁ (mn_seq_within_add he₂ he₃)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CommonClassGeometry
