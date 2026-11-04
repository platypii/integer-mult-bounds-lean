module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareCommonClassMasters
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAllocatedPublicationOrigins

/-! Generate class words in the existing fresh routing suffix, then release it
before numerical execution. Retained global words occupy caller prefix ports. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv CommonClassGeometry
noncomputable section
variable {T Q A : ℕ} {P U : Type}

def commonSeedRole : TblR 13 → TblR 16
  | .v i => .v (Fin.castAdd 3 i)
  | .wr => .wr | .wn => .wn | .acc => .acc | .z i => .z i

theorem commonSeedRole_injective : Function.Injective commonSeedRole := by
  intro x y h
  cases x <;> cases y <;> simp_all [commonSeedRole,Fin.ext_iff]

def commonSeedReg (T : ℕ) (r : TblR 13) : Fin (T+tapeCount) :=
  Fin.natAdd T (headerReg (originReg (commonSeedRole r)))

theorem commonSeedReg_injective (T : ℕ) : Function.Injective (commonSeedReg T) :=
  (Fin.natAdd_injective _ _).comp (headerReg_injective.comp (originReg_injective.comp commonSeedRole_injective))

theorem commonSeedReg_off_prefix (r : TblR 13) (k : Fin T) :
    commonSeedReg T r ≠ Fin.castAdd tapeCount k := by
  intro heq
  have hh := congrArg (fun j : Fin (T+tapeCount) => j.val) heq
  simp only [commonSeedReg,Fin.val_natAdd,Fin.val_castAdd] at hh
  have := k.isLt
  omega

def allocatedClassMasters (globals : Fin 11 → Fin T) (zero widthMaster core halo : Fin T)
    (clipped : Bool) : Pr P (T+tapeCount) Q A U :=
  prepareMasters (commonSeedReg T) (Fin.castAdd tapeCount ∘ globals)
    (Fin.castAdd tapeCount zero) (Fin.castAdd tapeCount widthMaster) clipped
    (Fin.castAdd tapeCount core) (Fin.castAdd tapeCount halo)

theorem allocatedClassMasters_exec_within (body : P → Pr P (T+tapeCount) Q A U)
    (globals : Fin 11 → Fin T) (zero widthMaster core halo : Fin T)
    (hoff : ∀ j, globals j ≠ zero) (hne : core ≠ halo)
    (clipped : Bool) (D p u l target s t B W N radius width : ℕ) (value : Fin (T+tapeCount) → ℕ)
    (hvalues : ∀ j, value (Fin.castAdd tapeCount (globals j)) = globalValues p u l target s t B W N radius width j)
    (hfit : ∀ j, value (Fin.castAdd tapeCount (globals j)) < 2^D)
    (hwidth : 0 < width) (hgeometryFit : width+2*radius < 2^D)
    (v : HS (T+tapeCount) Q A U) (S : Stacks (T+tapeCount) A)
    (hwidthWord : (S.R (Fin.castAdd tapeCount widthMaster)).length = D)
    (hzero : S.R (Fin.castAdd tapeCount zero) = [])
    (hwords : ∀ j, S.R (Fin.castAdd tapeCount (globals j)) = binSyms D (value (Fin.castAdd tapeCount (globals j))))
    (hblank : ∀ i, S.R (Fin.natAdd T i) = [])
    (hcore : S.R (Fin.castAdd tapeCount core) = []) (hhalo : S.R (Fin.castAdd tapeCount halo) = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ prepareMastersTimeCost D ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+prepareMastersStock D) depth
        (allocatedClassMasters globals zero widthMaster core halo clipped) (mk v S) n
        (mk v' (masterLoaded (Fin.castAdd tapeCount core) (Fin.castAdd tapeCount halo) D clipped s width radius S)) := by
  exact prepareMasters_exec_within body (commonSeedReg T) (commonSeedReg_injective T)
    (Fin.castAdd tapeCount ∘ globals) (Fin.castAdd tapeCount zero) (Fin.castAdd tapeCount widthMaster)
    (Fin.castAdd tapeCount core) (Fin.castAdd tapeCount halo)
    (fun r => commonSeedReg_off_prefix r widthMaster) (fun r => commonSeedReg_off_prefix r zero)
    (fun j r => commonSeedReg_off_prefix r (globals j))
    (fun j => (Fin.castAdd_injective _ _).ne (hoff j)) ((Fin.castAdd_injective _ _).ne hne)
    (fun r => commonSeedReg_off_prefix r core) (fun r => commonSeedReg_off_prefix r halo)
    clipped D p u l target s t B W N radius width value hvalues hfit hwidth hgeometryFit v S hwidthWord hzero hwords
    (fun r => hblank (headerReg (originReg (commonSeedRole r)))) hcore hhalo depth

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
