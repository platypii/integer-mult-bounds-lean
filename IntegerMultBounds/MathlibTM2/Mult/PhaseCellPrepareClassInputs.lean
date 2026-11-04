module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareCommonClassMasters
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBinaryHeaderFormat

/-! Actual class setup from ordinary global words, including the narrow halo
header. Temporary seed and copy scratch are restored before the selected run. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CommonClassGeometry
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type}

def classInputsLoaded (core halo header : Fin T) (B D : ℕ) (clipped : Bool)
    (s width radius : ℕ) (S : Stacks T A) : Stacks T A :=
  let M := masterLoaded core halo D clipped s width radius S
  {M with R := Function.update M.R header (binSyms B (haloRows clipped s width radius))}

theorem prepareClassInputs_exec_within (body : P → Pr P T Q A U) (rg : TblR 13 → Fin T) (hinj : Function.Injective rg)
    (globals : Fin 11 → Fin T) (zero widthMaster core halo : Fin T)
    (hwidthOff : ∀ r, rg r ≠ widthMaster) (hzeroOff : ∀ r, rg r ≠ zero)
    (hglobalOff : ∀ j r, rg r ≠ globals j) (hoff : ∀ j, globals j ≠ zero)
    (hne : core ≠ halo) (hcoreOff : ∀ r, rg r ≠ core) (hhaloOff : ∀ r, rg r ≠ halo)
    (header count saved tmp : Fin T)
    (hcopy : [count,halo,header,saved,tmp].Nodup)
    (hheaderCore : header ≠ core) (hheaderHalo : header ≠ halo)
    (hworkOff : ∀ k ∈ [count,saved,tmp], k ≠ core ∧ k ≠ halo)
    (clipped : Bool) (D p u l target s t B W N radius width : ℕ) (hBD : B ≤ D) (value : Fin T → ℕ)
    (hvalues : ∀ j, value (globals j) = globalValues p u l target s t B W N radius width j)
    (hfit : ∀ j, value (globals j) < 2^D) (hwidth : 0 < width) (hgeometryFit : width+2*radius < 2^D)
    (v : HS T Q A U) (S : Stacks T A)
    (hwidthWord : (S.R widthMaster).length = D) (hzero : S.R zero = [])
    (hwords : ∀ j, S.R (globals j) = binSyms D (value (globals j)))
    (hblank : ∀ r, S.R (rg r) = []) (hcore : S.R core = []) (hhalo : S.R halo = [])
    (hheader : S.R header = []) (hcount : (S.R count).length = B)
    (hsaved : S.R saved = []) (htmp : S.R tmp = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ prepareMastersTimeCost D+(10*B+10) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+(prepareMastersStock D+3*(10*B+10))) depth
        (.seq (prepareMasters rg globals zero widthMaster clipped core halo)
          (copyPrefix count halo header saved tmp)) (mk v S) n
        (mk v' (classInputsLoaded core halo header B D clipped s width radius S)) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := prepareMasters_exec_within body rg hinj globals zero widthMaster
    core halo hwidthOff hzeroOff hglobalOff hoff hne hcoreOff hhaloOff clipped D p u l target s t B W N
    radius width value hvalues hfit hwidth hgeometryFit v S hwidthWord hzero hwords hblank hcore hhalo depth
  let M := masterLoaded core halo D clipped s width radius S
  have hframe (k : Fin T) (hk : k ≠ core ∧ k ≠ halo) : M.R k = S.R k := by
    simp only [M,masterLoaded,Function.update_of_ne hk.1,Function.update_of_ne hk.2]
  obtain ⟨v₂,hu₂,he₂⟩ := copyBinaryHeader_exec_within body count halo header saved tmp hcopy B D
    (haloRows clipped s width radius) hBD v₁ M
    (by rw [hframe count (hworkOff count (by simp))]; exact hcount)
    (by simp [M,masterLoaded])
    ((hframe header ⟨hheaderCore,hheaderHalo⟩).trans hheader)
    ((hframe saved (hworkOff saved (by simp))).trans hsaved)
    ((hframe tmp (hworkOff tmp (by simp))).trans htmp) depth
  exact ⟨v₂,n₁+(10*B+10),hu₂.trans hu₁,Nat.add_le_add_right hn₁ _,mn_seq_within_add he₁ he₂⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CommonClassGeometry
