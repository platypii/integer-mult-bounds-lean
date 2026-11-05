module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingGeometryStock

/-! Execute the global binary-word producer from retained unary parameters.
Its sources live in the existing caller prefix, outside the typed header bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Fast.Main
  CommonClassGeometry ScalarPlacement ScalarPlacement.ComputedClassBanks PackedTranspose
noncomputable section
variable {T A D p u l target s t B W N radius width Vg Vr : ℕ}

def unarySource (T : ℕ) (k : Fin T) : Fin (MachineTapes T) := classCallerRegister (bank id k)

theorem unarySource_injective (T : ℕ) : Function.Injective (unarySource T) :=
  classCallerRegister_injective.comp (bank_injective id Function.injective_id)

theorem unarySource_ne_seed (T : ℕ) (k : Fin T) (r : TblR 13) :
    unarySource T k ≠ seedReg T r :=
  (commonSeedReg_off_prefix r (Fin.castAdd 175 (bank id k))).symm

def globalCopies (T : ℕ) (src : Fin 11 → Fin T) : List (Fin (MachineTapes T) × Fin (MachineTapes T)) :=
  List.ofFn fun i => (unarySource T (src i),globals T i)

def globalsLoaded (D : ℕ) (src : Fin 11 → Fin T) (S : Stacks (MachineTapes T) A) : Stacks (MachineTapes T) A :=
  {S with R := binaryHeaderBankR D (fun k => (S.R k).length) S.R (globalCopies T src)}

def globalConversionCost (D p u l target s t B W N radius width : ℕ) : ℕ :=
  (List.ofFn (fun i : Fin 11 => globalValues p u l target s t B W N radius width i*(4*D+10)+4*D+8)).sum+1

theorem globalCopies_nodup (T : ℕ) (src : Fin 11 → Fin T) : ((globalCopies T src).map Prod.snd).Nodup := by
  rw [globalCopies,List.map_ofFn,List.nodup_ofFn]
  exact globals_injective T

theorem globalsLoaded_header (src : Fin 11 → Fin T) (S : Stacks (MachineTapes T) A) (r : Role)
    (hr : ∀ i, r ≠ .scalar i) :
    (globalsLoaded D src S).R (fullHeader T r) = S.R (fullHeader T r) := by
  apply binaryHeaderBankR_off
  intro q hq
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
  exact (fullHeader_injective T).ne (hr i)

theorem globalsLoaded_unarySource (src : Fin 11 → Fin T) (S : Stacks (MachineTapes T) A) (k : Fin T) :
    (globalsLoaded D src S).R (unarySource T k) = S.R (unarySource T k) := by
  apply binaryHeaderBankR_off
  intro q hq
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
  exact (fullHeader_ne_bank id (.scalar i) k).symm

/-- Only ordinary unary parameters and fresh destination words are assumed;
the complete binary scalar bank is the actual returned execution state. -/
theorem prepareGlobals_exec_within {Q : ℕ} {P U : Type}
    (body : P → Pr P (MachineTapes T) Q A U)
    (src : Fin 11 → Fin T) (widthSource : Fin T) (hwidthOff : ∀ i, src i ≠ widthSource)
    (v : HS (MachineTapes T) Q A U) (S : Stacks (MachineTapes T) A)
    (hwidth : (S.R (unarySource T widthSource)).length = D)
    (hvalues : ∀ i, (S.R (unarySource T (src i))).length = globalValues p u l target s t B W N radius width i)
    (hblank : ∀ i, S.R (globals T i) = [])
    (hsaved : S.R (seedReg T (.z 0)) = []) (htmp : S.R (seedReg T (.z 1)) = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ globalConversionCost D p u l target s t B W N radius width ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        3*globalConversionCost D p u l target s t B W N radius width) depth
        (binaryHeaderBank (unarySource T widthSource) (seedReg T (.z 0)) (seedReg T (.z 1))
          (seedReg T (.z 2)) (globalCopies T src))
        (Host.mk v S) n (Host.mk v' (globalsLoaded D src S)) := by
  have hregs : ∀ q ∈ globalCopies T src,
      [q.1,unarySource T widthSource,q.2,seedReg T (.z 0),seedReg T (.z 1)].Nodup := by
    intro q hq
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
    have hsrc := (unarySource_injective T).ne (hwidthOff i)
    have hs : unarySource T (src i) ≠ globals T i := (fullHeader_ne_bank id (.scalar i) (src i)).symm
    have hw : unarySource T widthSource ≠ globals T i := (fullHeader_ne_bank id (.scalar i) widthSource).symm
    have hz : ∀ r, globals T i ≠ seedReg T r := fullHeader_ne_seed T (.scalar i)
    have hs₀ := unarySource_ne_seed T (src i)
    have hw₀ := unarySource_ne_seed T widthSource
    have hn := (seedReg_injective T).ne (show (TblR.z 0 : TblR 13) ≠ .z 1 by decide)
    simp [List.nodup_cons,hsrc,hs,hw,hz,hs₀,hw₀,hn]
  have hsep : ∀ q ∈ globalCopies T src, ∀ r ∈ globalCopies T src, q.2 ≠ r.1 := by
    intro q hq r hr
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hr
    exact fullHeader_ne_bank id (.scalar i) (src j)
  have hcost : binaryHeaderBankCost D (fun k => (S.R k).length) (globalCopies T src) =
      globalConversionCost D p u l target s t B W N radius width := by
    unfold binaryHeaderBankCost globalConversionCost globalCopies
    rw [List.map_ofFn]
    congr 2
    apply congrArg List.ofFn
    funext i
    change (S.R (unarySource T (src i))).length*(4*D+10)+4*D+8 = _
    rw [hvalues i]
  obtain ⟨v',n,hu,hn,he⟩ := binaryHeaderBank_exec (body := body)
    (unarySource T widthSource) (seedReg T (.z 0)) (seedReg T (.z 1)) (seedReg T (.z 2))
    (globalCopies T src) (globalCopies_nodup T src) hregs hsep D (fun k => (S.R k).length) v S
    hwidth (fun _ _ => rfl)
    (by intro q hq; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq; exact hblank i) hsaved htmp
  rw [hcost] at hn
  exact ⟨v',n,hu,hn,mn_native_exec_within he 3 (binaryHeaderBank_native _ _ _ _ _) depth _ (by omega)⟩

/-- The ordinary setup contract is established by the generated global words.
Rulers and fresh owned/routing storage are preserved by the conversion. -/
theorem setupInput_of_globalsLoaded (src : Fin 11 → Fin T) (S : Stacks (MachineTapes T) A)
    (hvalues : ∀ i, (S.R (unarySource T (src i))).length = globalValues p u l target s t B W N radius width i)
    (hrulers : ∀ f, (S.R (rulers T f)).length = formatWidths B Vg Vr f)
    (howned : ∀ r ∈ ownedRoles, S.R (fullHeader T r) = [])
    (hzero : S.R (fullHeader T .zero) = [])
    (hrouting : ∀ i, S.R (Fin.natAdd ((T+headerCount)+175) i) = []) :
    SetupInput T A D p u l target s t B W N radius width Vg Vr (globalsLoaded D src S) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i
    change binaryHeaderBankR D (fun k => (S.R k).length) S.R (globalCopies T src) (globals T i) = _
    rw [binaryHeaderBankR_at _ _ _ _ (globalCopies_nodup T src)
      (unarySource T (src i),globals T i) (List.mem_ofFn.mpr ⟨i,rfl⟩),hvalues i]
  · intro f
    rw [show rulers T f = fullHeader T (.ruler f) from rfl,
      globalsLoaded_header src S (.ruler f) (by intro i h; cases h)]
    exact hrulers f
  · intro r hr
    rw [globalsLoaded_header src S r (fun i => (retained_ne_owned (.scalar i) rfl r hr).symm)]
    exact howned r hr
  · rw [globalsLoaded_header src S .zero (by intro i h; cases h)]
    exact hzero
  · intro i
    change binaryHeaderBankR D (fun k => (S.R k).length) S.R (globalCopies T src)
      (Fin.natAdd ((T+headerCount)+175) i) = []
    rw [binaryHeaderBankR_off]
    · exact hrouting i
    · intro q hq
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hq
      exact (prefix_ne_routing (Fin.castAdd 175 (header T (.scalar j))) i).symm

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
