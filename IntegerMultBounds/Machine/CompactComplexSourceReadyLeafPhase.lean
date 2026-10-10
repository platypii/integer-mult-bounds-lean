import IntegerMultBounds.Machine.CompactComplexNonleafRoleSourceReturn
import IntegerMultBounds.Machine.CompactNativeRoleChildPrecisionSaved

/-! Direct directional leaf execution consumes the actual source-ready bank.
The source and retained baseline numeric descriptors are the only public ports;
all controller, role, ancestor and seven private tapes remain framed. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyLeafPhase
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry
open CompactComplexNonleafRoleEntry (numeric headerPlacement)
open CompactComplexNonleafRoleSourceReturn (base)
open CompactSpectatorLeafGuardOriginal (Direction)
open SharedPlacementAlphabet (setTape)
variable {s c : ℕ}

abbrev publicTapes (s c : ℕ) := CompactComplexNonleafRoleSourceReturn.tapes s c
abbrev privateTapes := CompactSpectatorLeafOriginal.tapes
abbrev tapes (s c : ℕ) := publicTapes s c+privateTapes

def source : Fin (publicTapes s c) := Fin.castAdd 7 CompactComplexNonleafRoleEntry.source
def descriptor (j : Fin 15) : Fin (publicTapes s c) :=
  Fin.castAdd 7 (numeric (Fin.castAdd 15 (CompactSpectatorLeafOriginal.destination j)))
def common : Fin (1+15) → Fin (publicTapes s c) :=
  Fin.addCases (fun _ => source) descriptor

private theorem numeric_injective : Function.Injective (numeric (s:=s) (c:=c)) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [numeric,CompactComplexNativeCodecFrame.headerSlot,
    CompactComplexControllerNativeFrame.nativeSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

private theorem source_numeric (i : Fin 43) :
    CompactComplexNonleafRoleEntry.source (s:=s) (c:=c) ≠ numeric i := by
  intro h
  have hv := congrArg Fin.val h
  have hi := i.isLt
  simp only [CompactComplexNonleafRoleEntry.source,CompactComplexSpectatorTargetBank.numericSlot,numeric,
    CompactComplexNativeCodecFrame.headerSlot,CompactComplexControllerNativeFrame.nativeSlot,
    Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

theorem common_injective : Function.Injective (common (s:=s) (c:=c)) := by
  intro i j h
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j => exact congrArg (Fin.castAdd 15) (Subsingleton.elim i j)
    | right j =>
      simp only [common,Fin.addCases_left,Fin.addCases_right,source,descriptor] at h
      exact False.elim (source_numeric _ (Fin.castAdd_injective _ _ h))
  | right i =>
    induction j using Fin.addCases with
    | left j =>
      simp only [common,Fin.addCases_left,Fin.addCases_right,source,descriptor] at h
      exact False.elim (source_numeric _ (Fin.castAdd_injective _ _ h.symm))
    | right j =>
      simp only [common,Fin.addCases_right,descriptor] at h
      apply congrArg (Fin.natAdd 1)
      exact CompactSpectatorLeafOriginal.destination_injective
        (Fin.castAdd_injective _ _ (numeric_injective (Fin.castAdd_injective _ _ h)))

def program (dir : Direction) := Placement.placed
  (CompactSpectatorLeafGuardOriginal.phaseProgram dir)
  (CleanSubbank.placement CompactSpectatorLeafPlacement.ports (common (s:=s) (c:=c)) common_injective)

def ready (v : Tapes (publicTapes s c) 2) := v.append (SharedBank.empty privateTapes 2)
def output (v : Tapes (publicTapes s c) 2) (f : ℤ → Fin 6) := ready (setTape v source f 0)

private theorem numeric_active (i : Fin 43) :
    headerPlacement (s:=s) (c:=c)
      (Fin.castAdd (CompactComplexNonleafRoleEntry.tapes s c-43) i) = numeric i := by
  unfold headerPlacement
  exact InjectivePlacement.active_slot _ _ _ _

/-- Readiness is extracted from the actual raw baseline bank; saved codec and
corrected-precision words are outside all immutable leaf ports. -/
theorem actual_payload (sh : Shape) (rows ell q rho left count slots right src dst savedP savedPayload : ℕ)
    (v : Tapes (publicTapes s c) 2) (f : ℤ → Fin 6)
    (hraw : Placement.active headerPlacement (base v)=ActiveRepairRankHeadersCommands.bank
      (ActiveRepairRankHeadersCommands.put
        (ActiveRepairRankHeadersCommands.put
          (CompactSpectatorLeafSetup.raw sh rows ell q rho left count slots right src dst) 21 savedP)
        26 savedPayload))
    (hsource : v.head source=0 ∧ v.tape source=f) :
    SharedBank.payload v common=CompactSpectatorLeafPlacement.payload f
      (CompactSpectatorLeafOriginal.values sh rows ell q rho left count slots right src dst) := by
  have hn (i : Fin 43) := congrArg (fun z : Tapes 43 2 => (z.head i,z.tape i)) hraw
  simp only [Placement.active,numeric_active,base] at hn
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals induction i using Fin.addCases with
  | left i =>
    simp only [common,Fin.addCases_left,CountedLoopReuseAlphabet.one]
    first | exact hsource.1 | exact hsource.2
  | right i =>
    have hi := hn (Fin.castAdd 15 (CompactSpectatorLeafOriginal.destination i))
    fin_cases i
    all_goals simp only [common,descriptor,Fin.addCases_right,
      CompactSpectatorLeafOriginal.originals,CompactSpectatorLeafOriginal.values,
      CompactSpectatorLeafOriginal.destination] at hi ⊢
    all_goals first | exact congrArg Prod.fst hi | exact congrArg Prod.snd hi

private theorem payload_update {t n : ℕ} (v : Tapes t 2) (p : Fin n → Fin t)
    (hp : Function.Injective p) (i : Fin n) (f : ℤ → Fin 6) :
    SharedBank.payload (setTape v (p i) f 0) p=setTape (SharedBank.payload v p) i f 0 := by
  apply congrArg₂ Tapes.mk <;> funext j <;> by_cases hj : j=i <;>
    simp [SharedBank.payload,setTape,Function.update,hj,hp.eq_iff]

private theorem strip_update {t n : ℕ} (v : Tapes t 2) (p : Fin n → Fin t)
    (i : Fin n) (f : ℤ → Fin 6) :
    SharedBank.strip (setTape v (p i) f 0) p=SharedBank.strip v p := by
  apply congrArg₂ Tapes.mk <;> funext j <;> by_cases hj : ∃ i,p i=j
  all_goals simp only [hj,ite_true,ite_false]
  all_goals have hn : j≠p i := fun h => hj ⟨i,h.symm⟩
  all_goals simp [setTape,hn]

/-- One actual leaf, on its entered source rather than a selected parent role. -/
theorem runs (dir : Direction) (sh : Shape) (rows ell q : ℕ) (rho : Fin sh.chunk)
    {left k : ℕ} (visit : Visit sh.active left k)
    (slots right src dst savedP savedPayload : ℕ)
    (v : Tapes (publicTapes s c) 2) (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hr : 0<rows)
    (hw : ButterflySpectatorSemantics.Width rows sh.bits (2^ell) q f)
    (hraw : Placement.active headerPlacement (base v)=ActiveRepairRankHeadersCommands.bank
      (ActiveRepairRankHeadersCommands.put
        (ActiveRepairRankHeadersCommands.put
          (CompactSpectatorLeafSetup.raw sh rows ell q rho.val left (arity^k) slots right src dst) 21 savedP)
        26 savedPayload))
    (hsource : v.head source=0 ∧ v.tape source=CompactSpectatorLeafAxis.word f) :
    HoareTime (program dir) (fun z => z=ready v)
      (fun z => z=output v (CompactSpectatorLeafAxis.word
        (CompactSpectatorLeafGuardOriginal.result dir sh rows ell q rho visit f)))
      (CompactSpectatorLeafGuardOriginal.phaseCost dir sh rows ell q rho visit slots right src dst) := by
  let vs := CompactSpectatorLeafOriginal.values sh rows ell q rho.val left (arity^k) slots right src dst
  let g := CompactSpectatorLeafAxis.word (CompactSpectatorLeafGuardOriginal.result dir sh rows ell q rho visit f)
  have h := CompactSpectatorLeafGuardOriginal.phase_runs dir sh rows ell q rho visit slots right src dst hG hA hr f hw
  have hd := actual_payload sh rows ell q rho.val left (arity^k) slots right src dst savedP savedPayload v
    (CompactSpectatorLeafAxis.word f) hraw hsource
  apply CleanSubbank.realizes (CompactSpectatorLeafGuardOriginal.phaseProgram dir)
    CompactSpectatorLeafPlacement.ports common CompactSpectatorLeafPlacement.ports_injective common_injective
    v (setTape v source g 0)
    (CompactSpectatorLeafOriginal.bank (fun _ => none) (CompactSpectatorLeafAxis.word f) vs)
    (CompactSpectatorLeafOriginal.bank (fun _ => none) g vs) _
    ?_ ?_ (CompactSpectatorLeafPlacement.bank_clean _ _) (CompactSpectatorLeafPlacement.bank_clean _ _) ?_ h
  · rw [CompactSpectatorLeafPlacement.bank_payload]
    exact hd.symm
  · rw [CompactSpectatorLeafPlacement.bank_payload]
    have he : source (s:=s) (c:=c)=common (Fin.castAdd 15 (0 : Fin 1)) := rfl
    rw [he,payload_update _ _ common_injective,hd]
    unfold CompactSpectatorLeafPlacement.payload
    rw [SharedPlacementAlphabet.setTape_append_left]
    congr 1
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  · have he : source (s:=s) (c:=c)=common (Fin.castAdd 15 (0 : Fin 1)) := rfl
    rw [he,strip_update]

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyLeafPhase
