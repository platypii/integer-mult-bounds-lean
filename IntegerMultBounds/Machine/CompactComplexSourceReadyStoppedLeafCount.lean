import IntegerMultBounds.Machine.CompactComplexSourceReadyStoppedLeafBudget

/-! Positive-exponent source-ready nodes store per-child count in header7.
This actual adapter expands by retained arity before the leaf and restores the
count after live commit; exponent-zero leaves use the unchanged scalar body. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyStoppedLeafCount
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry
open CompactComplexSourceReadyLeafCodec (headers numericProgram numeric_runs headers_active headers_headers headers_original)
open CompactComplexSourceReadyStoppedLeaf (publicTapes ready)
open CompactComplexNonleafRoleSourceReturn (base)
open CompactComplexNonleafRoleEntry (headerPlacement)
open CompactSpectatorLeafGuardOriginal (Direction)
open CompactSpectatorLeafCountBudget (expand restore expanded)
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)
variable {s c : ℕ}

private theorem current_outside (j : Fin 43) :
    CompactComplexNonleafRoleChildBank.current (s:=s) (c:=c)≠CompactComplexSourceReadyLeafCodec.slot (s:=10+s) j := by
  intro h
  have hv := congrArg Fin.val h
  have hj := j.isLt
  simp only [CompactComplexNonleafRoleChildBank.current,CompactComplexNonleafRoleChildBank.storage,
    CompactComplexSourceReadyLeafCodec.slot,CompactComplexNonleafRoleEntry.numeric,
    CompactComplexNativeCodecFrame.headerSlot,CompactComplexSpectatorTargetBank.oldSlot,
    CompactComplexControllerNativeFrame.storageSlot,CompactComplexControllerNativeFrame.nativeSlot,
    Fin.val_castAdd,Fin.val_natAdd] at hv
  omega
private theorem target_outside (j : Fin 43) :
    CompactComplexNonleafRoleChildBank.target (s:=s) (c:=c)≠CompactComplexSourceReadyLeafCodec.slot (s:=10+s) j := by
  intro h
  have hv := congrArg Fin.val h
  have hj := j.isLt
  simp only [CompactComplexNonleafRoleChildBank.target,CompactComplexNonleafRoleChildBank.storage,
    CompactComplexSourceReadyLeafCodec.slot,CompactComplexNonleafRoleEntry.numeric,
    CompactComplexNativeCodecFrame.headerSlot,CompactComplexSpectatorTargetBank.oldSlot,
    CompactComplexControllerNativeFrame.storageSlot,CompactComplexControllerNativeFrame.nativeSlot,
    Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

private theorem replace_setTape {n u t a : ℕ} (e : Fin (n+u) ≃ Fin t)
    (v : Tapes t a) (small : Tapes n a) (i : Fin t)
    (hi : ∀ j,i≠e (Fin.castAdd u j)) (f : ℤ → Fin (a+4)) (p : ℤ) :
    Placement.replace e (setTape v i f p) small=setTape (Placement.replace e v small) i f p := by
  obtain ⟨j,rfl⟩ := e.surjective i
  induction j using Fin.addCases with
  | left j => exact False.elim (hi j rfl)
  | right j =>
    apply congrArg₂ Tapes.mk <;> funext k
    all_goals obtain ⟨k,rfl⟩ := e.surjective k
    all_goals induction k using Fin.addCases with
    | left k =>
      have hn : e (Fin.castAdd u k)≠e (Fin.natAdd n j) := by
        intro h;have hv := congrArg Fin.val (e.injective h);simp only [Fin.val_castAdd,Fin.val_natAdd] at hv;omega
      simp [Placement.replace,Placement.combine,Tapes.reindex,Tapes.append,setTape,hn]
    | right k =>
      by_cases hk : k=j
      · subst k;simp [Placement.replace,Placement.combine,Placement.extra,Tapes.reindex,Tapes.append,setTape]
      · have hn : e (Fin.natAdd n k)≠e (Fin.natAdd n j) := fun h => hk (Fin.natAdd_injective _ _ (e.injective h))
        simp [Placement.replace,Placement.combine,Placement.extra,Tapes.reindex,Tapes.append,setTape,hn]

private theorem headers_setTape (v : Tapes (publicTapes s c) 2)
    (st : ActiveRepairRankHeadersCommands.State) (i : Fin (publicTapes s c))
    (hi : ∀ j,i≠CompactComplexSourceReadyLeafCodec.slot (s:=10+s) j) (f : ℤ → Fin 6) (p : ℤ) :
    headers (setTape v i f p) st=setTape (headers v st) i f p :=
  replace_setTape CompactComplexSourceReadyLeafCodec.placement v _ i
    (by intro j;simpa only [CompactComplexSourceReadyLeafCodec.placement,InjectivePlacement.active_slot] using hi j) f p

private theorem active_setTape (v : Tapes (publicTapes s c) 2) (i : Fin (publicTapes s c))
    (hi : ∀ j,i≠CompactComplexSourceReadyLeafCodec.slot (s:=10+s) j) (f : ℤ → Fin 6) (p : ℤ) :
    Placement.active headerPlacement (base (setTape v i f p))=Placement.active headerPlacement (base v) := by
  rw [←CompactComplexSourceReadyLeafCodec.active,←CompactComplexSourceReadyLeafCodec.active]
  apply congrArg₂ Tapes.mk <;> funext j <;>
    simp only [CompactComplexSourceReadyLeafCodec.placement,InjectivePlacement.active_slot,setTape,
      Function.update_of_ne (hi j).symm]

def returned (v : Tapes (publicTapes s c) 2) (f : ℤ → Fin 6) (n : ℕ) :=
  setTape (setTape (setTape v (CompactComplexSourceReadyLeafPhase.source (s:=10+s)) f 0)
    CompactComplexNonleafRoleChildBank.current (RadixZeroFill.encodedBinary (bits n)) 1)
    CompactComplexNonleafRoleChildBank.target (fun _ => blank) 0

theorem returned_headers (v : Tapes (publicTapes s c) 2) (f : ℤ → Fin 6) (n : ℕ) :
    Placement.active headerPlacement (base (returned v f n))=Placement.active headerPlacement (base v) := by
  unfold returned
  rw [active_setTape _ _ target_outside,active_setTape _ _ current_outside,
    CompactComplexSourceReadyLeafCodec.active_set_source]

theorem headers_returned (v : Tapes (publicTapes s c) 2) (st : ActiveRepairRankHeadersCommands.State)
    (f : ℤ → Fin 6) (n : ℕ) : headers (returned v f n) st=returned (headers v st) f n := by
  unfold returned
  rw [headers_setTape _ _ _ target_outside,headers_setTape _ _ _ current_outside,
    CompactComplexSourceReadyLeafCodec.headers_set_source]

def countProgram (ops : List CompactChildHeadersArithmetic.Op) :=
  extend (extend (numericProgram (s:=10+s) (c:=c) (CompactChildHeadersArithmetic.compile (a:=2) ops).2)
    CompactComplexSourceReadyLeafPhase.privateTapes) 10

def program (dir : Direction) := seq (seq (countProgram (s:=s) (c:=c) expand)
  (CompactComplexSourceReadyStoppedLeaf.program (s:=s) (c:=c) dir)) (countProgram (s:=s) (c:=c) restore)

def cost (dir : Direction) (sh : Shape) (rows ell p : ℕ) (rho : Fin sh.chunk)
    {left k : ℕ} (visit : Visit sh.active left (k+1)) (right src dst n : ℕ) :=
  let st := CompactSpectatorLeafSetup.raw sh rows ell p rho.val left (arity^k) arity right src dst
  CompactChildHeadersArithmetic.scheduleCost expand st+
    CompactComplexSourceReadyStoppedLeafBudget.fullCost dir sh rows ell p rho visit arity right src dst n+
    CompactChildHeadersArithmetic.scheduleCost restore (expanded st arity (arity^k))+2

/-- Actual positive node input retains per-child header7. The physical adapter
expands it for whole-node execution and restores that same word afterwards. -/
theorem runs (dir : Direction) (sh : Shape) (rows ell p : ℕ) (rho : Fin sh.chunk)
    {left k : ℕ} (visit : Visit sh.active left (k+1)) (right src dst n : ℕ)
    (v : Tapes (publicTapes s c) 2)
    (f : CompactSpectatorVisitGeometry.Array (NativePolynomialStageShape.shape sh ell p) rows ell)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hr : 0<rows) (hp : 2*sh.bits≤p)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (hraw : Placement.active headerPlacement (base v)=ActiveRepairRankHeadersCommands.bank
      (CompactSpectatorLeafSetup.raw sh rows ell p rho.val left (arity^k) arity right src dst))
    (hsource : v.head (CompactComplexSourceReadyLeafPhase.source (s:=10+s))=0 ∧
      v.tape (CompactComplexSourceReadyLeafPhase.source (s:=10+s))=CompactSpectatorLeafAxis.word f)
    (hlive : v.head CompactComplexNonleafRoleChildBank.current=1 ∧
      v.tape CompactComplexNonleafRoleChildBank.current=RadixZeroFill.encodedBinary (bits n))
    (htarget : v.head CompactComplexNonleafRoleChildBank.target=0 ∧
      v.tape CompactComplexNonleafRoleChildBank.target=(fun _ => blank)) :
    HoareTime (program dir) (fun z => z=ready v)
      (fun z => z=ready (returned v (CompactSpectatorLeafAxis.word
        (CompactSpectatorLeafGuardOriginal.result dir (NativePolynomialStageShape.shape sh ell p)
          rows ell (p-2*sh.bits) rho visit f)) (CompactComplexDenominatorPolicy.leafTarget n (k+1))))
      (cost dir sh rows ell p rho visit right src dst n) := by
  let st := CompactSpectatorLeafSetup.raw sh rows ell p rho.val left (arity^k) arity right src dst
  let ex := expanded st arity (arity^k)
  let g := CompactSpectatorLeafAxis.word (CompactSpectatorLeafGuardOriginal.result dir
    (NativePolynomialStageShape.shape sh ell p) rows ell (p-2*sh.bits) rho visit f)
  let targetN := CompactComplexDenominatorPolicy.leafTarget n (k+1)
  have heq : ex=CompactSpectatorLeafSetup.raw sh rows ell p rho.val left (arity^(k+1)) arity right src dst := by
    funext i
    fin_cases i <;> simp [ex,st,expanded,CompactSpectatorLeafSetup.raw,ActiveRepairRankHeadersCommands.put,pow_succ]
  have he := CompactSpectatorLeafCountBudget.expand_runs (a:=2) st arity (arity^k) rfl rfl rfl (pow_pos (by decide) _)
  have h0 := hoare_extend_eq (hoare_extend_eq (numeric_runs _ v st ex _ hraw he)
    (SharedBank.empty CompactComplexSourceReadyLeafPhase.privateTapes 2)) (SharedBank.empty 10 2)
  have hs : (headers v ex).head (CompactComplexSourceReadyLeafPhase.source (s:=10+s))=0 ∧
      (headers v ex).tape (CompactComplexSourceReadyLeafPhase.source (s:=10+s))=CompactSpectatorLeafAxis.word f := by
    rw [(CompactComplexSourceReadyLeafCodec.headers_source v ex).1,(CompactComplexSourceReadyLeafCodec.headers_source v ex).2]
    exact hsource
  have hn := CompactComplexSourceReadyLeafCodec.headers_frame v ex CompactComplexNonleafRoleChildBank.current current_outside
  have ht := CompactComplexSourceReadyLeafCodec.headers_frame v ex CompactComplexNonleafRoleChildBank.target target_outside
  have h1 := CompactComplexSourceReadyStoppedLeaf.runs dir sh rows ell p rho visit arity right src dst n
    (headers v ex) f hG hA hr hp hw (by rw [headers_active,heq]) hs
    ⟨hn.1.trans hlive.1,hn.2.trans hlive.2⟩ ⟨ht.1.trans htarget.1,ht.2.trans htarget.2⟩
  rw [CompactComplexSourceReadyStoppedLeaf.output_eq_ready] at h1
  have hrst := CompactSpectatorLeafCountBudget.restore_runs (a:=2) st arity (arity^k) rfl rfl rfl (by decide : 0<arity)
  have h2 := hoare_extend_eq (hoare_extend_eq (numeric_runs _ (returned (headers v ex) g targetN) ex st _
    ((returned_headers _ _ _).trans (headers_active _ _)) hrst)
    (SharedBank.empty CompactComplexSourceReadyLeafPhase.privateTapes 2)) (SharedBank.empty 10 2)
  rw [headers_returned,headers_headers,headers_original v st hraw] at h2
  exact ((h0.seq h1).seq h2).consequence (fun _ hz => hz) (fun _ hz => hz) (by dsimp only [cost,CompactComplexSourceReadyStoppedLeafBudget.fullCost,st,ex] at *;omega)

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyStoppedLeafCount
