module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerCanonicalInputCopy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerSolverReady

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv ScalarPlacement CommonClassGeometry
  IntegerMultBounds.NLogN
variable {T Q A s : ℕ} [NeZero s] {P U : Type}
noncomputable section

def callerSeededInputPreparation (src : Fin 11 → Fin T) : Pr P (MachineTapes (T+solverRegisterCount)) Q A U :=
  .seq (callerInputMastersProgram src)
    (.seq (callerCanonicalInputCopyProgram src) (clearWords (List.ofFn (callerInputMaster T))))

noncomputable def callerInputMasterRetireCost (p u l target s t : ℕ) [NeZero s] : ℕ :=
  2*((List.ofFn (inverseMasterValues p u l target s t 0 s)).sum)+21

/-- From ordinary caller rulers and a borrowed scalar width, execute master
generation, canonical RHS isolation, and retirement of all exported masters.
Only the isolated RHS survives; no prepared width or count is an input. -/
theorem callerSeededInputPreparation_exec
    (body : P → Pr P (MachineTapes (T+solverRegisterCount)) Q A U)
    (src : Fin 11 → Fin T) (hs : Function.Injective src)
    (p u l target t radius width : ℕ) (hst : s < t)
    (hband : PhaseCellBand.width p u ≤ s) (Fs : List (ZMod s → GaussianInt))
    (tail : List (Fin (A+4))) (v : HS (MachineTapes (T+solverRegisterCount)) Q A U)
    (S : Stacks (MachineTapes (T+solverRegisterCount)) A)
    (hraw : ∀ i, (S.R (unarySource _ (solverSource (src i)))).length =
      globalValues p u l target s t (inverseCallerWordWidth p u l target s t)
        (packedHaloCommonWidth p l s u (target+1) 2) Fs.length radius width i)
    (hzero : S.R (fullHeader _ .zero) = [])
    (hwidth : S.R (solverRegister T (.input (familyInverseScalarReg .wr))) =
      List.replicate (inverseCallerWordWidth p u l target s t) tick)
    (hblank : ∀ r : SolverRole, r ≠ .input (familyInverseScalarReg .wr) → S.R (solverRegister T r) = [])
    (hsrc : S.R (fullHeader _ .input) = cstream A (packedHaloCommonWidth p l s u (target+1) 2)
      (Fs.map (chirpLine s)).flatten++tail) (depth : ℕ) :
    let d := InverseMasterInput.ofCuts p u l target t 0 s hst (Nat.zero_le _) le_rfl hband
    let copyCost := callerCanonicalInputCopyCost p u l target s t Fs.length
    ∃ v' n, v'.user = v.user ∧ n ≤ d.timeCost+copyCost+callerInputMasterRetireCost p u l target s t ∧
      ExecWithin body (fun k z => mnSize z+k ≤ mnSize (mk v S)+depth+d.stock+8*copyCost) depth
        (callerSeededInputPreparation src) (mk v S) n
        (mk v' {S with R := (Function.update S.R (solverRegister T (.scratch 4))
          (cstream A (inverseFullInputWidth p u l target s t) (Fs.map (chirpLine s)).flatten))}) := by
  let d := InverseMasterInput.ofCuts p u l target t 0 s hst (Nat.zero_le _) le_rfl hband
  let copyCost := callerCanonicalInputCopyCost p u l target s t Fs.length
  obtain ⟨v₁,F,n₁,hu₁,hn₁,he₁,hheads,hI,hO,hL,hframe⟩ := callerInputMasters_exec body src p u l target t hst hband v S
    (solverParameter_lengths src p u l target t _ _ _ radius width S hraw hzero) hwidth
    (by intro i hi; exact hblank _ (by intro he; exact hi (SolverRole.input.inj he)))
    (by intro i; exact hblank _ (by intro he; cases he)) depth
  have hrawF (i) : F.R (unarySource _ (solverSource (src i))) = S.R (unarySource _ (solverSource (src i))) :=
    hframe _ (fun j => solverRegister_ne_source T (.input (familyInverseMasterPort j)) (src i))
  have hsrcF : F.R (fullHeader _ .input) = S.R (fullHeader _ .input) :=
    hframe _ (fun i => solverRegister_ne_header T (.input (familyInverseMasterPort i)) .input)
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := callerCanonicalInputCopy_exec body src hs p u l target t Fs tail v₁ F
    (by rw [hrawF]; simpa [globalValues] using hraw 8)
    (by rw [hrawF]; simpa [globalValues] using hraw 4)
    (by rw [hrawF]; simpa [globalValues] using hraw 7)
    (by rw [hheads,List.length_replicate]) (hsrcF.trans hsrc)
    (by
      intro r hm hr
      exact (hframe _ (fun i => (solverRegister_injective T).ne (Ne.symm (hm i)))).trans (hblank r hr))
  let xs := cstream A (inverseFullInputWidth p u l target s t) (Fs.map (chirpLine s)).flatten
  let dst := solverRegister T (.scratch 4)
  let headers := List.ofFn (callerInputMaster T)
  have hdst : dst ∉ headers := by
    intro hm
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp hm
    have he := solverRegister_injective T hi
    cases he
  obtain ⟨v₃,hu₃,he₃⟩ := retireHeaderFrame_pair_exec body headers
    (List.nodup_ofFn_ofInjective (callerInputMaster_injective T)) S F hI hO hL
    (by intro k hk; exact hframe k (fun i hi => hk (List.mem_ofFn.mpr ⟨i,hi⟩)))
    (by
      intro k hk
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hk
      exact hblank _ (by
        intro he
        exact familyInverseScalarReg_master i .wr (SolverRole.input.inj he).symm))
    dst dst hdst hdst xs xs v₂ depth
  simp only [Function.update_idem] at he₃
  have hcost : 2*(headers.map (fun i => (F.R i).length)).sum+2*headers.length+1 =
      callerInputMasterRetireCost p u l target s t := by
    simp only [headers,List.map_ofFn,Function.comp_def,hheads,List.length_replicate,List.length_ofFn,
      callerInputMasterRetireCost]
  rw [hcost] at he₃
  have he₂w := mn_native_exec_within he₂ 8 (canonicalInputCopy_native ..) depth
    (mnSize (mk v₁ F)+depth+8*copyCost) (by dsimp only [copyCost]; omega)
  have hF := he₁.final
  have hH := he₂w.final
  let bound := fun (k : ℕ) (z : Store (HΓ (T := MachineTapes (T+solverRegisterCount)) A)
    (HS (MachineTapes (T+solverRegisterCount)) Q A U)) =>
      mnSize z+k ≤ mnSize (mk v S)+depth+d.stock+8*copyCost
  have e₁ : ExecWithin body bound depth _ _ _ _ := he₁.mono (by
    intro k z hz
    dsimp only [bound,d]
    omega)
  have e₂ : ExecWithin body bound depth _ _ _ _ := he₂w.mono (by
    intro k z hz
    dsimp only [bound,d]
    omega)
  have e₃ : ExecWithin body bound depth _ _ _ _ := he₃.mono (by
    intro k z hz
    dsimp only [bound,d,xs,dst] at hz ⊢
    omega)
  exact ⟨v₃,n₁+(n₂+callerInputMasterRetireCost p u l target s t),hu₃.trans (hu₂.trans hu₁),
    by dsimp only [copyCost] at *; omega,ExecWithin.seq e₁ (ExecWithin.seq e₂ e₃)⟩

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
