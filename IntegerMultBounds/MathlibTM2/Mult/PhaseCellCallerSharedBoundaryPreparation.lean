module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerCanonicalInputPreparation
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerSolverCarryFrame
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerPublishedPreparation
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryCallerReady

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  CommonClassGeometry ScalarPlacement ScalarPlacement.ComputedClassBanks PackedTranspose
  IntegerMultBounds.NLogN
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {T Q K D p u l target s t radius width Vg Vr : ℕ} [NeZero s] {P U : Type}

noncomputable def sharedBoundaryPreparationTime (p u l target s t D N radius width Vg Vr : ℕ) [NeZero s] : ℕ :=
  canonicalInputPreparationTime p u l target s t N+
    gatherPreparationCost D p u l target s t (inverseCallerWordWidth p u l target s t)
      (packedHaloCommonWidth p l s u (target+1) 2) N radius width Vg Vr

noncomputable def sharedBoundaryPreparationStock (p u l target s t D N radius width Vg Vr : ℕ) [NeZero s] : ℕ :=
  canonicalInputPreparationStock p u l target s t N+
    3*gatherPreparationCost D p u l target s t (inverseCallerWordWidth p u l target s t)
      (packedHaloCommonWidth p l s u (target+1) 2) N radius width Vg Vr

/-- Prepare both consumers from raw caller rulers and the common input stream.
The canonical RHS is copied first into reserved carry; shared caller setup then
produces numerical, gather, publication and boundary readiness together. -/
theorem prepareSharedBoundaryCaller_exec_within
    (body : P → Pr P (MachineTapes (T+solverRegisterCount)) Q (prime+K) U)
    (src : Fin 11 → Fin T) (widthSource : Fin T) (widths : Fin 3 → Fin T)
    (b : ComputedClassBank → Fin T) (Fs : List (ZMod s → GaussianInt))
    (borrowed : List (Fin (prime+K+4)))
    (v : HS (MachineTapes (T+solverRegisterCount)) Q (prime+K) U) (S : Stacks (MachineTapes (T+solverRegisterCount)) (prime+K))
    (raw : RawInput (T+solverRegisterCount) (prime+K) D p u l target s t (inverseCallerWordWidth p u l target s t) (packedHaloCommonWidth p l s u (target+1) 2) Fs.length radius width Vg Vr (solverSource ∘ src) (solverSource widthSource) (solverSource ∘ widths) S)
    (hword : S.R (fullHeader (T+solverRegisterCount) .word) = []) (hreplicas : S.R (fullHeader (T+solverRegisterCount) .replicas) = [])
    (hvolume : S.R (fullHeader (T+solverRegisterCount) .volume) = [])
    (hsource : S.R (fullHeader (T+solverRegisterCount) .input) = Fs.flatMap (fun C => cstream (prime+K) (packedHaloCommonWidth p l s u (target+1) 2) (chirpLine s C))++borrowed)
    (hexposure : ∀ i : Fin 175, S.R (Fin.castAdd tapeCount (Fin.natAdd ((T+solverRegisterCount)+headerCount) i)) = [])
    (houtput : S.R (fullExposedClassBank (bank (solverSource ∘ b)) (.control .source)) = [])
    (hroutingLeft : ∀ i : Fin tapeCount, S.L (Fin.natAdd (((T+solverRegisterCount)+headerCount)+175) i) = [])
    (hsourceLeft : S.L (control (fullExposedClassBank (bank (solverSource ∘ b))) .source) = [])
    (htable : ∀ r, S.R (numericTable (T+solverRegisterCount) r) = [])
    (hbank : ∀ j, j ≠ .control .source → S.R (fullExposedClassBank (bank (solverSource ∘ b)) j) = [])
    (hleft : ∀ j, S.L (recovery (fullExposedClassBank (bank (solverSource ∘ b))) (.work j)) = [])
    (hpubBlank : ∀ i : Fin 7, S.R (fullHeader (T+solverRegisterCount) (.publication i)) = [])
    (hresultLeft : S.L (fullExposedClassBank (bank (solverSource ∘ b)) (.recovery (.control .result))) = [])
    (hambientLeft : S.L (fullHeader (T+solverRegisterCount) .output) = []) (hs : Function.Injective src) (hst : s < t)
    (hband : PhaseCellBand.width p u ≤ s)
    (hsolver : ∀ r : SolverRole, S.R (solverRegister T r) = [])
    (hsolverLeft : ∀ r : SolverRole, S.L (solverRegister T r) = []) (depth : ℕ) :
    let W := packedHaloCommonWidth p l s u (target+1) 2
    let prepTime := sharedBoundaryPreparationTime p u l target s t D Fs.length radius width Vg Vr
    let prepStock := sharedBoundaryPreparationStock p u l target s t D Fs.length radius width Vg Vr
    ∃ v' F, ∃ input : SetupInput (T+solverRegisterCount) (prime+K) D p u l target s t (inverseCallerWordWidth p u l target s t) (packedHaloCommonWidth p l s u (target+1) 2) Fs.length radius width Vg Vr F,
      v'.user = v.user ∧
      (∀ clipped, (makeSetup input clipped raw.widthPositive raw.geometryFit raw.fit raw.bitsFit).NumericalInput
        (fullExposedClassBank (bank (solverSource ∘ b))) (numericTable (T+solverRegisterCount)) (geometrySources (T+solverRegisterCount)) (masterSources (T+solverRegisterCount))) ∧
      GatherRetainedInput (T+solverRegisterCount) K s (packedHaloCommonWidth p l s u (target+1) 2) (solverSource ∘ b) Fs borrowed F ∧
      PublicationCallerReady (classCallerRegister ∘ publication (T+solverRegisterCount))
        (selectedPublicationPlacement (bank (solverSource ∘ b)) (header (T+solverRegisterCount) .output)) F ∧
      (∀ f i, F.R (fullHeader (T+solverRegisterCount) (.geometry f i)) = binSyms (formatWidths (inverseCallerWordWidth p u l target s t) Vg Vr f) (![s,width,radius] i)) ∧
      BoundaryCallerReady src (solverSource widthSource) p u l target t W D radius width Fs F ∧
      F.L = S.L ∧ F.inp = S.inp ∧ F.out = S.out ∧
      (∀ k, k ≠ solverRegister T (.scratch 4) → k ≠ fullHeader (T+solverRegisterCount) .word → k ≠ fullHeader (T+solverRegisterCount) .replicas → k ≠ fullHeader (T+solverRegisterCount) .volume →
        (∀ i, k ≠ globals (T+solverRegisterCount) i) → (∀ f, k ≠ rulers (T+solverRegisterCount) f) →
        (∀ f i, k ≠ fullHeader (T+solverRegisterCount) (.geometry f i)) → F.R k = S.R k) ∧
      ∃ n, n ≤ prepTime ∧
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
          prepStock) depth
          (.seq (callerCanonicalInputPreparation src)
            (gatherPreparationProgram (solverSource ∘ src) (solverSource widthSource) (solverSource ∘ widths))) (Host.mk v S) n (Host.mk v' F) := by
  let W := packedHaloCommonWidth p l s u (target+1) 2
  let rhs := cstream (prime+K) (inverseFullInputWidth p u l target s t) (Fs.map (chirpLine s)).flatten
  let M := solverCarryState S rhs
  have hstream : ∀ Gs : List (ZMod s → GaussianInt),
      cstream (prime+K) W (Gs.map (chirpLine s)).flatten =
        Gs.flatMap (fun F => cstream (prime+K) W (chirpLine s F)) := by
    intro Gs
    induction Gs with
    | nil => rfl
    | cons G Gs ih => simp only [List.map_cons,List.flatten_cons,cstream_append,List.flatMap_cons,ih]
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := callerCanonicalInputPreparation_exec body src hs p u l target t radius width
    hst hband Fs borrowed v S raw.values raw.zeroBlank hsolver (by exact hsource.trans (congrArg (fun xs => xs++borrowed) (hstream Fs).symm)) depth
  have rawM := raw.solverCarry rhs
  obtain ⟨v₂,F,input,hu₂,numerical,retained,pubReady,hwords,hL,hI,hO,hframe,n₂,hn₂,he₂⟩ :=
    prepareSharedPublishedCaller_exec_within body (solverSource ∘ src) (solverSource widthSource) (solverSource ∘ widths)
      (solverSource ∘ b) Fs borrowed v₁ M rawM
      (by simpa only [M,solverCarryState_header] using hword)
      (by simpa only [M,solverCarryState_header] using hreplicas)
      (by simpa only [M,solverCarryState_header] using hvolume)
      (by simpa only [M,solverCarryState_header] using hsource)
      (by intro i; simpa only [M,solverCarryState_exposure] using hexposure i)
      (by simpa only [M,solverCarryState_numerical] using houtput)
      hroutingLeft hsourceLeft
      (by intro r; exact (solverCarryState_header S rhs (tableRole r)).trans (htable r))
      (by intro j hj; exact (solverCarryState_numerical S rhs b j).trans (hbank j hj))
      hleft (by intro i; exact (solverCarryState_header S rhs (.publication i)).trans (hpubBlank i))
      hresultLeft hambientLeft depth
  have hprefix (k) (hk : ∀ r, k ≠ fullHeader (T+solverRegisterCount) r) : F.R k = M.R k :=
    hframe k (hk .word) (hk .replicas) (hk .volume) (fun i => hk (.scalar i))
      (fun f => hk (.ruler f)) (fun f i => hk (.geometry f i))
  have hreserved (r : SolverRole) : F.R (solverRegister T r) = M.R (solverRegister T r) :=
    hprefix _ (solverRegister_ne_header T r)
  have hrawF (i : Fin T) : F.R (unarySource _ (solverSource i)) = S.R (unarySource _ (solverSource i)) :=
    (hprefix _ (fun r => (fullHeader_ne_bank id r (solverSource i)).symm)).trans (solverCarryState_raw S rhs i)
  have hpubF (i : Fin 7) : F.R (fullHeader _ (.publication i)) = S.R (fullHeader _ (.publication i)) := by
    rw [hframe]
    · exact solverCarryState_header S rhs (.publication i)
    all_goals first
      | exact (fullHeader_injective _).ne (by intro he; cases he)
      | intro j; exact (fullHeader_injective _).ne (by intro he; cases he)
      | intro f j; exact (fullHeader_injective _).ne (by intro he; cases he)
  have boundary : BoundaryCallerReady src (solverSource widthSource) p u l target t W D radius width Fs F := by
    refine ⟨?_,input.zeroBlank,?_,?_,?_,?_,input.routingBlank,?_,input.scalarWords⟩
    · intro i; exact (congrArg List.length (hrawF (src i))).trans (raw.values i)
    · intro r hr
      rw [hreserved]
      dsimp only [M,solverCarryState]
      exact (Function.update_of_ne ((solverRegister_injective T).ne hr) _ _).trans (hsolver r)
    · intro r; rw [hL]; exact hsolverLeft r
    · rw [hreserved]; simp only [M,solverCarryState,Function.update_self,rhs]
    · intro i; exact (hpubF (Fin.castAdd 1 i)).trans (hpubBlank _)
    · exact (congrArg List.length (hrawF widthSource)).trans raw.widthLength
  have hMsize := he₁.final
  let bound := fun (k : ℕ) (z : Store (HΓ (T := MachineTapes (T+solverRegisterCount)) (prime+K))
    (HS (MachineTapes (T+solverRegisterCount)) Q (prime+K) U)) =>
      mnSize z+k ≤ mnSize (mk v S)+depth+
        sharedBoundaryPreparationStock p u l target s t D Fs.length radius width Vg Vr
  have e₁ : ExecWithin body bound depth _ _ _ _ := he₁.mono (by
    intro k z hz
    dsimp only [bound,sharedBoundaryPreparationStock]
    omega)
  have e₂ : ExecWithin body bound depth _ _ _ _ := he₂.mono (by
    intro k z hz
    dsimp only [bound,sharedBoundaryPreparationStock,W,M,solverCarryState,rhs] at hz ⊢
    omega)
  refine ⟨v₂,F,input,hu₂.trans hu₁,numerical,retained,pubReady,hwords,boundary,hL,hI,hO,?_,n₁+n₂,?_,ExecWithin.seq e₁ e₂⟩
  · intro k hk hw hr hv hs hf hg
    have hoff : M.R k = S.R k := by
      dsimp only [M,solverCarryState]
      exact Function.update_of_ne hk _ _
    exact (hframe k hw hr hv hs hf hg).trans hoff
  · exact Nat.add_le_add hn₁ hn₂

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
