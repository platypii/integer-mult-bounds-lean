module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyInverseBatchDescriptorCall
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedDescriptorFinish
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSelectedFamilyInverseBatchCaller
public import IntegerMultBounds.MathlibTM2.StackLifecycleResources

public import IntegerMultBounds.MathlibTM2.Host.EmbedStock
public import IntegerMultBounds.MathlibTM2.StackExecutionUnique

/-! One complete dispatch step loads a raw batch, executes it, collects its output and clears the bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

noncomputable def familyInverseBatchDispatchStep (work : Fin 303 → Fin T)
    (src saved count tmp spare result : Fin T) (recovery : Bool)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  .seq (familyInverseBatchDescriptorCall work src saved count tmp spare recovery hR hQ)
    (finishDescriptorBank (List.ofFn work) (work 132) result tmp)

theorem familyInverseBatchDispatchStep_spec
    (work : Fin 303 → Fin T) (hwork : Function.Injective work)
    (src saved count tmp spare result : Fin T) (hreg : [src,saved,count,tmp,spare].Nodup)
    (hresult : result ∉ [src,saved,count,tmp,spare]) (hresultWork : ∀ i, work i ≠ result)
    (hsep : ∀ i, work i ∉ [src,saved,count,tmp,spare])
    (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (ha : a ≤ s) (hb : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1) :
    let B := haloBoundary s t (PhaseCellBand.width p u) a b
    let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    ∀ (Fs : List (ZMod s → GaussianInt)), (∀ F ∈ Fs, ∀ i, ‖value q (F i)‖ ≤ (2 : ℝ)^2) →
    ∀ (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A+4))),
    ∀ (words : Fin 303 → List (Fin (A+4))) (rest : List (Fin (A+4))), words 132 = [] →
    (∀ i, S.R (work i) = []) →
    S.R src = descriptorBankTape (placedDescriptorFields work words)++rest →
    S.R count = [] → S.R tmp = [] → S.R spare = [] →
    ∀ (wl : List (Fin (A+4))), wl.length = inverseCallerWordWidth p u l target s t →
    tblHolds familyInverseScalarReg (descriptorReadyBank work words S) (tblRho (inverseCallerWordWidth p u l target s t) wl [] (inverseInputScalars p u l target s t a b)) →
    (∀ i, (descriptorReadyBank work words S).L (familyInverseCoreReg i) = []) →
    (∀ i, i ≠ 110 → i ≠ 132 → i ≠ 246 → (descriptorReadyBank work words S).R (familyInverseCoreReg i) = []) →
    (descriptorReadyBank work words S).R 110 = cstream A w (Fs.map (chirpLine s)).flatten++tail →
    ((descriptorReadyBank work words S).R (familyInverseCoreReg 246)).length = Fs.length →
    ∀ (x y : (ZMod s → GaussianInt) → ZMod s → ℝ),
    (∀ F ∈ Fs, Solves (realMatrix s t p u) (haloVertices s a b) (x F) (fun i => (value q (F i)).re)) →
    (∀ F ∈ Fs, Solves (realMatrix s t p u) (haloVertices s a b) (y F) (fun i => (value q (F i)).im)) →
    ∃ v' n, ∃ Zs : List (ZMod s → GaussianInt),
      v'.user = v.user ∧ n ≤ takeDescriptorBankCost (placedDescriptorFields work words)+familyInverseBatchCallerCost A (inverseCallerWordWidth p u l target s t) p u l s t a b target Fs.length+(6*(Fs.length*s*w)+2*(∑ i, (words i).length)+611) ∧
      Exec body (familyInverseBatchDispatchStep work src saved count tmp spare result recovery hR hQ) (mk v S) n
        (mk v' (dispatchedDescriptorState work words src saved result rest (cstream A w (Zs.map (chirpLine s)).flatten) S)) ∧
      List.Forall₂ (fun F Z => PhaseCellInterface.ErrorOn (haloVertices s a b)
        (pairedCellRead q w (cstream A w (chirpLine s Z)++words 132))
          (fun i => (⟨x F i,y F i⟩ : ℂ)) (1/(2 : ℝ)^target)) Fs Zs ∧
      ∀ C, mnProgPush (familyInverseBatchDispatchStep work src saved count tmp spare result (P := P) (U := U) (A := A) recovery hR hQ) ≤ C →
        (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          (C+1)*(takeDescriptorBankCost (placedDescriptorFields work words)+
            familyInverseBatchCallerStockCost A (inverseCallerWordWidth p u l target s t) p u l s t a b target Fs.length+(6*(Fs.length*s*w)+2*(∑ i, (words i).length)+611)))
          depth (familyInverseBatchDispatchStep work src saved count tmp spare result recovery hR hQ) (mk v S) n
          (mk v' (dispatchedDescriptorState work words src saved result rest (cstream A w (Zs.map (chirpLine s)).flatten) S)) := by
  dsimp only
  intro Fs hF v S tail words rest houtputBlank hblankWork hsourcePacket hcounter htmp hspare wl hwl
    hscalar hleft hblank hsource hcount x y hx hy
  obtain ⟨v₁,n₁,Zs,hu₁,hn₁,he₁,herror,htrace⟩ := familyInverseBatchDescriptorCall_spec
    (body := body) work hwork src saved count tmp spare hreg hsep recovery hR hQ hA hp hwidth hα
      hst hu hαu hθ hgap hbudget hband ha hb hpad Fs hF v S tail words rest
      hblankWork hsourcePacket hcounter htmp hspare wl hwl hscalar hleft hblank hsource hcount x y hx hy
  have hr := hreg
  regs_ne hr
  have hresultNe : result ≠ src ∧ result ≠ saved ∧ result ≠ count ∧ result ≠ tmp ∧ result ≠ spare := by
    simpa only [List.mem_cons,List.not_mem_nil,or_false,not_or] using hresult
  have hfinish : [src,saved,result,tmp].Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨⟨‹src ≠ saved›,hresultNe.1.symm,‹src ≠ tmp›⟩,
      ⟨hresultNe.2.1.symm,‹saved ≠ tmp›⟩,hresultNe.2.2.2.1,by simp⟩
  let w := executionWidth p l (initialSchurTarget p u
    (boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2
      (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2
  let produced := cstream A w (Zs.map (chirpLine s)).flatten
  have he₁' := he₁
  simp only [houtputBlank,List.append_nil] at he₁' htrace
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := finishPlacedDescriptorBank_exec (body := body) work hwork words
    src saved result tmp hfinish
    (by intro i; have hi := hsep i; simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hi ⊢
        exact ⟨hi.1,hi.2.1,hresultWork i,hi.2.2.2.1⟩)
    132 rest produced v₁ S hblankWork htmp
  have hlen : produced.length = Fs.length*s*w := by
    rw [familyBatchWords_length,← herror.length_eq]
  have hn₂' : n₂ ≤ 6*(Fs.length*s*w)+2*(∑ i, (words i).length)+611 := by
    simpa only [hlen] using hn₂
  refine ⟨v₂,n₁+n₂,Zs,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂',Exec.seq he₁' he₂,herror,?_⟩
  exact mn_seq_exec_within htrace (mn_bounded_exec_certify he₂ hn₂')

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
