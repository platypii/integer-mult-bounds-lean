module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedDescriptorBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSelectedFamilyInverseBatchCaller
public import IntegerMultBounds.MathlibTM2.StackLifecycleResources

public import IntegerMultBounds.MathlibTM2.Host.EmbedStock
public import IntegerMultBounds.MathlibTM2.StackExecutionUnique

/-! Load an ordinary raw bank from a packet tape and execute its counted batch. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def descriptorReadyBank (work : Fin 303 → Fin T) (words : Fin 303 → List (Fin (A+4)))
    (S : Stacks T A) : Stacks 303 A := {embStk work S with R := words}

noncomputable def familyInverseBatchDescriptorCall (work : Fin 303 → Fin T)
    (src saved count tmp spare : Fin T) (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  .seq (takePlacedDescriptorBank work src saved count tmp spare)
    (embProg work (Empty.elim : Empty → P) (familyInverseBatchCaller (P := Empty) recovery hR hQ))

theorem familyInverseBatchDescriptorCall_spec
    (work : Fin 303 → Fin T) (hwork : Function.Injective work)
    (src saved count tmp spare : Fin T) (hreg : [src,saved,count,tmp,spare].Nodup)
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
    ∀ (words : Fin 303 → List (Fin (A+4))) (rest : List (Fin (A+4))),
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
      v'.user = v.user ∧ n ≤ takeDescriptorBankCost (placedDescriptorFields work words)+familyInverseBatchCallerCost A (inverseCallerWordWidth p u l target s t) p u l s t a b target Fs.length ∧
      Exec body (familyInverseBatchDescriptorCall work src saved count tmp spare recovery hR hQ) (mk v S) n
        (mk v' {placedDescriptorState work words src saved rest S with R := (Function.update (placedDescriptorState work words src saved rest S).R (work 132) (cstream A w (Zs.map (chirpLine s)).flatten++words 132))}) ∧
      List.Forall₂ (fun F Z => PhaseCellInterface.ErrorOn (haloVertices s a b)
        (pairedCellRead q w (cstream A w (chirpLine s Z)++words 132))
          (fun i => (⟨x F i,y F i⟩ : ℂ)) (1/(2 : ℝ)^target)) Fs Zs ∧
      ∀ C, mnProgPush (familyInverseBatchDescriptorCall work src saved count tmp spare (P := P) (U := U) (A := A) recovery hR hQ) ≤ C →
        (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          (C+1)*(takeDescriptorBankCost (placedDescriptorFields work words)+
            familyInverseBatchCallerStockCost A (inverseCallerWordWidth p u l target s t) p u l s t a b target Fs.length))
          depth (familyInverseBatchDescriptorCall work src saved count tmp spare recovery hR hQ) (mk v S) n
          (mk v' {placedDescriptorState work words src saved rest S with R := (Function.update (placedDescriptorState work words src saved rest S).R (work 132) (cstream A w (Zs.map (chirpLine s)).flatten++words 132))}) := by
  dsimp only
  intro Fs hF v S tail words rest hblankWork hsourcePacket hcounter htmp hspare wl hwl
    hscalar hleft hblank hsource hcount x y hx hy
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁,hload⟩ := takePlacedDescriptorBank_exec (body := body)
    work hwork src saved count tmp spare hreg hsep words v S rest
      hsourcePacket hblankWork hcounter htmp hspare
  let w := executionWidth p l (initialSchurTarget p u
    (boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2
      (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2
  let S₁ := placedDescriptorState work words src saved rest S
  have hload' : embStk work S₁ = descriptorReadyBank work words S := hload
  obtain ⟨vi,n₂,Zs,hui,hn₂,hei,herror,htrace⟩ := familyInverseBatchCaller_derived_spec
    (body := fun f : Empty => nomatch f) recovery hR hQ hA hp hwidth hα hst hu hαu
      hθ hgap hbudget hband ha hb hpad Fs hF (embDn work v₁) (descriptorReadyBank work words S)
      tail wl hwl hscalar hleft hblank hsource hcount x y hx hy
  rw [← hload'] at hei htrace
  have hbase : (embStk work S₁).R 132 = words 132 := congrArg (fun S => S.R 132) hload'
  rw [hbase] at hei htrace
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body) hwork
    (fun f => nomatch f) hei v₁ rfl S₁ rfl
  have hfinal : embOvr work
      ({embStk work S₁ with R := (Function.update (embStk work S₁).R 132
        (cstream A w (Zs.map (chirpLine s)).flatten++words 132))}).get S₁ =
      {S₁ with R := (Function.update S₁.R (work 132)
        (cstream A w (Zs.map (chirpLine s)).flatten++words 132))} := by
    rw [embOvr_updR hwork,embOvr_stk]
  have heOut := he₂.cast rfl (congrArg (mk v₂) hfinal)
  refine ⟨v₂,n₁+n₂,Zs,(hu₂.trans hui).trans hu₁,Nat.add_le_add hn₁ hn₂,
    Exec.seq he₁ heOut,herror,?_⟩
  have htBig : ∀ C, mnProgPush (embProg work (Empty.elim : Empty → P)
      (familyInverseBatchCaller (P := Empty) (U := U) (A := A) recovery hR hQ)) ≤ C →
      (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v₁ S₁)+depth+
        (C+1)*familyInverseBatchCallerStockCost A (inverseCallerWordWidth p u l target s t)
          p u l s t a b target Fs.length) depth
        (embProg work (Empty.elim : Empty → P) (familyInverseBatchCaller recovery hR hQ))
        (mk v₁ S₁) n₂
        (mk v₂ {S₁ with R := (Function.update S₁.R (work 132)
          (cstream A w (Zs.map (chirpLine s)).flatten++words 132))}) := by
    intro C hpC hbC depth
    have hpSmall : mnProgPush (familyInverseBatchCaller (P := Empty) (U := U) (A := A) recovery hR hQ) ≤ C := by
      simpa only [embProg_push] using hpC
    obtain ⟨vf,hvf,huf,ht⟩ := exec_emb_ovr_within_stock work hwork
      (ι := Empty.elim) (body' := body) (fun f => nomatch f)
      (htrace C hpSmall (fun f => nomatch f) depth) v₁ rfl S₁ rfl
    have hsame := (ht.toExec.unique heOut).2
    rw [hsame] at ht
    exact ht
  exact mn_seq_exec_within (mn_bounded_exec_certify he₁ hn₁) htBig

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
