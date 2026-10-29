module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloCouplingReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBinaryLengthCouplingCoefficientInterval

/-! Generate the retained coefficient page through the shared scalar-header view.
The temporary origin index is copied once and released after page generation. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

def sharedCouplingCoefficientInterval : Pr P 168 Q A U :=
  .seq (ucopy 141 107 135)
    (.seq (embProg sharedCouplingReg Empty.elim (binaryLengthCouplingCoefficientInterval (P := Empty))) (uclear 107))

/-- The retained page occupies only ports outside the shared arithmetic view. -/
def sharedCouplingPageState (band w : ℕ) (xs : List GaussianInt) (S : Stacks 168 A) : Stacks 168 A :=
  {S with R := (Function.update (Function.update (Function.update (Function.update (Function.update S.R
    140 (List.replicate (2*band+1) tick)) 135 []) 138 (cstream A w xs++S.R 138))
    139 (List.replicate xs.length tick)) 143 [])}

theorem sharedCouplingPage_core (band w : ℕ) (xs : List GaussianInt) (S : Stacks 168 A) :
    embStk sharedCouplingCoreReg (sharedCouplingPageState band w xs S) = embStk sharedCouplingCoreReg S := by
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  have hn (j : Fin 168) (hj : 117 ≤ j.val) (hfix : sharedCouplingReg j = j) : sharedCouplingCoreReg i ≠ j := by
    intro he
    have hh := sharedCouplingReg_injective (he.trans hfix.symm)
    have hv := congrArg (fun k : Fin 168 => k.val) hh
    change i.val = j.val at hv
    have hi := i.isLt
    omega
  simp only [sharedCouplingPageState,embStk_R,
    Function.update_of_ne (hn 143 (by decide) (by decide)),
    Function.update_of_ne (hn 139 (by decide) (by decide)),
    Function.update_of_ne (hn 138 (by decide) (by decide)),
    Function.update_of_ne (hn 135 (by decide) (by decide)),
    Function.update_of_ne (hn 140 (by decide) (by decide))]

theorem sharedCouplingPage_native (band w : ℕ) (xs : List GaussianInt) (S : Stacks 168 A) :
    embStk packedCellCoreReg (sharedCouplingPageState band w xs S) = embStk packedCellCoreReg S := by
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  have hn (j : Fin 168) (hj : 117 ≤ j.val) : packedCellCoreReg i ≠ j := by
    intro he
    have hv := congrArg (fun k : Fin 168 => k.val) he
    change i.val = j.val at hv
    have hi := i.isLt
    omega
  simp only [sharedCouplingPageState,embStk_R,
    Function.update_of_ne (hn 143 (by decide)),Function.update_of_ne (hn 139 (by decide)),
    Function.update_of_ne (hn 138 (by decide)),Function.update_of_ne (hn 135 (by decide)),
    Function.update_of_ne (hn 140 (by decide))]

def sharedCouplingCoefficientIntervalCost (precision q w s t u band a b V : ℕ) : ℕ :=
  let N := b-a
  let xs := couplingCoefficientPageInterval precision q s t u band a b a N
  6*a+6+(8*N+11*V+8+(buildMarkedRowCoefficientPacketCost precision q w s t u band a+
    (prepareCouplingPageCountsCost N band+(144*V+145+((46*N+2)*tblC V 1+66*V+2*N+70)+
      couplingCoefficientPageIntervalLoopCost precision q w s t u band a b a N+
      transferCountedLineCost xs.length w+24*liftedCoefficientWidth precision q w s t u band+4))))

theorem sharedCouplingCoefficientInterval_exec {V precision q w s t u band a b : ℕ} [NeZero s]
    (hA : 4 ≤ A) (hprecision : 13 ≤ precision) (hst : s < t) (hab : a ≤ b) (hb : b ≤ s) (ha : a < s)
    (hwide : 8*(t+1)^2+4*band+8 < 2^V) (hfitV : a+((b-a)+2*band)+s < 2^V)
    (raw : List (Fin (A+4))) (v : HS 168 Q A U) (S : Stacks 168 A)
    (hready : CouplingReady precision q w s t u band a b raw (embStk sharedCouplingCoreReg S))
    (hmeta : CouplingIntervalMetadata V s t band a b a (b-a) S)
    (h141 : (S.R 141).length = a) (h107 : S.R 107 = [])
    (hfresh : ∀ k ∈ [(135 : Fin 168),139,140,143,166], S.R k = []) :
    let xs := couplingCoefficientPageInterval precision q s t u band a b a (b-a)
    ∃ v' m, v'.user = v.user ∧ m ≤ sharedCouplingCoefficientIntervalCost precision q w s t u band a b V ∧
      Exec body sharedCouplingCoefficientInterval (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update (Function.update S.R
          140 (List.replicate (2*band+1) tick)) 135 []) 138 (cstream A w xs++S.R 138))
          139 (List.replicate xs.length tick)) 143 [])}) := by
  dsimp only
  let xs := couplingCoefficientPageInterval precision q s t u band a b a (b-a)
  obtain ⟨v₀,hu₀,he₀⟩ := ucopy_exec (body := body) (a := 141) (b := 107) (t := 135)
    (by decide) (by decide) (by decide) v S (hfresh 135 (by simp))
  let B : Stacks 168 A := {S with R := Function.update S.R 107 (List.replicate a tick)}
  have he₀' : Exec body (ucopy 141 107 135) (mk v S) (4*a+4) (mk v₀ B) := by
    simpa [B,h141,h107] using he₀
  have hreadyB : CouplingReady precision q w s t u band a b raw (embStk sharedCouplingCoreReg B) := by
    refine hready.of_source_frame (S' := embStk sharedCouplingCoreReg B) ?_ rfl ?_
    · simpa [B,embStk,sharedCouplingCoreReg,sharedCouplingReg,packedCellCoreReg] using hready.source
    · intro k _ hk _ _
      have hn : sharedCouplingCoreReg k ≠ 107 := by
        intro he
        apply hk
        apply sharedCouplingCoreReg_injective
        exact he.trans (by decide)
      simp [B,embStk,hn]
  have hmetaB : CouplingIntervalMetadata V s t band a b a (b-a) B := by
    constructor
    · simpa [B] using hmeta.width
    · intro k hk
      have hn : k ≠ 107 := by
        simp only [couplingIntervalPorts,List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      simpa [B,hn] using hmeta.encoded k hk
  let T := embStk sharedCouplingReg B
  have hmetaT := couplingIntervalMetadata_shared hmetaB
  let value := fun k : Fin 117 => couplingIntervalValue s t band a b a (b-a) (intervalGuardPlacement k)
  have hvalue : ∀ k, value k < 2^V := fun k => couplingIntervalValue_bound
    (by omega) (hab.trans hb) hb hst hfitV (by nlinarith only [hwide]) _
  have hblank : ∀ r, (embStk intervalGuardPlacement T).R (intervalGuardReg r) = [] := by
    intro r
    have hr := intervalGuardReg_range r
    have hn : intervalGuardReg r ≠ 109 := by
      intro he; have hv := congrArg (fun k : Fin 117 => k.val) he; norm_num at hv; omega
    have hh := hreadyB.low (intervalGuardReg r) (by omega)
    change T.R (intervalGuardPlacement (intervalGuardReg r)) = []
    simpa only [T,embStk_R,intervalGuardPlacement,ite_eq_right hn,
      ite_eq_left (show (intervalGuardReg r).val < 96 by omega),sharedCouplingCoreReg,packedCellCoreReg] using hh
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := binaryLengthCouplingCoefficientInterval_exec
    (body := fun p : Empty => nomatch p) value
    (by simp [value,intervalGuardPlacement,couplingIntervalValue])
    (by simp [value,intervalGuardPlacement,couplingIntervalValue])
    (by simp [value,intervalGuardPlacement,couplingIntervalValue])
    (by simp [value,intervalGuardPlacement,couplingIntervalValue])
    (by simp [value,intervalGuardPlacement,couplingIntervalValue])
    (by simp [value,intervalGuardPlacement,couplingIntervalValue])
    (by simp [value,intervalGuardPlacement,couplingIntervalValue])
    (show a+(b-a) ≤ s by omega) (NeZero.pos s) hst (hab.trans hb) hb hwide
    (fun i => hvalue _) (embDn sharedCouplingReg v₀) T
    (by simpa [T,embStk,intervalGuardPlacement] using hmetaT.width) hmetaT.guard hblank
    hA hprecision raw hreadyB
    (by simpa [T,B,embStk,sharedCouplingReg] using hfresh 140 (by simp))
    (by simpa [T,B,embStk,sharedCouplingReg] using hfresh 143 (by simp))
    (by simpa [T] using hmetaT.count)
    (by simpa [T,B,embStk,sharedCouplingReg] using hfresh 166 (by simp))
    (by simpa [T,B,embStk,sharedCouplingReg] using hfresh 135 (by simp))
    (by simp [T,B,embStk,sharedCouplingReg]) ha
    (by simpa [T,B,embStk,sharedCouplingReg] using hfresh 139 (by simp))
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    sharedCouplingReg_injective (fun p => nomatch p) he₁ v₀ rfl B rfl
  let C : Stacks 168 A := {B with R := (Function.update (Function.update (Function.update (Function.update (Function.update B.R
    140 (List.replicate (2*band+1) tick)) 135 []) 138 (cstream A w xs++B.R 138))
    139 (List.replicate xs.length tick)) 143 [])}
  have hfinal : embOvr sharedCouplingReg
      ({T with R := (Function.update (Function.update (Function.update (Function.update (Function.update T.R
        140 (List.replicate (2*band+1) tick)) 135 []) 138 (cstream A w xs++T.R 138))
        139 (List.replicate xs.length tick)) 143 [])} : Stacks 168 A).get B = C := by
    let T₁ : Stacks 168 A := {T with R := Function.update T.R 140 (List.replicate (2*band+1) tick)}
    let T₂ : Stacks 168 A := {T₁ with R := Function.update T₁.R 135 []}
    let T₃ : Stacks 168 A := {T₂ with R := Function.update T₂.R 138 (cstream A w xs++T.R 138)}
    let T₄ : Stacks 168 A := {T₃ with R := Function.update T₃.R 139 (List.replicate xs.length tick)}
    change embOvr sharedCouplingReg ({T₄ with R := Function.update T₄.R 143 []} : Stacks 168 A).get B = C
    rw [embOvr_updR sharedCouplingReg_injective T₄ B 143,
      embOvr_updR sharedCouplingReg_injective T₃ B 139,
      embOvr_updR sharedCouplingReg_injective T₂ B 138,
      embOvr_updR sharedCouplingReg_injective T₁ B 135,
      embOvr_updR sharedCouplingReg_injective T B 140,embOvr_stk]
    rfl
  have he₂' := he₂.cast rfl (congrArg (mk v₂) hfinal)
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec body 107 v₂ C
  have h107C : (C.R 107).length = a := by simp [C,B]
  refine ⟨v₃,(4*a+4)+(m₁+(2*a+2)),hu₃.trans (hu₂.trans (hu₁.trans hu₀)),?_,
    (Exec.seq he₀' (Exec.seq he₂' he₃)).cast (by rw [h107C]) ?_⟩
  · dsimp only [sharedCouplingCoefficientIntervalCost]
    omega
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk : k = 107
    · subst k; simp [C,B,h107]
    · simp [C,B,xs,Function.update_apply,hk]

/-- The state returned by the complete interior solver supplies coefficient
setup directly; no independently prepared coupling parameter bank is assumed. -/
theorem PackedHaloReady.coefficient_exec {V precision stage q l w s t u band a b : ℕ} [NeZero s]
    (hA : 4 ≤ A) (hprecision : 13 ≤ precision) (hst : s < t) (hab : a ≤ b) (hb : b ≤ s) (ha : a < s)
    (hwide : 8*(t+1)^2+4*band+8 < 2^V) (hfitV : a+((b-a)+2*band)+s < 2^V)
    (input E outputTail : List (Fin (A+4))) (v : HS 168 Q A U) (S : Stacks 168 A)
    (h : PackedHaloReady precision stage q l s t u band a b V w input E outputTail S)
    (h141 : (S.R 141).length = a) (h142 : (S.R 142).length = b)
    (hleft : ∀ k ∈ [(121 : Fin 168),122,123,124], S.L k = [])
    (h139 : S.R 139 = []) (h143 : S.R 143 = []) :
    let xs := couplingCoefficientPageInterval precision q s t u band a b a (b-a)
    ∃ v' m, v'.user = v.user ∧ m ≤ sharedCouplingCoefficientIntervalCost precision q w s t u band a b V ∧
      Exec body sharedCouplingCoefficientInterval (Host.mk v S) m
        (Host.mk v' {S with R := (Function.update (Function.update (Function.update (Function.update (Function.update S.R
          140 (List.replicate (2*band+1) tick)) 135 []) 138 (cstream A w xs++S.R 138))
          139 (List.replicate xs.length tick)) 143 [])}) := by
  have h107 : S.R 107 = [] := by
    simpa [embStk,packedCellCoreReg,releasedCellBank] using
      congrArg (fun B : Stacks 117 A => B.R 107) h.native
  exact sharedCouplingCoefficientInterval_exec (body := body) hA hprecision hst hab hb ha hwide hfitV
    input v S (h.coupling h141 h142 hleft) h.metadata h141 h107 (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl
      · exact h.fresh 135 (by simp)
      · exact h139
      · exact h.fresh 140 (by simp)
      · exact h143
      · exact h.fresh 166 (by simp))

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
