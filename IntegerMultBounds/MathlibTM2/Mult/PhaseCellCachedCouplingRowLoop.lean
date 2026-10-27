module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedOuterCouplingRow
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedLoop

/-! Counted consecutive residual/recovery rows with exact physical stream and frame. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

noncomputable def cachedCouplingRowLoop (hQ : SS.states ≤ Q) (boundary : Bool) : Pr P₀ 144 Q A U :=
  countedLoop 143 (cachedOuterCouplingRow hQ boundary)

def cachedCouplingRowLoopCost (P q w s t u band a b i N : ℕ) : ℕ :=
  (Finset.range N).sum (fun j => cachedCouplingRowStepCost P q w s t u band a b (i+j)+3)+2

theorem cachedCouplingRowLoop_exec (hQ : SS.states ≤ Q) {P q w s t u band a b i : ℕ} [NeZero s]
    (boundary : Bool) (hA : 96 ≤ A) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hbandS : band ≤ s) (hP : 13 ≤ P)
    (C : ZMod s → GaussianInt) (rhs : List GaussianInt) (hrows : i+rhs.length ≤ s)
    (tail rhsTail : List (Fin (A+4))) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hready : CouplingReady P q w s t u band a b (cstream A w (chirpLine s C)++tail) (embStk cachedCouplingCoreReg (embStk cachedCouplingOuterReg S)))
    (hcache : ∃ cacheTail, S.R 141 = cstream A w (chirpLine s C)++cacheTail)
    (hindex : (S.R 107).length = i) (hrhs : S.R 93 = cstream A w rhs++rhsTail)
    (hcount : (S.R 143).length = rhs.length)
    (hxs : ∀ j < rhs.length, ∀ x ∈ couplingInputWords boundary t band a b (i+j) C, Fits w x)
    (has : ∀ j < rhs.length, ∀ z ∈ couplingCoefficientWords P q s t u band (i+j), Fits w z ∧ z.im = 0) :
    ∃ v' m, v'.user = v.user ∧ m ≤ cachedCouplingRowLoopCost P q w s t u band a b i rhs.length ∧
      Exec (body) (cachedCouplingRowLoop hQ boundary) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update S.R
          93 rhsTail) 107 (List.replicate rhs.length tick++S.R 107))
          113 (cstream A w (couplingRowWords P q t u band a b boundary C i rhs).reverse++S.R 113)) 143 [])}) := by
  let ys := couplingRowWords P q t u band a b boundary C i rhs
  let Inv : ℕ → Stacks 144 A → Prop := fun j B =>
    B.inp = S.inp ∧ B.out = S.out ∧ B.L = S.L ∧
    (∀ k : Fin 144, k ≠ 93 → k ≠ 107 → k ≠ 113 → k ≠ 143 → B.R k = S.R k) ∧
    B.R 93 = cstream A w (rhs.drop j)++rhsTail ∧
    B.R 107 = List.replicate j tick++S.R 107 ∧
    B.R 113 = cstream A w (ys.take j).reverse++S.R 113
  have hstable : ∀ j B cs, Inv j B → Inv j {B with R := Function.update B.R 143 cs} := by
    intro j B cs h
    rcases h with ⟨hi,ho,hl,hf,hr,hj,hy⟩
    exact ⟨hi,ho,hl,by intro k h93 h107 h113 h143; simpa [h143] using hf k h93 h107 h113 h143,
      by simpa using hr,by simpa using hj,by simpa using hy⟩
  have hstep : ∀ j < rhs.length, ∀ (vi : HS 144 Q A U) B, Inv j B →
      ∃ v' B' m, v'.user = vi.user ∧ m ≤ cachedCouplingRowStepCost P q w s t u band a b (i+j) ∧
        Exec (body) (cachedOuterCouplingRow hQ boundary) (mk vi B) m (mk v' B') ∧
        B'.R 143 = B.R 143 ∧ Inv (j+1) B' := by
    intro j hj vi B h
    rcases h with ⟨hiB,hoB,hlB,hf,hr,hjB,hyB⟩
    have hreadyB : CouplingReady P q w s t u band a b
        (cstream A w (chirpLine s C)++tail) (embStk cachedCouplingCoreReg (embStk cachedCouplingOuterReg B)) := by
      apply hready.of_frame
      · change (B.L ∘ cachedCouplingOuterReg) ∘ cachedCouplingCoreReg =
          (S.L ∘ cachedCouplingOuterReg) ∘ cachedCouplingCoreReg
        rw [hlB]
      · intro k h93 h107 h113
        apply hf (cachedCouplingOuterReg (cachedCouplingCoreReg k))
        · simpa [cachedCouplingOuterReg,cachedCouplingCoreReg,k.isLt,Fin.ext_iff] using h93
        · simpa [cachedCouplingOuterReg,cachedCouplingCoreReg,k.isLt,Fin.ext_iff] using h107
        · simpa [cachedCouplingOuterReg,cachedCouplingCoreReg,k.isLt,Fin.ext_iff] using h113
        · exact cachedCouplingOuterReg_off 143 (by decide) (by decide) (cachedCouplingCoreReg k)
    have hindexB : (B.R 107).length = i+j := by simp [hjB,hindex,Nat.add_comm]
    have hrhsB : B.R 93 = csyms A w rhs[j]++(cstream A w (rhs.drop (j+1))++rhsTail) := by
      rw [hr,List.drop_eq_getElem_cons hj,cstream_cons,List.append_assoc]
    obtain ⟨v',m,hu,hm,he⟩ := cachedOuterCouplingRow_exec (body := body) hQ boundary hA hw5 hqw
      hst haS hbS hbandS (by omega) hP C rhs[j] tail (cstream A w (rhs.drop (j+1))++rhsTail)
      vi B hreadyB (by obtain ⟨cacheTail,hh⟩ := hcache; exact ⟨cacheTail,(hf 141 (by decide) (by decide) (by decide) (by decide)).trans hh⟩) hindexB hrhsB (hxs j hj) (has j hj)
    let z := couplingRowWord P q t u band a b (i+j) boundary C rhs[j]
    let B' : Stacks 144 A := {B with R := (Function.update (Function.update (Function.update B.R
      113 (csyms A w z++B.R 113)) 93 (cstream A w (rhs.drop (j+1))++rhsTail)) 107 (tick::B.R 107))}
    have hylen : j < ys.length := by simpa [ys] using hj
    have hyget : ys[j] = z := couplingRowWords_getElem P q t u band a b i boundary C rhs j hj
    have hnext : cstream A w (ys.take (j+1)).reverse = csyms A w z++cstream A w (ys.take j).reverse := by
      rw [List.take_succ_eq_append_getElem hylen,List.reverse_append,List.reverse_singleton,
        cstream_append,cstream_cons,cstream_nil,List.append_nil,hyget]
    refine ⟨v',B',m,hu,hm,he,by simp [B'],hiB,hoB,hlB,?_,by simp [B'],?_,?_⟩
    · intro k h93 h107 h113 h143
      simpa [B',h93,h107,h113] using hf k h93 h107 h113 h143
    · simp [B',hjB,List.replicate_succ]
    · simp [B',hyB,hnext,List.append_assoc]
  have hInv : Inv 0 S := by
    exact ⟨rfl,rfl,rfl,by intros; rfl,by simpa using hrhs,by simp,by simp⟩
  obtain ⟨v',S',m,hu,hm,he,h143,hI⟩ := countedLoop_exec_costs (body := body)
    143 (cachedOuterCouplingRow hQ boundary) rhs.length
    (fun j => cachedCouplingRowStepCost P q w s t u band a b (i+j)) Inv hstable hstep v S hcount hInv
  rcases hI with ⟨hi',ho',hl',hf,hr',hj',hy'⟩
  refine ⟨v',m,hu,hm,he.cast rfl ?_⟩
  apply congrArg (mk v')
  refine Stacks.ext hi' ho' hl' ?_
  funext k
  by_cases h93 : k = 93
  · subst k; simpa using hr'
  by_cases h107 : k = 107
  · subst k; simpa using hj'
  by_cases h113 : k = 113
  · subst k
    have hlen : ys.length = rhs.length := by simp [ys]
    rw [← hlen,List.take_length] at hy'
    simpa [ys] using hy'
  by_cases h143' : k = 143
  · subst k; simpa using h143
  simpa [h93,h107,h113,h143'] using hf k h93 h107 h113 h143'

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
