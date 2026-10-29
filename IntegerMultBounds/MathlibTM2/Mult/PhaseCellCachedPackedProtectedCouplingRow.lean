module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedProtectedCouplingRow
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedCouplingWorkspace

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 118 Q A U}

noncomputable def cachedPackedProtectedCouplingRow (hQ : SS.states ≤ Q) : Pr P₀ 118 Q A U :=
  embProg cachedCouplingCoreReg Empty.elim (packedProtectedCouplingRow (P₀ := Empty) hQ)

theorem cachedPackedProtectedCouplingRow_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {L q w : ℕ} (hw5 : 5 ≤ w) (hqw : q+4 ≤ w) (xs as : List GaussianInt) (rhs : GaussianInt)
    (hxlen : xs.length = L) (halen : as.length = L)
    (hxs : ∀ x ∈ xs, Fits w x) (has : ∀ a ∈ as, Fits w a ∧ a.im = 0)
    (v : HS 118 Q A U) (S : Stacks 118 A) (tailX tailA tailR : List (Fin (A+4)))
    (hL : ((embStk cachedCouplingCoreReg S).R 102).length = L) (hwR : ((embStk cachedCouplingCoreReg S).R 94).length = w) (hq : ((embStk cachedCouplingCoreReg S).R 112).length = q)
    (hx : (embStk cachedCouplingCoreReg S).R 110 = cstream A w xs++tailX) (ha : (embStk cachedCouplingCoreReg S).R 111 = cstream A w as++tailA)
    (hrhs : (embStk cachedCouplingCoreReg S).R 93 = csyms A w rhs++tailR) (hc : CClean mul (embStk cachedCouplingCoreReg S))
    (hblank : ∀ r : CR, (embStk cachedCouplingCoreReg S).R (cr r) = [])
    (hleft : ∀ k ∈ [(97 : Fin 117),98,99,100], (embStk cachedCouplingCoreReg S).L k = [])
    (hwork : ∀ k ∈ integerRowWork, k ∉ [(97 : Fin 117),98,99,105,106] → (embStk cachedCouplingCoreReg S).R k = [])
    (h109 : (embStk cachedCouplingCoreReg S).R 109 = [])
    (hmetaLeft : ∀ r ∈ [(105 : Fin 117),106], (embStk cachedCouplingCoreReg S).L r = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ generatedReadyRowCost L q w (S.R 100).length+
        4*((S.R 97).length+(S.R 98).length+(S.R 99).length)+12+
        4*(S.R 105).length+4+4*(S.R 106).length+4 ∧
      Exec body (cachedPackedProtectedCouplingRow hQ) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update S.R
          113 (csyms A w (rhs-(List.zipWith (fun x a => tdivN q (x*a)) xs as).sum)++S.R 113))
          110 tailX) 111 tailA) 102 [])}) := by
  obtain ⟨v₁,m,hu₁,hm,he⟩ := packedProtectedCouplingRow_exec
    (body := fun p : Empty => nomatch p) hQ hA hw5 hqw xs as rhs hxlen halen hxs has
    (embDn cachedCouplingCoreReg v) (embStk cachedCouplingCoreReg S) tailX tailA tailR
    hL hwR hq hx ha hrhs hc hblank hleft hwork h109 hmetaLeft
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    cachedCouplingCoreReg_injective (fun p => nomatch p) he v rfl S rfl
  refine ⟨v₂,m,hu₂.trans hu₁,hm,he₂.cast rfl ?_⟩
  apply congrArg (mk v₂)
  let T := embStk cachedCouplingCoreReg S
  let output := csyms A w (rhs-(List.zipWith (fun x a => tdivN q (x*a)) xs as).sum)++T.R 113
  let T₁ : Stacks 117 A := {T with R := Function.update T.R 113 output}
  let T₂ : Stacks 117 A := {T₁ with R := Function.update T₁.R 110 tailX}
  let T₃ : Stacks 117 A := {T₂ with R := Function.update T₂.R 111 tailA}
  change embOvr cachedCouplingCoreReg
    ({T₃ with R := Function.update T₃.R 102 []} : Stacks 117 A).get S = _
  rw [embOvr_updR cachedCouplingCoreReg_injective T₃ S 102,
    embOvr_updR cachedCouplingCoreReg_injective T₂ S 111,
    embOvr_updR cachedCouplingCoreReg_injective T₁ S 110,
    embOvr_updR cachedCouplingCoreReg_injective T S 113,embOvr_stk]
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
