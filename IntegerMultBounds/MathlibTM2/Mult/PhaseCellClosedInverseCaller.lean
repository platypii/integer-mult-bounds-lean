module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInverseHeadersReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseInverseCaller

/-! A raw-scalar inverse caller: generate readiness, execute the retained solver, and release every generated header. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def inverseInputScalars {A : ℕ} (p u l target s t a b : ℕ) : TblSt 25 A :=
  ⟨![p,u,l,target,s,t,a,b,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]⟩

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

noncomputable def closedInverseCaller (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 264 Q A U :=
  .seq (installInverseHeaders inverseScalarReg inverseMasterPort)
    (.seq (embProg inverseCoreReg id (retainedComplexBoundary hR hQ)) releaseInverseCaller)

noncomputable def closedInverseCallerCost (W p u l target s t : ℕ) [NeZero s] : ℕ :=
  inverseScalarAtoms p s t u 0 s*tblC W 0+
    inverseMasterCopyCost W (inverseMasterValues p u l target s t 0 s)+
    retainedComplexBoundaryCost p u l s t 0 s target+
    inverseReleaseCost W (inverseMasterValues p u l target s t 0 s)

theorem closedInverseCaller_sized_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {W p u l target s t : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (hbandRoom : 64*(p+1)+u < 2^W)
    (hgeometryRoom : 8*(t+1)^2+2*PhaseCellBand.width p u+8 < 2^W)
    (hprecisionRoom : inversePrecisionRoom p l target (haloBoundary s t (PhaseCellBand.width p u) 0 s).card
      (PhaseCellBand.width p u) < 2^W)
    (F : ZMod s → GaussianInt)
    (hF : ∀ i, ‖value (executionPrecision p l (initialSchurTarget p u
      (boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 (haloBoundary s t (PhaseCellBand.width p u) 0 s).card) 2) 2) (F i)‖ ≤ (2 : ℝ)^2)
    (v : HS 264 Q A U) (S : Stacks 264 A) (tail wl : List (Fin (A+4))) (hwl : wl.length = W)
    (hscalar : tblHolds inverseScalarReg S (tblRho W wl [] (inverseInputScalars p u l target s t 0 s)))
    (hleft : ∀ i, S.L (inverseCoreReg i) = [])
    (hblank : ∀ i, i ≠ 110 → i ≠ 132 → S.R (inverseCoreReg i) = [])
    (hsource : S.R 110 = cstream A (executionWidth p l (initialSchurTarget p u
      (boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 (haloBoundary s t (PhaseCellBand.width p u) 0 s).card) 2) 2)
        (chirpLine s F)++tail) :
    let B := haloBoundary s t (PhaseCellBand.width p u) 0 s
    let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    ∀ z : ZMod s → ℂ,
      Matrix.mulVec (fun i j => (realMatrix s t p u i j : ℂ)) z = (fun i => value q (F i)) →
      ∃ v' n, ∃ G : ZMod s → GaussianInt,
        v'.user = v.user ∧ n ≤ closedInverseCallerCost W p u l target s t ∧
        Exec (embTab inverseCoreReg (embTab boundaryFactorLegacyReg (embTab tableReg
          (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body))))))
          (closedInverseCaller hR hQ) (mk v S) n
          (mk v' {S with R := Function.update S.R 132 (cstream A w (chirpLine s G)++S.R 132)}) ∧
        ∀ i, ‖pairedCellRead q w (cstream A w (chirpLine s G)++S.R 132) i-z i‖ ≤ 1/(2 : ℝ)^target := by
  dsimp only
  let B := haloBoundary s t (PhaseCellBand.width p u) 0 s
  let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  let E := inverseExecutionExponent p l target B.card (PhaseCellBand.width p u)
  let initial : TblSt 25 A := inverseInputScalars p u l target s t 0 s
  let coreBody := embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg
    (embTab componentReg (embTab groupReg body))))
  let outerBody := embTab inverseCoreReg coreBody
  have hfit : ∀ i, initial.val i < 2^W := by
    have hroom : 2^15*(p+1)+8*E+2*(B.card+1)+4*(PhaseCellBand.width p u+1)+9 < 2^W := hprecisionRoom
    have hEl : 2*l+target ≤ E := by dsimp [E,inverseExecutionExponent]; omega
    have htW : t < 2^W := by nlinarith only [hgeometryRoom,Nat.zero_le (t*t)]
    have hsW : s < 2^W := by omega
    intro i
    fin_cases i <;> simp [initial,inverseInputScalars] <;> omega
  obtain ⟨v₁,S₁,n₁,scalars,hu₁,hn₁,he₁,hh₁,hkeep,hacc,hfit₁,hinp,hout,hL,hheaders,hframe⟩ :=
    installInverseHeaders_exec (body := outerBody) (p := p) (u := u) (l := l) (target := target)
      (s := s) (t := t) (a := 0) (b := s) inverseScalarReg inverseScalarReg_injective
      inverseMasterPort inverseMasterPort_injective inverseScalarReg_master wl hwl initial
      rfl rfl rfl rfl rfl rfl rfl rfl hst (Nat.zero_le s) (le_refl s) hband
      hbandRoom hgeometryRoom hprecisionRoom hfit v S hscalar
  let T₁ := embStk inverseCoreReg S₁
  have hhead (i : Fin 10) : T₁.R (inverseMasterCorePort i) =
      List.replicate (inverseMasterValues p u l target s t 0 s i) Node.tick := by
    have hb := hblank (inverseMasterCorePort i) (by fin_cases i <;> decide) (by fin_cases i <;> decide)
    simpa only [T₁,embStk,Function.comp_def,inverseMasterPort,hb,List.append_nil] using hheaders i
  have hclean (k : Fin 224) (hk : ∀ i, inverseMasterCorePort i ≠ k) (h110 : k ≠ 110) (h132 : k ≠ 132) :
      T₁.R k = [] := by
    exact (hframe (inverseCoreReg k) (fun r => inverseScalarReg_core r k)
      (fun i he => hk i (inverseCoreReg_injective he))).trans (hblank k h110 h132)
  have hleft₁ (k : Fin 224) : T₁.L k = [] := by change S₁.L (inverseCoreReg k) = []; rw [hL]; exact hleft k
  have hsource₁ : T₁.R 110 = cstream A w (chirpLine s F)++tail :=
    (hframe 110 (fun r => inverseScalarReg_core r 110) (by intro i; fin_cases i <;> decide)).trans hsource
  have hready := inverseHeaders_ready T₁ (cstream A w (chirpLine s F)++tail) hleft₁ hhead hclean hsource₁
  have hready' : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u bits 2) 2+1)
      q l s t u (PhaseCellBand.width p u) 0 0 (cstream A w (chirpLine s F)++tail)
      (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg T₁)))) := by
    simpa only [q,bits,B,executionPrecision,executionStagePrecision,← inverseExecutionExponent_eq] using hready
  have hc (k : Fin 224) (hk : ∀ i, inverseMasterCorePort i ≠ k) (h110 : k ≠ 110) (h132 : k ≠ 132) := hclean k hk h110 h132
  have h141 : T₁.R 141 = [] := by simpa [inverseMasterCorePort,inverseMasterValues] using hhead 8
  have h142 : (T₁.R 142).length = s := by simpa [inverseMasterCorePort,inverseMasterValues] using congrArg List.length (hhead 9)
  have hnew : ∀ i : Fin 224, 154 ≤ i.val → T₁.R i = [] := by
    intro i hi
    apply hc i
    · intro j
      intro he
      have hh := congrArg (fun k : Fin 224 => k.val) he
      have hlt : (inverseMasterCorePort j).val < 154 := by fin_cases j <;> decide
      omega
    · intro he; subst i; norm_num at hi
    · intro he; subst i; norm_num at hi
  intro z hz
  obtain ⟨v₂,n₂,G,hu₂,hn₂,he₂,herror⟩ := retainedInverse_spec (body := body) hR hQ hA
    hp hwidth hα hst hu hαu hθ hgap hbudget hband hpad F hF (embDn inverseCoreReg v₁) T₁ tail
    (hc 109 (by intro i; fin_cases i <;> decide) (by decide) (by decide))
    (hc 115 (by intro i; fin_cases i <;> decide) (by decide) (by decide))
    (hc 116 (by intro i; fin_cases i <;> decide) (by decide) (by decide)) hleft₁ hready' h141 h142
    (hc 0 (by intro i; fin_cases i <;> decide) (by decide) (by decide))
    (hc 139 (by intro i; fin_cases i <;> decide) (by decide) (by decide))
    (hc 127 (by intro i; fin_cases i <;> decide) (by decide) (by decide))
    (hc 138 (by intro i; fin_cases i <;> decide) (by decide) (by decide))
    (hc 143 (by intro i; fin_cases i <;> decide) (by decide) (by decide))
    (hc 147 (by intro i; fin_cases i <;> decide) (by decide) (by decide))
    (hc 151 (by intro i; fin_cases i <;> decide) (by decide) (by decide))
    (hc 153 (by intro i; fin_cases i <;> decide) (by decide) (by decide))
    (hc 152 (by intro i; fin_cases i <;> decide) (by decide) (by decide)) hnew z hz
  obtain ⟨v₂',hv₂',hu₂',he₂'⟩ := exec_emb_ovr (ι := id) (body' := outerBody) inverseCoreReg_injective
    (fun _ => rfl) he₂ v₁ rfl S₁ rfl
  let output := cstream A w (chirpLine s G)++S₁.R 132
  let S₂ : Stacks 264 A := {S₁ with R := Function.update S₁.R 132 output}
  have he₂'' : Exec outerBody (embProg inverseCoreReg id (retainedComplexBoundary hR hQ))
      (mk v₁ S₁) n₂ (mk v₂' S₂) := by
    convert he₂' using 1
    apply congrArg (mk v₂')
    rw [embOvr_updR inverseCoreReg_injective,embOvr_stk]
    rfl
  have hh₂ : tblHolds inverseScalarReg S₂ (tblRho W wl [] scalars) := by
    intro r
    have hr132 : inverseScalarReg r ≠ 132 := inverseScalarReg_core r 132
    simpa only [S₂,Function.update_of_ne hr132] using hh₁ r
  have hmasterLen (i : Fin 10) : (S₂.R (inverseMasterPort i)).length = inverseMasterValues p u l target s t 0 s i := by
    have h132 : inverseMasterPort i ≠ 132 := by fin_cases i <;> decide
    have hh : (S₁.R (inverseMasterPort i)).length = inverseMasterValues p u l target s t 0 s i := by
      simpa only [T₁,embStk,Function.comp_def,inverseMasterPort,List.length_replicate] using congrArg List.length (hhead i)
    simpa only [S₂,Function.update_of_ne h132] using hh
  obtain ⟨v₃,S₃,n₃,hu₃,hn₃,he₃,hh₃,hinp₃,hout₃,hL₃,hcore₃⟩ := releaseInverseCaller_exec (body := outerBody)
    wl hwl scalars initial (inverseMasterValues p u l target s t 0 s)
    (fun i hi => hkeep ⟨i.val,hi⟩)
    (by intro i hi; fin_cases i <;> first | (simp at hi; done) | rfl) hacc hfit₁ v₂' S₂ hh₂ hmasterLen
  have h132 : S₁.R 132 = S.R 132 := hframe 132 (fun r => inverseScalarReg_core r 132) (by intro i; fin_cases i <;> decide)
  have hfinal : S₃ = {S with R := Function.update S.R 132 (cstream A w (chirpLine s G)++S.R 132)} := by
    refine Stacks.ext (hinp₃.trans hinp) (hout₃.trans hout) (hL₃.trans hL) ?_
    funext k
    rcases inverseCallerReg_cover k with ⟨i,rfl⟩ | ⟨r,rfl⟩
    · rw [hcore₃]
      change (if inverseCoreReg i ∈ inverseMasterRegs then [] else S₂.R (inverseCoreReg i)) =
        Function.update S.R 132 (cstream A w (chirpLine s G)++S.R 132) (inverseCoreReg i)
      by_cases hi132 : inverseCoreReg i = 132
      · have hnot : inverseCoreReg i ∉ inverseMasterRegs := by rw [hi132]; decide
        rw [if_neg hnot]
        simp only [S₂,hi132,Function.update_self,output,h132]
      by_cases hi : inverseCoreReg i ∈ inverseMasterRegs
      · have hi110 : i ≠ 110 := by
          intro he
          subst i
          obtain ⟨j,_,hj⟩ := List.mem_map.mp hi
          have hne : inverseMasterPort j ≠ 110 := by fin_cases j <;> decide
          exact hne hj
        have hi132' : i ≠ 132 := by intro he; subst i; exact hi132 rfl
        simp [hi,Function.update_of_ne hi132,hblank i hi110 hi132']
      · have hports : ∀ j, inverseMasterPort j ≠ inverseCoreReg i := by
          intro j he; exact hi (List.mem_map.mpr ⟨j,List.mem_finRange j,he⟩)
        simp only [hi,ite_false,S₂,Function.update_of_ne hi132]
        exact hframe _ (fun r => inverseScalarReg_core r i) hports
    · rw [hh₃ r]
      change tblRho W wl [] initial r = Function.update S.R 132 (cstream A w (chirpLine s G)++S.R 132) (inverseScalarReg r)
      have hr132 : inverseScalarReg r ≠ 132 := inverseScalarReg_core r 132
      rw [Function.update_of_ne hr132]
      exact (hscalar r).symm
  refine ⟨v₃,n₁+(n₂+n₃),G,hu₃.trans (hu₂'.trans (hu₂.trans hu₁)),?_,?_,?_⟩
  · simpa only [closedInverseCallerCost,Nat.add_assoc] using Nat.add_le_add hn₁ (Nat.add_le_add hn₂ hn₃)
  · exact (Exec.seq he₁ (Exec.seq he₂'' he₃)).cast rfl (congrArg (mk v₃) hfinal)
  · intro i
    have hh : ‖pairedCellRead q w (cstream A w (chirpLine s G)++S₁.R 132) i-z i‖ ≤ 1/(2 : ℝ)^target := herror i
    simpa only [h132] using hh

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
