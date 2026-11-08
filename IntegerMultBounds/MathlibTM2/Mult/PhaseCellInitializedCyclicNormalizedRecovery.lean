module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializedCyclicCroppedRecovery
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPhysicalCyclicCommonNormalization
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicNormalizedRecoveryAccuracy
public import IntegerMultBounds.MathlibTM2.Host.EmbedUpdate

/-! Ordinary cyclic recovery normalizes and publishes at the router's common width.
The former narrow-only caller is restorable from commit 4c755426. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def initializedCyclicNormalizedRecovery (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 280 Q A U :=
  .seq (embProg cyclicSolverReg id (initializedCyclicCroppedRecovery hR hQ)) physicalCyclicCommonNormalization

theorem initializedCyclicNormalizedRecovery_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target a n W : ℕ} [NeZero s] {α d : ℝ}
    (axis : RecoveryAxisBounds s t p u l α d) (has : a < s) (hbs : n ≤ s) (hW : 2*p+13 ≤ W)
    (rhs : ZMod s → GaussianInt)
    (hrhs : ∀ i, ‖value (executionPrecision p l (initialSchurTarget p u
      (boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card) 2) 2) (rhs i)‖ ≤ (2 : ℝ)^2)
    (v : HS 280 Q A U) (S : Stacks 280 A) (tail : List (Fin (A+4)))
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u (boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card) 2) 2+1)
      (executionPrecision p l (initialSchurTarget p u (boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card) 2) 2) l s t u (PhaseCellBand.width p u) 0 0
      (cstream A (executionWidth p l (initialSchurTarget p u (boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2
        (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card) 2) 2) (chirpLine s rhs)++tail) (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg (embStk cyclicSolverReg S))))))
    (haMaster : (S.R 141).length = a) (hnMaster : (S.R 142).length = n)
    (hfresh : ∀ k ∈ [(109 : Fin 280),115,116,144,145,146], S.R k = [])
    (h0 : S.R 0 = [])
    (h139 : S.R 139 = [])
    (h127 : S.R 127 = []) (h138 : S.R 138 = []) (h143 : S.R 143 = []) (h147 : S.R 147 = [])
    (h151 : S.R 151 = []) (h152 : S.R 152 = []) (h153 : S.R 153 = [])
    (hleft : ∀ i : Fin 280, S.L i = [])
    (hwide : (S.R 279).length = W)
    (hnew : ∀ i : Fin 280, 154 ≤ i.val → i ≠ 279 → S.R i = []) :
    let band := PhaseCellBand.width p u
    let B := cyclicPrincipalBoundary s t band a n
    let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    ∃ v₀ S₀ m₀ v' S' m, ∃ columns : List (ZMod s → GaussianInt), ∃ G : ZMod s → GaussianInt,
      Exec (embTab cyclicSolverReg (embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg
        (embTab componentReg (embTab groupReg body))))))
        (embProg cyclicSolverReg id (initializedCyclicCroppedRecovery hR hQ)) (mk v S) m₀ (mk v₀ S₀) ∧
      m ≤ m₀+physicalCyclicCommonNormalizationCost p q a n W ∧ v'.user = v.user ∧
      Exec (embTab cyclicSolverReg (embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg
        (embTab componentReg (embTab groupReg body)))))) (initializedCyclicNormalizedRecovery hR hQ)
        (mk v S) m (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧ S'.R 110 = S.R 110 ∧
      (∀ k : Fin 280, 224 ≤ k.val → S'.R k = S.R k) ∧
      S'.R 132 = cstream A w (chirpLine s G)++(bandTableWords A w B (24*band+1) columns 0++S.R 132) ∧
      S'.R 147 = cstream A W (cyclicInterval a n
        (fun i => finalRoundWord w q p (inverseNormalizationShift p) (G i))) ∧
      (S'.R 147).length = n*W ∧
      (∀ x ∈ cyclicInterval a n (fun i => finalRoundWord w q p (inverseNormalizationShift p) (G i)),
        Fits (2*p+13) x) ∧
      ∀ x : ZMod s → ℝ,
        SchurDominance.Solves (realMatrix s t p u) (cyclicPrincipalVertices s a n) x
          (fun i => (value q (rhs i)).re) →
        PhaseCellInterface.ErrorOn (cyclicPrincipalVertices s a n)
          (cyclicIntervalRead p W a (S'.R 147))
          (fun i => ((2 : ℂ)^inverseNormalizationShift p)⁻¹*(x i : ℂ))
          (2/(2 : ℝ)^p+(1/(2 : ℝ)^(target+1))/(2 : ℝ)^inverseNormalizationShift p) := by
  dsimp only
  let band := PhaseCellBand.width p u
  let B := cyclicPrincipalBoundary s t band a n
  let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  let native := embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg
    (embTab componentReg (embTab groupReg body))))
  obtain ⟨va,Sa,ma,vb,Sb,mb,columns,G,hea,hmb,hvb,heb,hinp,hout,hL,h110,hfield,h147,hlen,
    hP,hq,h144,h145,h146,hfreshB,hreal,hfits,haccuracy⟩ := initializedCyclicCroppedRecovery_spec
      (body := body) hR hQ hA axis has hbs rhs hrhs (embDn cyclicSolverReg v) (embStk cyclicSolverReg S) tail hready
      haMaster hnMaster
      (by intro k hk
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
          rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
          · simpa [embStk,cyclicSolverReg] using hfresh 109 (by simp)
          · simpa [embStk,cyclicSolverReg] using hfresh 115 (by simp)
          · simpa [embStk,cyclicSolverReg] using hfresh 116 (by simp)
          · simpa [embStk,cyclicSolverReg] using hfresh 144 (by simp)
          · simpa [embStk,cyclicSolverReg] using hfresh 145 (by simp)
          · simpa [embStk,cyclicSolverReg] using hfresh 146 (by simp))
      h0 h139 h127 h138 h143 h147 h151 h152 h153
      (by intro i; exact hleft (cyclicSolverReg i))
      (by intro i hi
          apply hnew (cyclicSolverReg i) hi
          intro heq
          have hv := congrArg Fin.val heq
          have hi := i.isLt
          simp only [cyclicSolverReg] at hv
          omega)
  obtain ⟨vc,hvc,huC,heC⟩ := exec_emb_ovr (e := cyclicSolverReg) (ι := id)
    cyclicSolverReg_injective (body := native) (body' := embTab cyclicSolverReg native)
    (by intro f; rfl) heb v rfl S rfl
  let Sc := embOvr cyclicSolverReg Sb.get S
  have hproj : embStk cyclicSolverReg Sc = Sb := embStk_ovr cyclicSolverReg_injective Sb S
  have hread (k : Fin 280) (hk : k.val < 224) : Sc.R k = Sb.R ⟨k.val,hk⟩ := by
    exact congrArg (fun F => F.R ⟨k.val,hk⟩) hproj
  have hhigh (k : Fin 280) (hk : 224 ≤ k.val) : Sc.R k = S.R k := by
    exact (embOvr_off Sb.get S (by
      intro i heq
      have hv := congrArg Fin.val heq
      have hi := i.isLt
      simp only [cyclicSolverReg] at hv
      omega)).2
  have hw : w = 2*q+8 := by dsimp [w,q,executionWidth,executionPrecision]; omega
  change Sb.R 147 = cstream A w (cyclicInterval a n G) at h147
  change ∀ i, Fits w (G i) at hfits
  have hfits' : ∀ i, Fits (2*q+8) (G i) := by rw [←hw]; exact hfits
  have herror (x : ZMod s → ℝ)
      (hx : SchurDominance.Solves (realMatrix s t p u) (cyclicPrincipalVertices s a n) x
        (fun i => (value q (rhs i)).re)) :
      PhaseCellInterface.ErrorOn (cyclicPrincipalVertices s a n) (fun i => (value q (G i)).re) x
        (1/(2 : ℝ)^(target+1)) := by
    intro i hi
    have hr : cyclicIntervalRead q w a (Sb.R 147) i = value q (G i) := by
      rw [h147]
      simpa only [List.append_nil] using
        cyclicIntervalRead_eq q w a n (by omega) (by rw [hw]; omega) has G hfits [] i hi
    have herr := haccuracy x hx i hi
    dsimp only at herr ⊢
    rw [hr] at herr
    exact herr
  have hp : 0 < p := by have := axis.hp; omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  obtain ⟨x₀,hx₀⟩ := SchurDominance.solves_exists (realMatrix s t p u) (cyclicPrincipalVertices s a n)
    (1/(8*(p : ℝ))) (by positivity)
    (SchurDominance.dominates_mono _ Finset.univ _ _ (Finset.subset_univ _) axis.hdom)
    (fun i => (value q (rhs i)).re)
  have hmag : ∀ i ∈ cyclicPrincipalVertices s a n, ‖(x₀ i : ℂ)‖ ≤ 4*(2 : ℝ)^(p+8) := by
    intro i hi
    simpa only [Complex.norm_real] using cyclicPrincipal_round_magnitude hp axis.hdom rhs hrhs x₀ hx₀ i hi
  have hgood : PhaseCellInterface.ErrorOn (cyclicPrincipalVertices s a n)
      (cyclicIntervalRead q (2*q+8) a (cstream A (2*q+8) (cyclicInterval a n G)++[]))
      (fun i => (x₀ i : ℂ)) (1/(2 : ℝ)^(target+1)) := by
    intro i hi
    dsimp only
    rw [cyclicIntervalRead_eq q (2*q+8) a n (by omega) (by omega) has G hfits' [] i hi]
    have hv : value q (G i) = ((value q (G i)).re : ℂ) := by
      apply Complex.ext <;> simp only [value,hreal i,Int.cast_zero,zero_div,Complex.ofReal_re,Complex.ofReal_im]
    rw [hv,←Complex.ofReal_sub,Complex.norm_real]
    exact herror x₀ hx₀ i hi
  have hdim := cyclicRound_dimensions p u l target B.card
  obtain ⟨vd,md,hvd,hmd,hed,hrounded,_⟩ := physicalCyclicCommonNormalization_exec
    (body := embTab cyclicSolverReg native) (by omega) p q a n W hW hdim.1 hdim.2.2 has hbs G
    (fun i => (x₀ i : ℂ)) _ ((div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))) hmag [] [] hgood vc Sc
    (by simpa [hread 117 (by decide)] using hP)
    (by simpa [hread 119 (by decide)] using hq)
    (by simpa [hread 144 (by decide)] using h144)
    (by simpa [hread 145 (by decide)] using h145)
    (by simpa [hread 146 (by decide)] using h146)
    (by intro k hk
        have hk224 : k.val < 224 := by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
          rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        rw [hread k hk224]
        apply hfreshB
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
    (by intro k hk hne; rw [hhigh k hk]; exact hnew k (by omega) hne)
    (by rw [hhigh 279 (by decide)]; exact hwide)
    (by simpa [←hw,hread 147 (by decide)] using h147)
  let F : Stacks 280 A := {Sc with R := (Function.update Sc.R 147
    (cstream A W (cyclicInterval a n (fun i => finalRoundWord w q p (inverseNormalizationShift p) (G i)))))}
  have hed' : Exec (embTab cyclicSolverReg native) physicalCyclicCommonNormalization (mk vc Sc) md (mk vd F) := by
    simpa only [F,hw,List.append_nil] using hed
  refine ⟨vc,Sc,mb,vd,F,mb+md,columns,G,heC,Nat.add_le_add_left hmd mb,
    hvd.trans (huC.trans hvb),Exec.seq heC hed',hinp,hout,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact embOvr_left_of_eq S Sb hL
  · simpa [F,hread 110 (by decide),embStk,cyclicSolverReg] using h110
  · intro k hk
    have hne : k ≠ 147 := by intro heq; subst k; norm_num at hk
    simpa only [F,Function.update_of_ne hne] using hhigh k hk
  · simpa [F,hread 132 (by decide),embStk,cyclicSolverReg] using hfield
  · rfl
  · simp only [F,Function.update_self,length_cstream,cyclicInterval_length]
  · simpa only [←hw] using hrounded
  · intro x hx
    change PhaseCellInterface.ErrorOn (cyclicPrincipalVertices s a n)
      (cyclicIntervalRead p W a
        (cstream A W (cyclicInterval a n (fun i => finalRoundWord w q p (inverseNormalizationShift p) (G i)))))
      (fun i => ((2 : ℂ)^inverseNormalizationShift p)⁻¹*(x i : ℂ)) _
    have h : PhaseCellInterface.ErrorOn (cyclicPrincipalVertices s a n)
      (cyclicIntervalRead p W a
        (cstream A W (cyclicInterval a n (fun i => finalRoundWord (2*q+8) q p (inverseNormalizationShift p) (G i)))++[]))
      (fun i => ((2 : ℂ)^inverseNormalizationShift p)⁻¹*(x i : ℂ))
      (2/(2 : ℝ)^p+(1/(2 : ℝ)^(target+1))/(2 : ℝ)^inverseNormalizationShift p) := cyclicPrincipal_finalRound_accuracy (A := A) (l := l) (target := target) (by omega) hp has W hW axis.hdom rhs G hreal x []
      hrhs hfits' hx (herror x hx)
    simpa only [List.append_nil,←hw] using h

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
