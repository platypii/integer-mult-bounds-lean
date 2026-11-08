module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicPackedNormalizationPair
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicRecoveredRows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRealRoundAccuracy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicReplicaProblems

/-! Actual recovered-field certificates supply both normalization calls.
Principal solutions, magnitude bounds and per-piece row errors are derived. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
open CyclicPackedNormalizationPlacement
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 907 Q A U}

theorem recoveredCyclicPackedNormalization_exec (hA : 4 ≤ A)
    {p l s t u target a n : ℕ} [NeZero s] {α d : ℝ}
    (axis : RecoveryAxisBounds s t p u l α d) (ha : a < s) (hn : n ≤ s) :
    let B := cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n
    let cellTarget := initialSchurTarget p u (boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 B.card) 2
    let q := executionPrecision p l cellTarget 2
    let w := executionWidth p l cellTarget 2
    ∀ (Fs : List (ZMod s → GaussianInt)) (hF : ∀ F ∈ Fs, ∀ i, ‖value q (F i)‖ ≤ (2 : ℝ)^2),
    let H := axis.cyclicLeftReplicaProblem cellTarget 2 a n ha Fs hF
    let K := axis.cyclicRightReplicaProblem cellTarget 2 a n hn Fs hF
    ∀ (fields : Fin Fs.length → ZMod s → GaussianInt),
    (∀ j, (∀ i, Fits w (fields j i)) ∧ (∀ i, (fields j i).im = 0) ∧
      ∀ x : ZMod s → ℝ, SchurDominance.Solves (realMatrix s t p u) (cyclicPrincipalVertices s a n) x
        (fun i => (value q (Fs.getD j.val (fun _ => 0) i)).re) →
      PhaseCellInterface.ErrorOn (cyclicPrincipalVertices s a n)
        (fun i => (value q (fields j i)).re) x (1/(2 : ℝ)^(target+1))) →
    ∀ (W : ℕ) (_ : 2*p+13 ≤ W) (wide : List (Fin (A+4))) (_ : wide.length = W)
      (v : HS 907 Q A U) (S : Stacks 850 A),
    ReplicaAssemblyControls H (gather false) 839 S → ReplicaAssemblyControls K (gather true) 838 S →
    S.R 848 = (List.ofFn (fun j => cstream A w (packedInterval a (min n (s-a)) (fields j)))).reverse.flatten →
    S.R 849 = (List.ofFn (fun j => cstream A w (packedInterval 0 (n-min n (s-a)) (fields j)))).reverse.flatten →
    let E := cyclicPackedNormalizationInput S wide
    let Gs := ((List.ofFn fields).reverse).map
      (fun D i => finalRoundWord w q p (inverseNormalizationShift p) (D i))
    ∃ (xs : List (ZMod s → ℝ)) (vf : HS 907 Q A U) (steps : ℕ),
      List.Forall₂ (fun F x => SchurDominance.Solves (realMatrix s t p u)
        (cyclicPrincipalVertices s a n) x (fun i => (value q (F i)).re)) Fs.reverse xs ∧
      vf.user = v.user ∧
      steps ≤ PackedRecoveryNormalization.normalizationCost p q W a (min n (s-a)) Fs.length+
        PackedRecoveryNormalization.normalizationCost p q W 0 (n-min n (s-a)) Fs.length ∧
      Exec body cyclicPackedNormalization (mk v E) steps
        (mk vf {E with R := (Function.update (Function.update E.R 848
          ((Gs.map (fun D => cstream A W (packedInterval a (min n (s-a)) D))).flatten)) 849
          ((Gs.map (fun D => cstream A W (packedInterval 0 (n-min n (s-a)) D))).flatten))}) ∧
      List.Forall₂ (fun x D => PhaseCellInterface.ErrorOn (haloVertices s a (a+min n (s-a)))
        (packedIntervalRead p W a (cstream A W (packedInterval a (min n (s-a)) D)))
        (fun i => ((2 : ℂ)^inverseNormalizationShift p)⁻¹*(x i : ℂ))
        (1/(2 : ℝ)^p+(1/(2 : ℝ)^(target+1))/(2 : ℝ)^inverseNormalizationShift p)) xs Gs ∧
      List.Forall₂ (fun x D => PhaseCellInterface.ErrorOn (haloVertices s 0 (n-min n (s-a)))
        (packedIntervalRead p W 0 (cstream A W (packedInterval 0 (n-min n (s-a)) D)))
        (fun i => ((2 : ℂ)^inverseNormalizationShift p)⁻¹*(x i : ℂ))
        (1/(2 : ℝ)^p+(1/(2 : ℝ)^(target+1))/(2 : ℝ)^inverseNormalizationShift p)) xs Gs := by
  dsimp only
  let B := cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n
  let cellTarget := initialSchurTarget p u (boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 B.card) 2
  let q := executionPrecision p l cellTarget 2
  let w := executionWidth p l cellTarget 2
  intro Fs hF
  let H := axis.cyclicLeftReplicaProblem cellTarget 2 a n ha Fs hF
  let K := axis.cyclicRightReplicaProblem cellTarget 2 a n hn Fs hF
  have hHp : H.p = p := rfl
  have hKp : K.p = p := rfl
  have hHq : H.precision = q := rfl
  have hKq : K.precision = q := rfl
  have hHw : H.wordWidth = w := rfl
  have hKw : K.wordWidth = w := rfl
  have hHo : H.origin = a := rfl
  have hKo : K.origin = 0 := rfl
  have hHs : H.span = min n (s-a) := rfl
  have hKs : K.span = n-min n (s-a) := rfl
  intro fields hfields W hW wide hwide v S controlsL controlsR hsrcL hsrcR
  obtain ⟨xs,hlen,hsol,hmag,haccuracy⟩ := cyclicRecoveredRows axis Fs hF fields
    (1/(2 : ℝ)^(target+1)) (fun j => (hfields j).2.2)
  let Ds := (List.ofFn fields).reverse
  have hDlen : Ds.length = Fs.length := by simp [Ds]
  have hreal : ∀ D ∈ Ds, ∀ i, (D i).im = 0 := by
    intro D hD
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp (List.mem_reverse.mp hD)
    exact (hfields j).2.1
  have hfits : ∀ D ∈ Ds, ∀ i, Fits w (D i) := by
    intro D hD
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp (List.mem_reverse.mp hD)
    exact (hfields j).1
  have hdim := cyclicRound_dimensions p u l target B.card
  have he : 1/(2 : ℝ)^(target+1) ≤ 1 := by
    exact (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
  have hleft : ∀ i ∈ haloVertices s a (a+min n (s-a)), i ∈ cyclicPrincipalVertices s a n := by
    intro i hi; exact Finset.mem_union_left _ hi
  have hright : ∀ i ∈ haloVertices s 0 (n-min n (s-a)), i ∈ cyclicPrincipalVertices s a n := by
    intro i hi; exact Finset.mem_union_right _ hi
  have hwordsL : S.R 848 = (Ds.map (fun D => cstream A w (packedInterval a (min n (s-a)) D))).flatten++[] := by
    simpa only [Ds,List.map_reverse,List.map_ofFn,Function.comp_def,List.append_nil] using hsrcL
  have hwordsR : S.R 849 = (Ds.map (fun D => cstream A w (packedInterval 0 (n-min n (s-a)) D))).flatten++[] := by
    simpa only [Ds,List.map_reverse,List.map_ofFn,Function.comp_def,List.append_nil] using hsrcR
  obtain ⟨vf,steps,hu,ht,hexec,_haccL,_haccR⟩ := cyclicPackedNormalization_exec (body := body) hA H K rfl rfl W
    hdim.1 hdim.2.2 hW (haloVertices s a (a+min n (s-a))) (haloVertices s 0 (n-min n (s-a)))
    (by intro i hi; exact (mem_haloVertices _ _ i).mp hi)
    (by intro i hi hj; exact (mem_haloVertices _ _ i).mpr ⟨hi,hj⟩)
    (by intro i hi; simpa only [hKo,hKs,Nat.zero_add] using (mem_haloVertices _ _ i).mp hi)
    (by intro i hi hj; exact (mem_haloVertices _ _ i).mpr ⟨hi,by simpa only [hKo,hKs,Nat.zero_add] using hj⟩)
    xs Ds hDlen hDlen (1/(2 : ℝ)^(target+1)) he
    (fun x hx i hi => hmag x hx i (hleft i hi))
    (fun x hx i hi => hmag x hx i (hright i hi)) hreal hfits [] [] wide hwide
    (List.Forall₂.imp (fun x D h i hi => h i (hleft i hi)) haccuracy)
    (List.Forall₂.imp (fun x D h i hi => h i (hright i hi)) haccuracy)
    v S controlsL controlsR hwordsL hwordsR
  have hwpos : 1 ≤ w := by
    dsimp only [w,executionWidth]
    omega
  have hsharpL := packedRealFinalRoundBatch_accuracy hA p q (inverseNormalizationShift p) w W (p+8)
    a (min n (s-a)) hdim.1 hwpos (by omega) (haloVertices s a (a+min n (s-a))) (by omega)
    (by intro i hi; exact (mem_haloVertices _ _ i).mp hi) xs Ds (1/(2 : ℝ)^(target+1)) he
    (fun x hx i hi => hmag x hx i (hleft i hi)) hreal hfits []
    (List.Forall₂.imp (fun x D h i hi => h i (hleft i hi)) haccuracy)
  have hsharpR := packedRealFinalRoundBatch_accuracy hA p q (inverseNormalizationShift p) w W (p+8)
    0 (n-min n (s-a)) hdim.1 hwpos (by omega) (haloVertices s 0 (n-min n (s-a))) (by omega)
    (by intro i hi; simpa only [Nat.zero_add] using (mem_haloVertices _ _ i).mp hi)
    xs Ds (1/(2 : ℝ)^(target+1)) he
    (fun x hx i hi => hmag x hx i (hright i hi)) hreal hfits []
    (List.Forall₂.imp (fun x D h i hi => h i (hright i hi)) haccuracy)
  refine ⟨xs,vf,steps,hsol,hu,?_,?_,?_,?_⟩
  · simpa only [hHp,hKp,hHq,hKq,hHo,hKo,hHs,hKs,hDlen] using ht
  · simpa only [hHp,hKp,hHq,hKq,hHw,hKw,hHo,hKo,hHs,hKs,Ds,List.append_nil] using hexec
  · simpa only [Ds,List.append_nil] using hsharpL
  · simpa only [Ds,List.append_nil] using hsharpR

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
