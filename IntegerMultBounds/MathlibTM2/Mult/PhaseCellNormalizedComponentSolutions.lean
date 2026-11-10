module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPhysicalNormalizedCoreAssembly
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedComponentSolutions
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHalfCount

/-! Principal-solution uniqueness identifies the actual scalar core targets
with the two component halves consumed by the existing complex assembly. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem componentSolution_normalized {s : ℕ} (j : ℕ)
    (y : (ZMod s → GaussianInt) → ZMod s → ℝ) :
    componentSolution (fun F i => (((2 : ℂ)^j)⁻¹*(y F i : ℂ)).re) =
      (fun F i => ((2 : ℂ)^j)⁻¹*componentSolution y F i) := by
  have hscale : ((2 : ℂ)^j)⁻¹ = (((2 : ℝ)^j)⁻¹ : ℝ) := by simp
  funext F i
  apply Complex.ext <;>
    simp only [componentSolution,hscale,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
      Complex.ofReal_im,mul_zero,zero_mul,add_zero,sub_zero]

theorem normalizedIntervalSolutions_certificate {A s : ℕ} [NeZero s]
    (M : Matrix (ZMod s) (ZMod s) ℝ) (principal : Finset (ZMod s)) (μ : ℝ)
    (hμ : 0 < μ) (hdom : SchurDominance.DominatesOn M principal μ)
    (p q d j W start rows : ℕ) (hcore : haloVertices s start (start+rows) ⊆ principal)
    (Fs : List (ZMod s → GaussianInt)) (y : (ZMod s → GaussianInt) → ZMod s → ℝ)
    (hy : ∀ F ∈ complexComponentFields Fs, SchurDominance.Solves M principal (y F)
      (fun i => (value q ((2 : GaussianInt)^d*F i)).re))
    (xs : List (ZMod s → ℝ)) (Ds : List (ZMod s → GaussianInt)) (e : ℝ)
    (hsol : List.Forall₂ (fun F x => SchurDominance.Solves M principal x
      (fun i => (value q (F i)).re))
      ((complexComponentFields Fs).map (fun F i => (2 : GaussianInt)^d*F i)) xs)
    (hgood : List.Forall₂ (fun x D => PhaseCellInterface.ErrorOn (haloVertices s start (start+rows))
      (packedIntervalRead p W (start) (cstream A W (packedInterval start rows D)))
      (fun i => ((2 : ℂ)^j)⁻¹*(x i : ℂ)) e) xs Ds) :
    List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn (haloVertices s start (start+rows))
      (fun i => (packedIntervalRead p W (start)
        (cstream A W (packedInterval start rows D)) i).re) z e)
      (complexComponentTargets (Fs.map (fun F i => ((2 : ℂ)^j)⁻¹*componentSolution y F i))) Ds := by
  rw [←componentSolution_normalized j y,componentSolution_targets]
  apply List.forall₂_map_left_iff.mpr
  have hlen : (complexComponentFields Fs).length = xs.length := by simpa only [List.length_map] using hsol.length_eq
  apply List.forall₂_of_length_eq_of_get (hlen.trans hgood.length_eq)
  intro i hi hj
  have hix : i < xs.length := by omega
  have his : i < ((complexComponentFields Fs).map (fun F i => (2 : GaussianInt)^d*F i)).length := by
    simpa only [List.length_map] using hi
  have hs : SchurDominance.Solves M principal (xs.get ⟨i,hix⟩)
      (fun k => (value q ((2 : GaussianInt)^d*((complexComponentFields Fs).get ⟨i,hi⟩) k)).re) := by
    simpa only [List.get_eq_getElem,List.getElem_map] using hsol.get his hix
  intro z hz
  have hx := SchurDominance.solves_unique M principal μ hμ hdom (xs.get ⟨i,hix⟩)
    (y ((complexComponentFields Fs).get ⟨i,hi⟩)) _ hs
    (hy _ (List.get_mem _ _)) z (hcore hz)
  have hc := (Complex.abs_re_le_norm
    (packedIntervalRead p W (start) (cstream A W (packedInterval start rows (Ds.get ⟨i,hj⟩))) z-
      ((2 : ℂ)^j)⁻¹*((xs.get ⟨i,hix⟩) z : ℂ))).trans ((hgood.get hix hj) z hz)
  simpa only [Real.norm_eq_abs,Complex.sub_re,hx] using hc

theorem normalizedComponentSolutions_certificate {A s : ℕ} [NeZero s]
    (M : Matrix (ZMod s) (ZMod s) ℝ) (principal : Finset (ZMod s)) (μ : ℝ)
    (hμ : 0 < μ) (hdom : SchurDominance.DominatesOn M principal μ)
    (p q d j W coreWidth k : ℕ) (hcore : ownedCore s coreWidth k ⊆ principal)
    (Fs : List (ZMod s → GaussianInt)) (y : (ZMod s → GaussianInt) → ZMod s → ℝ)
    (hy : ∀ F ∈ complexComponentFields Fs, SchurDominance.Solves M principal (y F)
      (fun i => (value q ((2 : GaussianInt)^d*F i)).re))
    (xs : List (ZMod s → ℝ)) (Ds : List (ZMod s → GaussianInt)) (e : ℝ)
    (hsol : List.Forall₂ (fun F x => SchurDominance.Solves M principal x
      (fun i => (value q (F i)).re))
      ((complexComponentFields Fs).map (fun F i => (2 : GaussianInt)^d*F i)) xs)
    (hgood : List.Forall₂ (fun x D => PhaseCellInterface.ErrorOn (ownedCore s coreWidth k)
      (packedIntervalRead p W (coreStart coreWidth k) (cstream A W (ownedCoreWords coreWidth k D)))
      (fun i => ((2 : ℂ)^j)⁻¹*(x i : ℂ)) e) xs Ds) :
    List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn (ownedCore s coreWidth k)
      (fun i => (packedIntervalRead p W (coreStart coreWidth k)
        (cstream A W (ownedCoreWords coreWidth k D)) i).re) z e)
      (complexComponentTargets (Fs.map (fun F i => ((2 : ℂ)^j)⁻¹*componentSolution y F i))) Ds := by
  simpa only [ownedCore,ownedCoreWords,packedInterval] using
    normalizedIntervalSolutions_certificate M principal μ hμ hdom p q d j W
      (coreStart coreWidth k) (coreLength s coreWidth k) hcore Fs y hy xs Ds e hsol hgood

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 909 Q A U}

def normalizedComponentSolutionsAssembly : Pr P 909 Q A U :=
  .seq (halfCount 121 856 857) (.seq (normalizedCoreAssembly 857) (uclear 857))

theorem assembleNormalizedIntervalSolutions_exec {s : ℕ} [NeZero s]
    (hA : 4 ≤ A)
    (M : Matrix (ZMod s) (ZMod s) ℝ) (principal : Finset (ZMod s)) (μ : ℝ)
    (hμ : 0 < μ) (hdom : SchurDominance.DominatesOn M principal μ)
    (p q d j W start rows target : ℕ) (hcore : haloVertices s start (start+rows) ⊆ principal)
    (hfit : start+rows ≤ s)
    (Fs : List (ZMod s → GaussianInt)) (y : (ZMod s → GaussianInt) → ZMod s → ℝ)
    (hy : ∀ F ∈ complexComponentFields Fs, SchurDominance.Solves M principal (y F)
      (fun i => (value q ((2 : GaussianInt)^d*F i)).re))
    (xs : List (ZMod s → ℝ)) (Ds : List (ZMod s → GaussianInt))
    (hsol : List.Forall₂ (fun F x => SchurDominance.Solves M principal x
      (fun i => (value q (F i)).re))
      ((complexComponentFields Fs).map (fun F i => (2 : GaussianInt)^d*F i)) xs)
    (hgood : List.Forall₂ (fun x D => PhaseCellInterface.ErrorOn (haloVertices s start (start+rows))
      (packedIntervalRead p W (start) (cstream A W (packedInterval start rows D)))
      (fun i => ((2 : ℂ)^j)⁻¹*(x i : ℂ))
      (1/(2 : ℝ)^p+(1/(2 : ℝ)^(target+1))/(2 : ℝ)^j)) xs Ds)
    (tail : List (Fin (A+4))) (v : HS 909 Q A U) (S : Stacks 909 A)
    (hscalar : (S.R 121).length = Ds.length)
    (hrows : (S.R 908).length = rows) (hwidth : (S.R 906).length = W)
    (hsrc : S.R 850 = (Ds.map (fun D => cstream A W (packedInterval start rows D))).flatten++tail)
    (hclean : ∀ i ∈ ([(851 : Fin 909),852,853,854,855,856,857]), S.R i = []) :
    let Gs := pairedComponentFields (Ds.take Fs.length) (Ds.drop Fs.length)
    Gs.length = Fs.length ∧
    ∃ vf n, vf.user = v.user ∧
      n ≤ (6*Fs.length+4)+((rows*(4*W+9)+4)+
        (Fs.length*(16*(rows*W)+9)+14)+(2*(rows*W)+2))+
        (2*Fs.length+2) ∧
      Exec body normalizedComponentSolutionsAssembly (mk v S) n
        (mk vf {S with R := (Function.update S.R 850
          ((Gs.map (fun D => cstream A W (packedInterval start rows D))).flatten++tail))}) ∧
      List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn (haloVertices s start (start+rows))
        (packedIntervalRead p W (start) (cstream A W (packedInterval start rows D)++tail)) z
        (2/(2 : ℝ)^p+(1/(2 : ℝ)^target)/(2 : ℝ)^j))
        (Fs.map (fun F i => ((2 : ℂ)^j)⁻¹*componentSolution y F i)) Gs := by
  dsimp only
  have hcert := normalizedIntervalSolutions_certificate M principal μ hμ hdom p q d j W start rows
    hcore Fs y hy xs Ds _ hsol hgood
  have hDlen : Ds.length = 2*Fs.length := by
    have hlen := hsol.length_eq.trans hgood.length_eq
    simpa only [List.length_map,complexComponentFields_length] using hlen.symm
  obtain ⟨vi,hui,hei⟩ := halfCount_exec (body := body) (count := 121) (saved := 856) (dst := 857)
    (by decide) Fs.length v S (hscalar.trans hDlen) (hclean 856 (by simp))
  let E : Stacks 909 A := {S with R := Function.update S.R 857 (List.replicate Fs.length tick)}
  have hei' : Exec body (halfCount 121 856 857) (mk v S) (6*Fs.length+4) (mk vi E) := by
    simpa only [E,hclean 857 (by simp),List.append_nil] using hei
  obtain ⟨hlen,vf,m,huf,hm,hex,haccuracy⟩ := normalizedIntervalAssembly_exec (body := body) 857 (by decide +kernel) hA
    p W start rows target j hfit (Fs.map (fun F i => ((2 : ℂ)^j)⁻¹*componentSolution y F i)) Ds hcert
    tail vi E (by simp [E]) (by simpa [E] using hrows) (by simpa [E] using hwidth)
    (by simpa [E] using hsrc)
    (by intro i hi
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl <;> simpa [E] using hclean _ (by simp))
  let Gs := pairedComponentFields (Ds.take Fs.length) (Ds.drop Fs.length)
  let ys := (Gs.map (fun D => cstream A W (packedInterval start rows D))).flatten++tail
  let F : Stacks 909 A := {E with R := Function.update E.R 850 ys}
  have hlen' : Gs.length = Fs.length := by simpa only [List.length_map] using hlen
  have hm' : m ≤ (rows*(4*W+9)+4)+
      (Fs.length*(16*(rows*W)+9)+14)+(2*(rows*W)+2) := by
    simpa only [List.length_map] using hm
  have hex' : Exec body (normalizedCoreAssembly 857) (mk vi E) m (mk vf F) := by
    simpa only [F,ys,Gs,List.length_map] using hex
  obtain ⟨vz,huz,hez⟩ := uclear_exec body 857 vf F
  have hez' : Exec body (uclear 857) (mk vf F) (2*Fs.length+2)
      (mk vz {S with R := Function.update S.R 850 ys}) := by
    have hf : {F with R := Function.update F.R 857 []} = {S with R := Function.update S.R 850 ys} := by
      refine Stacks.ext rfl rfl rfl ?_
      funext i
      by_cases hi : i = 857
      · subst i; simp [hclean 857 (by simp)]
      simp [F,E,Function.update_apply,hi]
    have hc : (F.R 857).length = Fs.length := by simp [F,E]
    exact hez.cast (by rw [hc]) (congrArg (mk vz) hf)
  refine ⟨hlen',vz,(6*Fs.length+4)+(m+(2*Fs.length+2)),huz.trans (huf.trans hui),by omega,?_,?_⟩
  · simpa only [normalizedComponentSolutionsAssembly,ys,Gs] using Exec.seq hei' (Exec.seq hex' hez')
  · simpa only [List.length_map] using haccuracy

theorem assembleNormalizedComponentSolutions_exec {s : ℕ} [NeZero s]
    (hA : 4 ≤ A)
    (M : Matrix (ZMod s) (ZMod s) ℝ) (principal : Finset (ZMod s)) (μ : ℝ)
    (hμ : 0 < μ) (hdom : SchurDominance.DominatesOn M principal μ)
    (p q d j W coreWidth k target : ℕ) (hcore : ownedCore s coreWidth k ⊆ principal)
    (hfit : coreStart coreWidth k+coreLength s coreWidth k ≤ s)
    (Fs : List (ZMod s → GaussianInt)) (y : (ZMod s → GaussianInt) → ZMod s → ℝ)
    (hy : ∀ F ∈ complexComponentFields Fs, SchurDominance.Solves M principal (y F)
      (fun i => (value q ((2 : GaussianInt)^d*F i)).re))
    (xs : List (ZMod s → ℝ)) (Ds : List (ZMod s → GaussianInt))
    (hsol : List.Forall₂ (fun F x => SchurDominance.Solves M principal x
      (fun i => (value q (F i)).re))
      ((complexComponentFields Fs).map (fun F i => (2 : GaussianInt)^d*F i)) xs)
    (hgood : List.Forall₂ (fun x D => PhaseCellInterface.ErrorOn (ownedCore s coreWidth k)
      (packedIntervalRead p W (coreStart coreWidth k) (cstream A W (ownedCoreWords coreWidth k D)))
      (fun i => ((2 : ℂ)^j)⁻¹*(x i : ℂ))
      (1/(2 : ℝ)^p+(1/(2 : ℝ)^(target+1))/(2 : ℝ)^j)) xs Ds)
    (tail : List (Fin (A+4))) (v : HS 909 Q A U) (S : Stacks 909 A)
    (hscalar : (S.R 121).length = Ds.length)
    (hrows : (S.R 908).length = coreLength s coreWidth k) (hwidth : (S.R 906).length = W)
    (hsrc : S.R 850 = (Ds.map (fun D => cstream A W (ownedCoreWords coreWidth k D))).flatten++tail)
    (hclean : ∀ i ∈ ([(851 : Fin 909),852,853,854,855,856,857]), S.R i = []) :
    let Gs := pairedComponentFields (Ds.take Fs.length) (Ds.drop Fs.length)
    Gs.length = Fs.length ∧
    ∃ vf n, vf.user = v.user ∧
      n ≤ (6*Fs.length+4)+((coreLength s coreWidth k*(4*W+9)+4)+
        (Fs.length*(16*(coreLength s coreWidth k*W)+9)+14)+(2*(coreLength s coreWidth k*W)+2))+
        (2*Fs.length+2) ∧
      Exec body normalizedComponentSolutionsAssembly (mk v S) n
        (mk vf {S with R := (Function.update S.R 850
          ((Gs.map (fun D => cstream A W (ownedCoreWords coreWidth k D))).flatten++tail))}) ∧
      List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn (ownedCore s coreWidth k)
        (packedIntervalRead p W (coreStart coreWidth k) (cstream A W (ownedCoreWords coreWidth k D)++tail)) z
        (2/(2 : ℝ)^p+(1/(2 : ℝ)^target)/(2 : ℝ)^j))
        (Fs.map (fun F i => ((2 : ℂ)^j)⁻¹*componentSolution y F i)) Gs := by
  simpa only [ownedCore,ownedCoreWords,packedInterval] using
    assembleNormalizedIntervalSolutions_exec (body := body) hA M principal μ hμ hdom p q d j W
      (coreStart coreWidth k) (coreLength s coreWidth k) target hcore hfit Fs y hy xs Ds hsol hgood
      tail v S hscalar hrows hwidth hsrc hclean

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
