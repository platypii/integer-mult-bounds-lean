module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedComplexBatchAssembly
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCorePublication

/-! Pair the forward normalized scalar cores with the manuscript arithmetic
budget. Only one core byte ruler is generated, shared by the whole batch. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 909 Q A U}

def normalizedCoreAssembly (replicas : Fin 909) : Pr P 909 Q A U :=
  .seq (unaryProduct 908 906 851 854 855)
    (.seq (pairComplexKey replicas 851 852 850 853 854 855) (uclear 851))

theorem normalizedCoreAssembly_exec {s : ℕ} [NeZero s]
    (replicas : Fin 909) (hreg : [replicas,908,906,851,852,850,853,854,855].Nodup) (hA : 4 ≤ A)
    (p W coreWidth k target j : ℕ) (hfit : coreStart coreWidth k+coreLength s coreWidth k ≤ s)
    (Zs : List (ZMod s → ℂ)) (Ds : List (ZMod s → GaussianInt))
    (hgood : List.Forall₂ (fun y D => PhaseCellInterface.ErrorOn (ownedCore s coreWidth k)
      (fun i => (packedIntervalRead p W (coreStart coreWidth k)
        (cstream A W (ownedCoreWords coreWidth k D)) i).re) y
      (1/(2 : ℝ)^p+(1/(2 : ℝ)^(target+1))/(2 : ℝ)^j)) (complexComponentTargets Zs) Ds)
    (tail : List (Fin (A+4))) (v : HS 909 Q A U) (S : Stacks 909 A)
    (hreplicas : (S.R replicas).length = Zs.length)
    (hcore : (S.R 908).length = coreLength s coreWidth k) (hwidth : (S.R 906).length = W)
    (hsrc : S.R 850 = (Ds.map (fun D => cstream A W (ownedCoreWords coreWidth k D))).flatten++tail)
    (hclean : ∀ i ∈ ([(851 : Fin 909),852,853,854,855]), S.R i = []) :
    let Gs := pairedComponentFields (Ds.take Zs.length) (Ds.drop Zs.length)
    Gs.length = Zs.length ∧
    ∃ vf n, vf.user = v.user ∧
      n ≤ (coreLength s coreWidth k*(4*W+9)+4)+
        (Zs.length*(16*(coreLength s coreWidth k*W)+9)+14)+(2*(coreLength s coreWidth k*W)+2) ∧
      Exec body (normalizedCoreAssembly replicas) (mk v S) n
        (mk vf {S with R := (Function.update S.R 850
          ((Gs.map (fun D => cstream A W (ownedCoreWords coreWidth k D))).flatten++tail))}) ∧
      List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn (ownedCore s coreWidth k)
        (packedIntervalRead p W (coreStart coreWidth k) (cstream A W (ownedCoreWords coreWidth k D)++tail)) z
        (2/(2 : ℝ)^p+(1/(2 : ℝ)^target)/(2 : ℝ)^j)) Zs Gs := by
  dsimp only
  have hr := hreg
  regs_ne hr
  obtain ⟨vi,mi,hui,hmi,hei⟩ := unaryProduct_exec (body := body)
    (by decide : ([(908 : Fin 909),906,851,854,855]).Nodup) v S (hclean 854 (by simp)) (hclean 855 (by simp))
  let E : Stacks 909 A := {S with R := (Function.update S.R 851
    (List.replicate (coreLength s coreWidth k*W) tick))}
  have hei' : Exec body (unaryProduct 908 906 851 854 855) (mk v S) mi (mk vi E) := by
    simpa [E,hcore,hwidth,hclean 851 (by simp)] using hei
  have hmi' : mi ≤ coreLength s coreWidth k*(4*W+9)+4 := by
    simpa only [hcore,hwidth] using hmi
  obtain ⟨hlen,vf,m,huf,hm,hex,haccuracy⟩ := packedComplexBatchAssembly_exec (body := body)
    (by regs_nodup : [replicas,851,852,850,853,854,855].Nodup) hA p W (coreStart coreWidth k)
    (coreLength s coreWidth k) (ownedCore s coreWidth k) hfit
    (by intro i hi; exact (mem_haloVertices _ _ i).mp hi) Zs Ds
    (1/(2 : ℝ)^p+(1/(2 : ℝ)^(target+1))/(2 : ℝ)^j) [] tail
    (by simpa only [ownedCoreWords,packedInterval,List.append_nil] using hgood) vi E
    (by simpa [E,‹replicas ≠ 851›] using hreplicas) (by simp [E])
    (by simpa [E,ownedCoreWords,packedInterval] using hsrc)
    (by simpa [E] using hclean 852 (by simp)) (by simpa [E] using hclean 853 (by simp))
    (by simpa [E] using hclean 854 (by simp)) (by simpa [E] using hclean 855 (by simp))
  let Gs := pairedComponentFields (Ds.take Zs.length) (Ds.drop Zs.length)
  let ys := (Gs.map (fun D => cstream A W (ownedCoreWords coreWidth k D))).flatten++tail
  let F : Stacks 909 A := {E with R := Function.update E.R 850 ys}
  obtain ⟨vz,huz,hez⟩ := uclear_exec body 851 vf F
  have hez' : Exec body (uclear 851) (mk vf F) (2*(coreLength s coreWidth k*W)+2)
      (mk vz {S with R := Function.update S.R 850 ys}) := by
    have hf : {F with R := Function.update F.R 851 []} = {S with R := Function.update S.R 850 ys} := by
      refine Stacks.ext rfl rfl rfl ?_
      funext i
      by_cases hi : i = 851
      · subst i; simp [hclean 851 (by simp)]
      simp [F,E,Function.update_apply,hi]
    have hlenF : (F.R 851).length = coreLength s coreWidth k*W := by simp [F,E]
    exact hez.cast (by rw [hlenF]) (congrArg (mk vz) hf)
  have hhalf : 1/(2 : ℝ)^(target+1)+1/(2 : ℝ)^(target+1) = 1/(2 : ℝ)^target := by
    rw [pow_succ]
    ring
  have hbudget : (1/(2 : ℝ)^p+(1/(2 : ℝ)^(target+1))/(2 : ℝ)^j)+
      (1/(2 : ℝ)^p+(1/(2 : ℝ)^(target+1))/(2 : ℝ)^j) =
      2/(2 : ℝ)^p+(1/(2 : ℝ)^target)/(2 : ℝ)^j := by
    calc
      _ = 2/(2 : ℝ)^p+(1/(2 : ℝ)^(target+1)+1/(2 : ℝ)^(target+1))/(2 : ℝ)^j := by ring
      _ = _ := by rw [hhalf]
  refine ⟨hlen,vz,mi+(m+(2*(coreLength s coreWidth k*W)+2)),huz.trans (huf.trans hui),by omega,?_,?_⟩
  · simpa only [normalizedCoreAssembly,ys,Gs,ownedCoreWords,packedInterval] using Exec.seq hei' (Exec.seq hex hez')
  · simpa only [ownedCoreWords,packedInterval,hbudget] using haccuracy

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
