module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCoreArchiveComplex
public import IntegerMultBounds.MathlibTM2.Host.ExtendStacks
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoreArchiveStock

/-! Crop the actual normalized left archive to a fitting owned core. The crop
reuses restored normalization workspace and returns forward replica order. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 909 Q A U}

def normalizedCorePublication : Pr P 909 Q A U :=
  packedCoreArchiveFromDimensions 907 908 121 851 852 853 848 850 854 855 856 857 906 858 859 860

def normalizedCorePublicationInput (S : Stacks 907 A) (radius core : List (Fin (A+4))) : Stacks 909 A :=
  let E := extendStacks (by decide : 907 ≤ 909) S
  {E with R := (Function.update (Function.update E.R 907 radius) 908 core)}

theorem normalizedCorePublicationInput_view (S : Stacks 907 A) (radius core : List (Fin (A+4))) :
    embStk (Fin.castLE (by decide : 907 ≤ 909)) (normalizedCorePublicationInput S radius core) = S := by
  refine Stacks.ext rfl rfl ?_ ?_
  · funext i
    simp [embStk,normalizedCorePublicationInput,extendStacks,i.isLt]
  · funext i
    have h907 : Fin.castLE (by decide : 907 ≤ 909) i ≠ (907 : Fin 909) := by
      intro heq; have hv := congrArg Fin.val heq; simp only [Fin.val_castLE] at hv; omega
    have h908 : Fin.castLE (by decide : 907 ≤ 909) i ≠ (908 : Fin 909) := by
      intro heq; have hv := congrArg Fin.val heq; simp only [Fin.val_castLE] at hv; omega
    simp [embStk,normalizedCorePublicationInput,Function.update_of_ne h907,
      Function.update_of_ne h908,extendStacks,i.isLt]

theorem normalizedCorePublicationInput_override (S G : Stacks 907 A) (radius core : List (Fin (A+4))) :
    embOvr (Fin.castLE (by decide : 907 ≤ 909)) G.get (normalizedCorePublicationInput S radius core) =
      normalizedCorePublicationInput G radius core := by
  let e := Fin.castLE (by decide : 907 ≤ 909)
  let B := normalizedCorePublicationInput S radius core
  let C := normalizedCorePublicationInput G radius core
  have hview : embStk e (embOvr e G.get B) = G :=
    embStk_ovr (Fin.castLE_injective (by decide : 907 ≤ 909)) G B
  have htarget : embStk e C = G := normalizedCorePublicationInput_view G radius core
  have hports (i : Fin 909) : (embOvr e G.get B).L i = C.L i ∧ (embOvr e G.get B).R i = C.R i := by
    by_cases hi : i.val < 907
    · let j : Fin 907 := ⟨i.val,hi⟩
      have he : e j = i := Fin.ext rfl
      have hL := congrArg (fun D : Stacks 907 A => D.L j) hview
      have hR := congrArg (fun D : Stacks 907 A => D.R j) hview
      have hcL := congrArg (fun D : Stacks 907 A => D.L j) htarget
      have hcR := congrArg (fun D : Stacks 907 A => D.R j) htarget
      simp only [embStk_L] at hL hcL
      simp only [embStk_R] at hR hcR
      simpa only [he] using And.intro (hL.trans hcL.symm) (hR.trans hcR.symm)
    · have hoff : ∀ j : Fin 907, e j ≠ i := by
        intro j heq
        have hv := congrArg Fin.val heq
        change j.val = i.val at hv
        omega
      have hf := embOvr_off G.get B hoff
      refine ⟨hf.1.trans ?_,hf.2.trans ?_⟩
      · simp [B,C,normalizedCorePublicationInput,extendStacks,hi]
      · simp [B,C,normalizedCorePublicationInput,extendStacks,Function.update_apply,hi]
  exact Stacks.ext rfl rfl (funext fun i => (hports i).1) (funext fun i => (hports i).2)

theorem normalizedIntervalPublication_exec {s : ℕ} [NeZero s]
    (p W start coreRows radius : ℕ) (hleft : radius ≤ start)
    (hright : start+coreRows+radius ≤ s)
    (Zs : List (ZMod s → ℂ)) (Ds : List (ZMod s → GaussianInt)) (e : ℝ)
    (hgood : List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn
      (haloVertices s (start-radius) (start+coreRows+radius))
      (packedIntervalRead p W (start-radius)
        (cstream A W (packedInterval (start-radius) (coreRows+2*radius) D))) z e) Zs Ds)
    (v : HS 909 Q A U) (S : Stacks 907 A)
    (radiusWord coreWord : List (Fin (A+4))) (hR : radiusWord.length = radius)
    (hL : coreWord.length = coreRows)
    (hsrc : S.R 848 = (Ds.map (fun D => cstream A W
      (packedInterval (start-radius) (coreRows+2*radius) D))).flatten)
    (hw : (S.R 906).length = W) (hN : (S.R 121).length = Ds.length)
    (hfresh : ∀ i : Fin 907, 850 ≤ i.val → i.val < 906 → S.R i = []) :
    let E := normalizedCorePublicationInput S radiusWord coreWord
    ∃ vf n, vf.user = v.user ∧
      n ≤ packedCoreArchiveControlsCost radius (coreRows) W Ds.length+
        (Ds.length*(packedCoreArchiveStepCost radius (coreRows)
          (coreRows+2*radius) W+3)+2)+
        (2*(radius*W+coreRows*W+(coreRows+2*radius))+7) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v E)+0+
        normalizedCorePublicationWorkspace radius (coreRows) W Ds.length) 0
        normalizedCorePublication (mk v E) n
        (mk vf {E with R := (Function.update (Function.update E.R 848 []) 850
          ((Ds.reverse.map (fun D => cstream A W (packedInterval start coreRows D))).flatten))}) ∧
      Exec body normalizedCorePublication (mk v E) n
        (mk vf {E with R := (Function.update (Function.update E.R 848 []) 850
          ((Ds.reverse.map (fun D => cstream A W (packedInterval start coreRows D))).flatten))}) ∧
      (let F := {E with R := (Function.update (Function.update E.R 848 []) 850
          ((Ds.reverse.map (fun D => cstream A W (packedInterval start coreRows D))).flatten))}
       (F.R 121).length = Ds.length ∧ (F.R 908).length = coreRows ∧
       (F.R 906).length = W ∧ ∀ i ∈ ([(851 : Fin 909),852,853,854,855,856,857]), F.R i = []) ∧
      List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn (haloVertices s start (start+coreRows))
        (packedIntervalRead p W (start) (cstream A W (packedInterval start coreRows D))) z e)
        Zs.reverse Ds.reverse := by
  dsimp only
  let E := normalizedCorePublicationInput S radiusWord coreWord
  have hread (i : Fin 909) (hi : i.val < 907) : E.R i = S.R ⟨i.val,hi⟩ := by
    have h907 : i ≠ 907 := by
      intro heq
      have hv := congrArg Fin.val heq
      omega
    have h908 : i ≠ 908 := by
      intro heq
      have hv := congrArg Fin.val heq
      omega
    simp only [E,normalizedCorePublicationInput,Function.update_of_ne h907,Function.update_of_ne h908]
    exact dite_eq_left hi
  have hE850 : E.R 850 = [] := (hread 850 (by decide)).trans (hfresh 850 (by decide) (by decide))
  obtain ⟨vf,F,n,hu,hn,hex,hs,hd,hi,ho,hl,hframe,haccuracy⟩ := packedIntervalCoreArchiveFromDimensions_complex_exec
    (body := body) 907 908 121 851 852 853 848 850 854 855 856 857 906 858 859 860 (by decide +kernel)
    v E p W start coreRows radius hleft hright Ds.reverse []
    (by simpa only [List.reverse_reverse,List.append_nil] using (hread 848 (by decide)).trans hsrc)
    (by simpa [E,normalizedCorePublicationInput] using hR)
    (by simpa [E,normalizedCorePublicationInput] using hL)
    (by exact (congrArg List.length (hread 906 (by decide))).trans hw)
    (by simpa only [List.length_reverse] using (congrArg List.length (hread 121 (by decide))).trans hN)
    (by intro i hi
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals
          rw [hread _ (by decide)]
          exact hfresh _ (by decide) (by decide))
    Zs.reverse e (List.forall₂_reverse_iff.mpr hgood)
  have hF : F = {E with R := (Function.update (Function.update E.R 848 []) 850
      ((Ds.reverse.map (fun D => cstream A W (packedInterval start coreRows D))).flatten))} := by
    refine Stacks.ext hi ho hl ?_
    funext i
    by_cases hs' : i = 848
    · subst i; simpa only [Function.update_of_ne (by decide : (848 : Fin 909) ≠ 850),Function.update_self] using hs
    by_cases hd' : i = 850
    · subst i; simpa only [Function.update_self,hE850,List.append_nil] using hd
    simpa only [Function.update_of_ne hd',Function.update_of_ne hs'] using hframe i hs' hd'
  have hcost : n ≤ normalizedCorePublicationCost radius (coreRows) W Ds.length := by
    simpa only [List.length_reverse,normalizedCorePublicationCost] using hn
  have htraffic := hcost.trans (normalizedCorePublicationCost_le radius (coreRows) W Ds.length)
  have hstock := mn_native_exec_within hex 13 (packedCoreArchiveFromDimensions_native ..) 0
    (mnSize (mk v E)+0+normalizedCorePublicationWorkspace radius (coreRows) W Ds.length)
    (by unfold normalizedCorePublicationWorkspace; omega)
  refine ⟨vf,n,hu,by simpa only [List.length_reverse] using hn,
    hstock.cast rfl (congrArg (mk vf) hF),?_,?_,?_⟩
  · exact hex.cast rfl (congrArg (mk vf) hF)
  · refine ⟨?_,?_,?_,?_⟩
    · simpa only [Function.update_of_ne (by decide : (121 : Fin 909) ≠ 850),
        Function.update_of_ne (by decide : (121 : Fin 909) ≠ 848)] using
        (congrArg List.length (hread 121 (by decide))).trans hN
    · simpa [E,normalizedCorePublicationInput] using hL
    · simpa only [Function.update_of_ne (by decide : (906 : Fin 909) ≠ 850),
        Function.update_of_ne (by decide : (906 : Fin 909) ≠ 848)] using
        (congrArg List.length (hread 906 (by decide))).trans hw
    · intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals
        simp [Function.update_apply]
        rw [hread _ (by decide)]
        exact hfresh _ (by decide) (by decide)
  · simpa only [hE850,List.append_nil] using haccuracy

theorem normalizedCorePublication_exec {s : ℕ} [NeZero s]
    (p W coreWidth k radius : ℕ) (hleft : radius ≤ coreStart coreWidth k)
    (hright : coreStart coreWidth k+coreLength s coreWidth k+radius ≤ s)
    (Zs : List (ZMod s → ℂ)) (Ds : List (ZMod s → GaussianInt)) (e : ℝ)
    (hgood : List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn
      (haloVertices s (coreStart coreWidth k-radius) (coreStart coreWidth k+coreLength s coreWidth k+radius))
      (packedIntervalRead p W (coreStart coreWidth k-radius)
        (cstream A W (packedInterval (coreStart coreWidth k-radius) (coreLength s coreWidth k+2*radius) D))) z e) Zs Ds)
    (v : HS 909 Q A U) (S : Stacks 907 A)
    (radiusWord coreWord : List (Fin (A+4))) (hR : radiusWord.length = radius)
    (hL : coreWord.length = coreLength s coreWidth k)
    (hsrc : S.R 848 = (Ds.map (fun D => cstream A W
      (packedInterval (coreStart coreWidth k-radius) (coreLength s coreWidth k+2*radius) D))).flatten)
    (hw : (S.R 906).length = W) (hN : (S.R 121).length = Ds.length)
    (hfresh : ∀ i : Fin 907, 850 ≤ i.val → i.val < 906 → S.R i = []) :
    let E := normalizedCorePublicationInput S radiusWord coreWord
    ∃ vf n, vf.user = v.user ∧
      n ≤ packedCoreArchiveControlsCost radius (coreLength s coreWidth k) W Ds.length+
        (Ds.length*(packedCoreArchiveStepCost radius (coreLength s coreWidth k)
          (coreLength s coreWidth k+2*radius) W+3)+2)+
        (2*(radius*W+coreLength s coreWidth k*W+(coreLength s coreWidth k+2*radius))+7) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v E)+0+
        normalizedCorePublicationWorkspace radius (coreLength s coreWidth k) W Ds.length) 0
        normalizedCorePublication (mk v E) n
        (mk vf {E with R := (Function.update (Function.update E.R 848 []) 850
          ((Ds.reverse.map (fun D => cstream A W (ownedCoreWords coreWidth k D))).flatten))}) ∧
      Exec body normalizedCorePublication (mk v E) n
        (mk vf {E with R := (Function.update (Function.update E.R 848 []) 850
          ((Ds.reverse.map (fun D => cstream A W (ownedCoreWords coreWidth k D))).flatten))}) ∧
      (let F := {E with R := (Function.update (Function.update E.R 848 []) 850
          ((Ds.reverse.map (fun D => cstream A W (ownedCoreWords coreWidth k D))).flatten))}
       (F.R 121).length = Ds.length ∧ (F.R 908).length = coreLength s coreWidth k ∧
       (F.R 906).length = W ∧ ∀ i ∈ ([(851 : Fin 909),852,853,854,855,856,857]), F.R i = []) ∧
      List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn (ownedCore s coreWidth k)
        (packedIntervalRead p W (coreStart coreWidth k) (cstream A W (ownedCoreWords coreWidth k D))) z e)
        Zs.reverse Ds.reverse := by
  simpa only [ownedCore,ownedCoreWords,packedInterval] using
    normalizedIntervalPublication_exec (body := body) p W (coreStart coreWidth k)
      (coreLength s coreWidth k) radius hleft hright Zs Ds e hgood v S
      radiusWord coreWord hR hL hsrc hw hN hfresh

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
