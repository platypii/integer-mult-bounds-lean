module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryCompletion
public import IntegerMultBounds.MathlibTM2.Host.EmbedStock

/-! Lift the closed boundary completion into a caller bank. Exact two-port
framing preserves spectators, and placement adds no time or workspace. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.LayerMachine
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix ScalarPlacement
variable {T Q A s : ℕ} [NeZero s] {P U : Type}

theorem embeddedBoundaryCompletion_of_proper_exec (body : P → Pr P T Q A U)
    (e : Fin 117 → Fin T) (hinj : Function.Injective e)
    (p width W D band n : ℕ) (hA : 4 ≤ A) (hW : 2*p+13 ≤ W)
    (hwidth : 0 < width) (hroom : 3*width < s) (hvolumeFit : s*W < 2^D)
    (cropCount : Fin 3 → Fin 117)
    (hreg : ∀ slot, [cropCount slot,15,54,19,27,28,24,26].Nodup)
    (seedValue : Fin 117 → ℕ)
    (hvalues : ∀ j, seedValue (boundarySeedGlobals j) = ![s,width,W] j)
    (hfit : ∀ j, seedValue (boundarySeedGlobals j) < 2^D)
    (r : FamilyDispatchInput s A)
    (J : FamilyDispatchInput s A → (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (proper : CorePublicationClass s width)
    (hr : 0 < n*band) (hrw : n*band ≤ width)
    (hproper : proper.indices = coreGatherIndices s width (n*band) (width+2*(n*band)))
    (sourceTail outputTail : List (Fin (A+4))) (B : Stacks T A)
    (hready : BoundarySeamReady (s := s) p width W D r.inputs.length cropCount seedValue (embStk e B))
    (banks : List (List (List GaussianInt)))
    (hbanks : List.Forall₂ (SeamCropRows p width r J) (boundaryCropSchedule s width).reverse banks)
    (ambient : List (List (Fin (A+4))))
    (hgood : List.Forall₂ (fun target line => line.length = s*W ∧
      ∀ k ∈ proper.indices,
        (∀ i ∈ ownedCore s width k, ‖pairedCellRead p W line i‖ ≤ 1) ∧
        PhaseCellInterface.ErrorOn (ownedCore s width k) (pairedCellRead p W line) target (3/(2:ℝ)^p))
      (seamPublicationTargets p r J) ambient)
    (hsrc : B.R (e 95) = (banks.map (fun rows => cstream A (2*p+13) rows.flatten)).flatten++sourceTail)
    (hdst : B.R (e 96) = ambient.flatten++outputTail)
    (depth : ℕ) (v : HS T Q A U) :
    ∃ ambient : List (List (Fin (A+4))),
      List.Forall₂ (fun target line => line.length = s*W ∧
        (∀ i : ZMod s, ‖pairedCellRead p W line i‖ ≤ 1) ∧
        (∀ i : ZMod s, ‖pairedCellRead p W line i-target i‖ ≤ 3/(2:ℝ)^p))
        (seamPublicationTargets p r J) ambient ∧
      let F : Stacks T A := {B with R := (Function.update (Function.update B.R (e 95) sourceTail)
        (e 96) (ambient.flatten++outputTail))}
      ∃ v' n, v'.user = v.user ∧ n ≤ 3*boundarySeamBudget r.inputs.length D s W+1 ∧
        mnSize (mk v' F) ≤ mnSize (mk v B) ∧
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v B)+depth+
          13*boundarySeamBudget r.inputs.length D s W) depth
          (embProg e (fun f : Empty => nomatch f) (boundarySeamPublication cropCount))
          (mk v B) n (mk v' F) := by
  obtain ⟨u,F,m,hu,hm,hF,hsource,hgood,hstock,he⟩ := boundaryCompletion_of_proper_exec
    (fun f : Empty => nomatch f) p width W D band n hA hW hwidth hroom hvolumeFit
    cropCount hreg seedValue hvalues hfit r J proper hr hrw hproper sourceTail outputTail
    (embStk e B) hready banks hbanks ambient hgood hsrc hdst depth (embDn e v)
  obtain ⟨output,houtput,haccuracy⟩ := hgood
  have hframe : F = {embStk e B with R := (Function.update
      (Function.update (embStk e B).R 95 sourceTail) 96 (output.flatten++outputTail))} := by
    obtain ⟨remaining,lines,hremaining,hpending,hstate⟩ := hF
    have hnil : remaining = [] := List.eq_nil_of_length_eq_zero (by simpa using hremaining.length_eq.symm)
    rw [hstate]
    have hout : lines.flatten++outputTail = output.flatten++outputTail := by
      simpa only [hstate,Function.update_self] using houtput
    simp only [hnil,List.map_nil,List.flatten_nil,List.nil_append,hout]
  obtain ⟨v',hdn,huser,htrace⟩ := exec_emb_ovr_within_stock e hinj
    (ι := fun f : Empty => nomatch f) (body' := body) (by intro f; exact nomatch f)
    he v rfl B rfl
  have hbigstock := embOvr_stock_le e hinj u v' F B 0 (by simpa only [mnSize,mk,Nat.add_zero] using hstock)
  rw [hframe,embOvr_updateR_updateR hinj] at htrace hbigstock
  exact ⟨output,haccuracy,v',m,huser.trans hu,hm,by simpa only [mnSize,mk,Nat.add_zero] using hbigstock,htrace⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
