module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublishedHalo
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedResidualControls

/-! Publish the recovered real halo field in ordinary scratch outside both retained cache keys. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 256 Q A U}

noncomputable def placedPublishHalo : Pr P₀ 256 Q A U :=
  embProg couplingSourceReg Empty.elim (publishHalo (P₀ := Empty))

theorem placedPublishHalo_exec {P N q l s t u band a b : ℕ} [NeZero s]
    (hA : 4 ≤ A) (hst : s < t) (has : a ≤ s) (hbs : b ≤ s) (hband : band ≤ s)
    (D C : ZMod s → GaussianInt) (tail input : List (Fin (A+4)))
    (v : HS 256 Q A U) (S : Stacks 256 A)
    (hready : LengthKeyReady P N q l s t u band 0 0 input (embStk couplingSourceReg S))
    (ha : (S.R 141).length = a) (hb : (S.R 142).length = b) (h143 : S.R 143 = [])
    (hsource : S.R 132 = cstream A (2*q+8) (chirpLine s D)++
      (cstream A (2*q+8) (chirpLine s C)++tail)) :
    let G := fun i => realPartWord (publicationField t band a b D C i)
    ∃ v' n, v'.user = v.user ∧ n ≤ publishHaloCost P q s t u band a b ∧
      Exec body placedPublishHalo (mk v S) n
        (mk v' {S with R := Function.update S.R 132 (cstream A (2*q+8) (chirpLine s G)++tail)}) ∧
      LengthKeyReady P N q l s t u band 0 0 input
        (embStk couplingSourceReg {S with R := Function.update S.R 132 (cstream A (2*q+8) (chirpLine s G)++tail)}) := by
  dsimp only
  obtain ⟨vi,n,hu,hn,he,hready'⟩ := publishHalo_exec (body := fun p : Empty => nomatch p)
    hA hst has hbs hband D C tail input (embDn couplingSourceReg v) (embStk couplingSourceReg S)
    hready ha hb h143 hsource
  obtain ⟨v',hv',hu',he'⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    couplingSourceReg_injective (fun p => nomatch p) he v rfl S rfl
  refine ⟨v',n,hu'.trans hu,hn,he'.cast rfl ?_,?_⟩
  · apply congrArg (mk v')
    rw [embOvr_updR couplingSourceReg_injective,embOvr_stk]
    rfl
  · have hproj := embStk_updateR_inner couplingSourceReg couplingSourceReg_injective S 132
      (cstream A (2*q+8) (chirpLine s (fun i => realPartWord (publicationField t band a b D C i)))++tail)
    change embStk couplingSourceReg {S with R := Function.update S.R 132 _} = _ at hproj
    rw [hproj]
    exact hready'

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
