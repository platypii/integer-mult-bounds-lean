module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOuterPublicationMask
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationPorts
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingHeadersFrame

/-! Publish the selected real halo line from the retained interior and boundary prefixes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def publishHalo : Pr P₀ 144 Q A U :=
  .seq installCouplingHeaders (.seq outerPublicationMask (.seq publicationSplit
    (.seq publicationSelectFromHeaders releaseCouplingHeaders)))

def publishHaloCost (P q s t u band a b : ℕ) : ℕ :=
  let w := 2*q+8
  installCouplingHeadersCost P q s t u band a b+
    (closedPublicationMaskCost P q w s t u band a b+
      (publicationSplitCost s w+(publicationSelectFromHeadersCost s w+
        releaseCouplingHeadersCost P q s t u band a b)))

theorem publishHalo_exec {P N q l s t u band a b : ℕ} [NeZero s]
    (hA : 4 ≤ A) (hst : s < t) (has : a ≤ s) (hbs : b ≤ s) (hband : band ≤ s)
    (D C : ZMod s → GaussianInt) (tail input : List (Fin (A+4)))
    (v : HS 144 Q A U) (S : Stacks 144 A)
    (hready : LengthKeyReady P N q l s t u band 0 0 input S)
    (ha : (S.R 141).length = a) (hb : (S.R 142).length = b) (h143 : S.R 143 = [])
    (hsource : S.R 132 = cstream A (2*q+8) (chirpLine s D)++
      (cstream A (2*q+8) (chirpLine s C)++tail)) :
    let G := fun i => realPartWord (publicationField t band a b D C i)
    ∃ v' n, v'.user = v.user ∧ n ≤ publishHaloCost P q s t u band a b ∧
      Exec (embTab groupReg body) publishHalo (mk v S) n
        (mk v' {S with R := Function.update S.R 132 (cstream A (2*q+8) (chirpLine s G)++tail)}) ∧
      LengthKeyReady P N q l s t u band 0 0 input
        {S with R := Function.update S.R 132 (cstream A (2*q+8) (chirpLine s G)++tail)} := by
  dsimp only
  let w := 2*q+8
  let G := fun i => realPartWord (publicationField t band a b D C i)
  let result := cstream A w (chirpLine s G)++tail
  obtain ⟨v₀,hu₀,he₀,hcoupling⟩ := installCouplingHeaders_exec (body := embTab groupReg body)
    P N q l s t u band a b input v S hready ha hb
  let S₀ : Stacks 144 A := {S with R := couplingHeadersR P q s t u band a b S.R}
  have hoff (k : Fin 144) (hk : k ∉ couplingHeaderRegisters) : S₀.R k = S.R k :=
    couplingHeadersR_off P q s t u band a b S.R k hk
  have h0mask : S₀.R 109 = [] := by
    rw [hoff 109 (by decide)]
    exact hready.blank 109 (by decide) (by decide) (by decide)
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := outerPublicationMask_exec (body := body)
    hst has hbs hband input v₀ S₀ hcoupling
  let S₁ : Stacks 144 A := {S₀ with R := Function.update S₀.R 109 (publicationMaskSymbols A s t band a b)}
  have hs : (S.R 121).length = s := by
    simpa [groupHeaderValue] using hready.masters (121,97) (by simp [groupHeaderCopies])
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := publicationSplit_exec (body := embTab groupReg body)
    s w (cstream A w (chirpLine s D)) (cstream A w (chirpLine s C)++tail) v₁ S₁
    (by rw [show S₁.R 121 = S₀.R 121 by simp [S₁],hoff 121 (by decide)]; exact hs)
    (by simpa [S₁,embStk,groupReg,w] using hcoupling.width)
    (by rw [show S₁.R 132 = S₀.R 132 by simp [S₁],hoff 132 (by decide)]; exact hsource)
    (by simp)
    (by rw [show S₁.R 131 = S₀.R 131 by simp [S₁],hoff 131 (by decide)]; exact hready.fresh 131 (by simp))
    (by rw [show S₁.R 134 = S₀.R 134 by simp [S₁],hoff 134 (by decide)]; exact hready.fresh 134 (by simp))
    (by rw [show S₁.R 135 = S₀.R 135 by simp [S₁],hoff 135 (by decide)]; exact hready.fresh 135 (by simp))
    (by rw [show S₁.R 136 = S₀.R 136 by simp [S₁],hoff 136 (by decide)]; exact hready.fresh 136 (by simp))
    (by rw [show S₁.R 137 = S₀.R 137 by simp [S₁],hoff 137 (by decide)]; exact hready.fresh 137 (by simp))
  let S₂ : Stacks 144 A := {S₁ with R := (Function.update
    (Function.update S₁.R 132 (cstream A w (chirpLine s C)++tail)) 137 (cstream A w (chirpLine s D)))}
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := publicationSelectFromHeaders_exec (body := embTab groupReg body)
    (s := s) (t := t) (band := band) (a := a) (b := b) (w := w) hA hst hbs D C tail v₂ S₂
    (by simpa [S₂,S₁,hoff 121 (by decide)] using hs)
    (by simpa [S₂,S₁,embStk,groupReg,w] using hcoupling.width)
    (by simp [S₂,S₁]) (by simp [S₂]) (by simp [S₂])
    (by simpa [S₂,S₁,hoff 143 (by decide)] using h143)
    (by simpa [S₂,S₁,hoff 140 (by decide)] using hready.fresh 140 (by simp))
    (by simpa [S₂,S₁,hoff 134 (by decide)] using hready.fresh 134 (by simp))
    (by simpa [S₂,S₁,hoff 135 (by decide)] using hready.fresh 135 (by simp))
  let S₃ : Stacks 144 A := {S₀ with R := Function.update S₀.R 132 result}
  have he₃' : Exec (embTab groupReg body) publicationSelectFromHeaders (mk v₂ S₂) n₃ (mk v₃ S₃) := by
    convert he₃ using 1
    apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk109 : k = 109 <;> by_cases hk137 : k = 137 <;> by_cases hk132 : k = 132 <;>
      simp [S₃,S₂,S₁,hk109,hk137,hk132,h0mask,hoff 137 (by decide),hready.fresh 137 (by simp),result,G]
  let Sbase : Stacks 144 A := {S with R := Function.update S.R 132 result}
  have hreadyBase : LengthKeyReady P N q l s t u band 0 0 input Sbase := hready.update_output result
  have hblank : ∀ k ∈ couplingHeaderRegisters, Sbase.R k = [] := by
    intro k hk
    have hk117 : k.val < 117 := by
      simp only [couplingHeaderRegisters,List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hk93 : k ≠ 93 := by intro he; subst k; norm_num [couplingHeaderRegisters] at hk
    have hk110 : k ≠ 110 := by intro he; subst k; norm_num [couplingHeaderRegisters] at hk
    exact hreadyBase.blank k hk117 hk93 hk110
  obtain ⟨v₄,hu₄,he₄⟩ := releaseCouplingHeaders_exec (body := embTab groupReg body)
    P q s t u band a b v₃ Sbase hblank
  have hstate : S₃ = {Sbase with R := couplingHeadersR P q s t u band a b Sbase.R} := by
    refine Stacks.ext rfl rfl rfl ?_
    change Function.update (couplingHeadersR P q s t u band a b S.R) 132 result =
      couplingHeadersR P q s t u band a b (Function.update S.R 132 result)
    exact (couplingHeadersR_update P q s t u band a b S.R 132 result (by decide)).symm
  rw [← hstate] at he₄
  refine ⟨v₄,installCouplingHeadersCost P q s t u band a b+
      (n₁+(n₂+(n₃+releaseCouplingHeadersCost P q s t u band a b))),
    hu₄.trans (hu₃.trans (hu₂.trans (hu₁.trans hu₀))),?_,
    Exec.seq he₀ (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃' he₄))),hreadyBase⟩
  change installCouplingHeadersCost P q s t u band a b+
      (n₁+(n₂+(n₃+releaseCouplingHeadersCost P q s t u band a b))) ≤
    installCouplingHeadersCost P q s t u band a b+
      (closedPublicationMaskCost P q w s t u band a b+
        (publicationSplitCost s w+(publicationSelectFromHeadersCost s w+
          releaseCouplingHeadersCost P q s t u band a b)))
  have hn₁' : n₁ ≤ closedPublicationMaskCost P q w s t u band a b := by simpa only [w] using hn₁
  have hn₃' : n₃ ≤ publicationSelectFromHeadersCost s w := by simpa only [w] using hn₃
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
