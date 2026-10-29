module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFramedBoundaryRhsFold
public import IntegerMultBounds.MathlibTM2.Host.Embed

/-! Place the unchanged numerical fold beside the retained packed-cell masters. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN.PhaseCellMatrix

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

def packedBoundaryFoldPlacement (i : Fin 148) : Fin 168 :=
  if i = 94 then 130 else if i = 130 then 94 else ⟨i.val,by omega⟩

theorem packedBoundaryFoldPlacement_injective : Function.Injective packedBoundaryFoldPlacement := by
  intro i j he
  have hv := congrArg Fin.val he
  unfold packedBoundaryFoldPlacement at hv
  split_ifs at hv <;> simp_all only
  all_goals omega

def packedBoundaryRhsFold : Pr P 168 Q A U :=
  embProg packedBoundaryFoldPlacement Empty.elim (retainedBoundaryRhsFold (P₀ := Empty))

theorem packedBoundaryRhsFold_exec (s : ℕ) [NeZero s] (B : Finset (ZMod s))
    (C : ZMod s → GaussianInt) (w : ℕ) (v : HS 168 Q A U) (S : Stacks 168 A)
    (hsource : S.R 143 = cstream A w ((bOrder s B).map C))
    (hwidth : (S.R 130).length = w) (hcount : (S.R 116).length = B.card)
    (hfloor : (S.R 0).length = B.card/2)
    (hparity : (S.R 2).length = (B.card+1)/2-B.card/2)
    (hbytes : (S.R 3).length = (B.card+1)/2*w)
    (hblank : ∀ r : Fin 168, 6 ≤ r.val → r.val < 77 → S.R r = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ 60*(B.card+1)*w+60*B.card+60 ∧
      Exec body packedBoundaryRhsFold (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R 143 [])
          6 (cstream A w ((bFoldOrder s B).map C)))}) := by
  obtain ⟨v₁,m,hu₁,hm,he⟩ := framedBoundaryRhsFold_exec
    (body := fun p : Empty => nomatch p) s B C w
    (embDn packedBoundaryFoldPlacement v) (embStk packedBoundaryFoldPlacement S)
    hsource hwidth hcount hfloor hparity hbytes (by
      intro r hr6 hr77
      have hn94 : r ≠ 94 := by intro hh; have hv := congrArg Fin.val hh; norm_num at hv; omega
      have hn130 : r ≠ 130 := by intro hh; have hv := congrArg Fin.val hh; norm_num at hv; omega
      simpa [embStk,packedBoundaryFoldPlacement,hn94,hn130] using hblank ⟨r.val,by omega⟩ hr6 hr77)
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    packedBoundaryFoldPlacement_injective (fun p => nomatch p) he v rfl S rfl
  refine ⟨v₂,m,hu₂.trans hu₁,hm,he₂.cast rfl ?_⟩
  apply congrArg (mk v₂)
  let T₀ := embStk packedBoundaryFoldPlacement S
  let T₁ : Stacks 148 A := {T₀ with R := Function.update T₀.R 143 []}
  let T₂ : Stacks 148 A := {T₁ with R := Function.update T₁.R 6 (cstream A w ((bFoldOrder s B).map C))}
  change embOvr packedBoundaryFoldPlacement T₂.get S = _
  dsimp only [T₂]
  rw [embOvr_updR packedBoundaryFoldPlacement_injective]
  dsimp only [T₁,T₀]
  rw [embOvr_updR packedBoundaryFoldPlacement_injective,embOvr_stk]
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
