module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedBandCollection
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetireResidentColumn
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCollectFoldedBand

/-! Generate the clipped controls, collect the band entries and release every control. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 151 Q A U}

def collectRetireColumn : Pr P 151 Q A U := .seq preparedBandCollection retireResidentColumn

noncomputable def collectRetireColumnCost {s : ℕ} [NeZero s]
    (B : Finset (ZMod s)) (q V band n : ℕ) : ℕ :=
  preparedBandCollectionCost B q V band n+retireResidentColumnCost q s

theorem collectRetireColumn_exec {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (q V band n : ℕ)
    (hA : 4 ≤ A) (hs : s ≤ 2^V) (hn : n < B.card) (C : ZMod s → GaussianInt)
    (pageTail tail : List (Fin (A+4))) (v : HS 151 Q A U) (S : Stacks 151 A)
    (hindex : (S.R 0).length = n) (hwidth : (S.R 115).length = V)
    (hband : (S.R 124).length = band) (hrows : (S.R 116).length = B.card)
    (hpage : S.R 109 = cstream A V ((bFoldOrder s B).map
      (fun k : ZMod s => (⟨(k.val : ℤ),0⟩ : GaussianInt)))++pageTail)
    (hq : (S.R 119).length = q)
    (hsMaster : (S.R 121).length = s)
    (hsource : S.R 110 = cstream A (2*q+8) (chirpLine s C)++tail)
    (hfresh : ∀ k ∈ [(94 : Fin 151),106,131,134,135,136,137,138,139,140], S.R k = [])
    (hblank : ∀ r : Fin 151, 1 ≤ r.val → r.val < 7 → S.R r = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ collectRetireColumnCost B q V band n ∧
      Exec body collectRetireColumn (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R 0 []) 110 tail) 132
          (cstream A (2*q+8) ((foldedBandRows B (12*band+1) n).reverse.map C)++S.R 132))}) := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := preparedBandCollection_exec (body := body) B q V band n hA hs hn C
    pageTail tail v S hindex hwidth hband hrows hpage hq hsource (by
      intro k hk
      exact hfresh k (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢; tauto)) hblank
  let output := cstream A (2*q+8) ((foldedBandRows B (12*band+1) n).reverse.map C)++S.R 132
  let S₁ : Stacks 151 A := {S with R := Function.update (Function.update S.R 0 []) 132 output}
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := retireResidentColumn_exec (body := body) q s
    (cstream A (2*q+8) (chirpLine s C)) tail (by simp) v₁ S₁
    (by simpa [S₁] using hq) (by simpa [S₁] using hsMaster) (by simpa [S₁] using hsource) (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> simpa [S₁] using hfresh _ (by simp))
  refine ⟨v₂,m₁+m₂,hu₂.trans hu₁,Nat.add_le_add hm₁ hm₂,
    (Exec.seq he₁ he₂).cast rfl ?_⟩
  apply congrArg (mk v₂)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases hk0 : k = 0 <;> by_cases hk110 : k = 110 <;> by_cases hk132 : k = 132 <;>
    simp [S₁,output,hk0,hk110,hk132]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
