module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCollectRetireColumn
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTableWorkspace
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

def retainedColumnCollection : Pr P 154 Q A U :=
  .seq (ucopy 151 0 135) (embProg tableReg id collectRetireColumn)

noncomputable def retainedColumnCollectionCost {s : ℕ} [NeZero s]
    (B : Finset (ZMod s)) (q V band n : ℕ) : ℕ :=
  (4*n+4)+collectRetireColumnCost B q V band n

theorem retainedColumnCollection_exec {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (q V band n : ℕ)
    (hA : 4 ≤ A) (hs : s ≤ 2^V) (hn : n < B.card) (C : ZMod s → GaussianInt)
    (pageTail tail : List (Fin (A+4))) (v : HS 154 Q A U) (S : Stacks 154 A)
    (hindex : (S.R 151).length = n) (hwidth : (S.R 115).length = V)
    (hband : (S.R 124).length = band) (hrows : (S.R 116).length = B.card)
    (hpage : S.R 109 = cstream A V ((bFoldOrder s B).map
      (fun k : ZMod s => (⟨(k.val : ℤ),0⟩ : GaussianInt)))++pageTail)
    (hq : (S.R 119).length = q)
    (hsMaster : (S.R 121).length = s)
    (hsource : S.R 110 = cstream A (2*q+8) (chirpLine s C)++tail)
    (h0 : S.R 0 = [])
    (hfresh : ∀ k ∈ [(94 : Fin 154),106,131,134,135,136,137,138,139,140], S.R k = [])
    (hblank : ∀ r : Fin 154, 1 ≤ r.val → r.val < 7 → S.R r = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ retainedColumnCollectionCost B q V band n ∧
      Exec (embTab tableReg body) retainedColumnCollection (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R 110 tail) 132
          (cstream A (2*q+8) ((foldedBandRows B (12*band+1) n).reverse.map C)++S.R 132))}) := by
  obtain ⟨v₁,hu₁,he₁⟩ := ucopy_exec (embTab tableReg body) (a := 151) (b := 0) (t := 135)
    (by decide) (by decide) (by decide) v S (hfresh 135 (by simp))
  let S₁ : Stacks 154 A := {S with R := Function.update S.R 0 (List.replicate n tick)}
  have he₁' : Exec (embTab tableReg body) (ucopy 151 0 135) (mk v S) (4*n+4) (mk v₁ S₁) := by
    simpa [S₁,hindex,h0] using he₁
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := collectRetireColumn_exec (body := body) B q V band n hA hs hn C pageTail tail
    (embDn tableReg v₁) (embStk tableReg S₁)
    (by simp [embStk,tableReg,S₁]) (by simpa [embStk,tableReg,S₁] using hwidth)
    (by simpa [embStk,tableReg,S₁] using hband) (by simpa [embStk,tableReg,S₁] using hrows)
    (by simpa [embStk,tableReg,S₁] using hpage) (by simpa [embStk,tableReg,S₁] using hq)
    (by simpa [embStk,tableReg,S₁] using hsMaster) (by simpa [embStk,tableReg,S₁] using hsource) (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simpa [embStk,tableReg,S₁] using hfresh _ (by simp)) (by
      intro k hk1 hk7
      have hk0 : k ≠ 0 := by omega
      have hne : tableReg k ≠ 0 := by
        change tableReg k ≠ tableReg 0
        exact fun h => hk0 (tableReg_injective h)
      simpa [embStk,Function.comp_def,S₁,hne] using hblank (tableReg k) hk1 hk7)
  obtain ⟨v₃,hu₃,he₃⟩ := tableExec_threePorts collectRetireColumn v₁ S₁ v₂ m₂ 0 110 132 _ _ _ hu₂ he₂
  refine ⟨v₃,(4*n+4)+m₂,hu₃.trans hu₁,Nat.add_le_add_left hm₂ _,
    (Exec.seq he₁' he₃).cast rfl ?_⟩
  apply congrArg (mk v₃)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases hk0 : k = 0 <;> by_cases hk110 : k = 110 <;> by_cases hk132 : k = 132 <;>
    simp [S₁,embStk,Function.comp_def,tableReg,hk0,hk110,hk132,h0]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
