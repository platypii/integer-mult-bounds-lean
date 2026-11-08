module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCollectCyclicColumnEntries
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReversePackedLines

/-! Gather a joint boundary RHS from two physical interval residuals in solver order. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 151 Q A U}

def cyclicBoundaryRhsPrepare : Pr P 151 Q A U :=
  .seq (ucopy 116 138 135) (.seq collectCyclicColumnEntries
    (.seq residentColumnWidth (.seq (retainedReversePackedLines 116 138 94 150 143 134 135) (uclear 94))))

noncomputable def cyclicBoundaryRhsPrepareCost {s : ℕ} [NeZero s]
    (B : Finset (ZMod s)) (q V a b : ℕ) : ℕ :=
  (4*B.card+4)+(collectCyclicColumnEntriesCost B q V a b 0 B.card+
    ((8*q+9)+(B.card*(6*(2*q+8)+13)+6+(2*(2*q+8)+2))))

theorem cyclicBoundaryRhsPrepare_exec {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (q V a b : ℕ)
    (hA : 4 ≤ A) (hwide : s+s ≤ 2^V) (ha : a ≤ s) (hb : b ≤ s)
    (C D : ZMod s → GaussianInt) (pageTail tail : List (Fin (A+4))) (v : HS 151 Q A U) (S : Stacks 151 A)
    (hrows : (S.R 116).length = B.card) (hwidth : (S.R 115).length = V)
    (hpage : S.R 109 = cstream A V ((bFoldOrder s B).map
      (fun k : ZMod s => (⟨(k.val : ℤ),0⟩ : GaussianInt)))++pageTail)
    (hq : (S.R 119).length = q) (hs : (S.R 121).length = s)
    (haSrc : (S.R 144).length = a) (hbSrc : (S.R 145).length = b)
    (hsource : S.R 132 = cstream A (2*q+8) (chirpLine s D)++(cstream A (2*q+8) (chirpLine s C)++tail))
    (h0 : S.R 0 = [])
    (hfresh : ∀ k ∈ [(94 : Fin 151),106,134,135,136,137,138,139,140,150], S.R k = [])
    (hblank : ∀ k : Fin 151, k.val < 31 → k ≠ 0 → S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ cyclicBoundaryRhsPrepareCost B q V a b ∧
      Exec body cyclicBoundaryRhsPrepare (mk v S) m
        (mk v' {S with R := (Function.update S.R 143
          (cstream A (2*q+8) ((List.range B.card).map (fun j =>
            let i := bFoldAt s B j
            if a ≤ i.val ∧ i.val < b then C i else D i))++S.R 143))}) := by
  let w := 2*q+8
  let F := fun j => let i := bFoldAt s B j; if a ≤ i.val ∧ i.val < b then C i else D i
  let xs := (List.range B.card).map F
  have h138 := hfresh 138 (by simp)
  have h150 := hfresh 150 (by simp)
  have h94 := hfresh 94 (by simp)
  obtain ⟨v₁,hv₁,he₁⟩ := ucopy_exec body (a := 116) (b := 138) (t := 135)
    (by decide) (by decide) (by decide) v S (hfresh 135 (by simp))
  let S₁ : Stacks 151 A := {S with R := Function.update S.R 138 (List.replicate B.card tick)}
  have he₁' : Exec body (ucopy 116 138 135) (mk v S) (4*B.card+4) (mk v₁ S₁) := by
    simpa [S₁,hrows,h138] using he₁
  obtain ⟨v₂,m₂,hv₂,hm₂,he₂⟩ := collectCyclicColumnEntries_exec (body := body)
    B q V a b 0 B.card hA hwide ha hb (by omega) C D pageTail tail v₁ S₁
    (by simpa [S₁] using congrArg List.length (hfresh 137 (by simp)))
    (by simp [S₁]) (by simpa [S₁] using hwidth) (by simpa [S₁] using hpage)
    (by simpa [S₁] using hq) (by simpa [S₁] using hs)
    (by simpa [S₁] using haSrc) (by simpa [S₁] using hbSrc) (by simpa [S₁] using hsource)
    (by simpa [S₁] using h0) (by simpa [S₁] using h94) (by simpa [S₁] using hfresh 106 (by simp))
    (by simpa [S₁] using hfresh 135 (by simp)) (by simpa [S₁] using hfresh 136 (by simp))
    (by simpa [S₁] using hfresh 139 (by simp)) (by simpa [S₁] using hfresh 140 (by simp))
    (by intro k hk hk0; simpa [S₁,show k ≠ 138 by omega] using hblank k hk hk0)
  let S₂ : Stacks 151 A := {S with R := Function.update S.R 150 (cstream A w xs.reverse)}
  have he₂' : Exec body collectCyclicColumnEntries (mk v₁ S₁) m₂ (mk v₂ S₂) := by
    convert he₂ using 1
    apply congrArg (mk v₂)
    ext1
    · rfl
    · rfl
    · rfl
    · funext k
      by_cases h137 : k = 137 <;> by_cases h138' : k = 138 <;>
        simp [S₂,S₁,w,xs,F,h150,h137,h138',hfresh 137 (by simp),h138,Function.update_apply]
  obtain ⟨v₃,hv₃,he₃⟩ := residentColumnWidth_exec (body := body) q v₂ S₂
    (by simpa [S₂] using hq) (by simpa [S₂] using h94) (by simpa [S₂] using hfresh 135 (by simp))
  let S₃ : Stacks 151 A := {S₂ with R := Function.update S₂.R 94 (List.replicate w tick)}
  let lines := xs.reverse.map (csyms A w)
  have hflat (ys : List GaussianInt) : (ys.map (csyms A w)).flatten = cstream A w ys := by
    induction ys with
    | nil => rfl
    | cons y ys ih => simpa [cstream] using congrArg (csyms A w y ++ ·) ih
  have hlines : lines.flatten = cstream A w xs.reverse := hflat xs.reverse
  have hreverse : lines.reverse.flatten = cstream A w xs := by
    have hr : lines.reverse = xs.map (csyms A w) := by simp [lines]
    rw [hr]
    exact hflat xs
  obtain ⟨v₄,S₄,m₄,hv₄,hm₄,he₄,hsrc,hdst,hinp,hout,hL,hframe⟩ :=
    retainedReversePackedLines_exec (body := body) 116 138 94 150 143 134 135 (by decide)
      lines w (by intro x hx; obtain ⟨z,_,rfl⟩ := List.mem_map.mp hx; simp)
      [] v₃ S₃ (by simp [S₃,S₂,lines,xs,hrows]) (by simp [S₃])
      (by simp [S₃,S₂,hlines]) (by simpa [S₃,S₂] using h138)
      (by simpa [S₃,S₂] using hfresh 134 (by simp)) (by simpa [S₃,S₂] using hfresh 135 (by simp))
  obtain ⟨v₅,hv₅,he₅⟩ := uclear_exec body 94 v₄ S₄
  have h94len : (S₄.R 94).length = w := by rw [hframe 94 (by decide) (by decide)]; simp [S₃]
  have hfinal : {S₄ with R := Function.update S₄.R 94 []} =
      {S with R := Function.update S.R 143 (cstream A w xs++S.R 143)} := by
    ext1
    · exact hinp
    · exact hout
    · exact hL
    · funext k
      by_cases h94' : k = 94
      · subst k; simp [h94]
      by_cases h143 : k = 143
      · subst k; simpa [S₃,S₂,hreverse] using hdst
      by_cases h150' : k = 150
      · subst k; simpa [h150] using hsrc
      simpa [S₃,S₂,h94',h143,h150'] using hframe k h150' h143
  refine ⟨v₅,(4*B.card+4)+(m₂+((8*q+9)+(m₄+(2*w+2)))),
    hv₅.trans (hv₄.trans (hv₃.trans (hv₂.trans hv₁))),?_,?_⟩
  · have hm₄' : m₄ ≤ B.card*(6*w+13)+6 := by simpa [lines,xs] using hm₄
    exact Nat.add_le_add_left (Nat.add_le_add hm₂ (Nat.add_le_add_left (Nat.add_le_add_right hm₄' _) _)) _
  · have he := Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃ (Exec.seq he₄ he₅)))
    rw [h94len] at he
    rw [hfinal] at he
    exact he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
