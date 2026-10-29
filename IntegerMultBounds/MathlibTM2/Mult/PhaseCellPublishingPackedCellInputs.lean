module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellControlledPublishingPackedCellInputs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateWordWidth

/-! Generate unary and binary widths around the shared gather/publication
schedule. Only local RHS rows and protected publication controls are retained. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Fast.TableVM
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

def preparedPublishingPackedCellInputs : Pr P 168 Q A U :=
  .seq (toBinary 94 163 153 0 1 2) (.seq controlledPublishingPackedCellInputs (uclear 153))

theorem preparedPublishingPackedCellInputs_exec {V N L w s origin : ℕ}
    (C : ZMod s → GaussianInt) (hhalo : origin+N ≤ s) (hNV : N < 2^V)
    (offsets : List ℕ) (hne : offsets ≠ []) (hdis : offsets.Pairwise (fun i j => i+L ≤ j))
    (hfit : ∀ j ∈ offsets, j+L ≤ N)
    (tail : List (Fin (A+4))) (v : HS 168 Q A U) (S : Stacks 168 A)
    (h165 : S.R 165 = binSyms V N) (h166 : S.R 166 = [])
    (hwidth : (S.R 94).length = w) (hrows : (S.R 102).length = L)
    (hsource : S.R 110 = cstream A w (packedInterval origin N C)++tail)
    (hwV : w < 2^V) (hcoords : origin+N < 2^V) (hunits : (origin+N)*w < 2^V)
    (originTail : List (Fin (A+4)))
    (hcount : S.R 116 = List.replicate offsets.length tick)
    (hpackets : S.R 109 = (offsets.map (origin+·)).flatMap (binSyms V)++originTail)
    (hV : (S.R 163).length = V) (h153 : S.R 153 = [])
    (h155 : S.R 155 = binSyms V origin) (h154 : S.R 154 = binSyms V 0)
    (hsmall : ∀ k : Fin 168, k.val < 19 → S.R k = [])
    (hpublication : ∀ k ∈ [(88 : Fin 168),89,90,92,95,104,106,131,134,135], S.R k = [])
    (hfresh : ∀ k ∈ [(88 : Fin 168),89,90,91,92,104,105,108], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ w*(4*V+10)+6*V+10+(offsets.length*(3*tblC V V+29*V+30)+8*N*w+78*V+91+
        ((12*N*w+21*offsets.length+6*L*w+9*L+27)+
          (offsets.length*(14*L*w+27)+32*N*w+17*N+11*V+6*L*w+9*L+60))) ∧
      Exec body preparedPublishingPackedCellInputs (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R 140
      (gatherControls A (packedCellGaps L w offsets)++S.R 140)) 110
          (offsets.flatMap (fun j => cstream A w (packedInterval (origin+j) L C))++S.R 110))}) := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := toBinary_exec (body := body)
    (u := 94) (wR := 163) (c := 153) (t := 0) (tmp := 1) (by decide) 2 v S
    h153 (hsmall 0 (by decide)) (hsmall 1 (by decide))
  let B : Stacks 168 A := {S with R := Function.update S.R 153 (binSyms V w)}
  have he₁' : Exec body (toBinary 94 163 153 0 1 2) (mk v S) m₁ (mk v₁ B) := by
    simpa only [hwidth,hV] using he₁
  have hsmallB : ∀ k : Fin 168, k.val < 19 → B.R k = [] := by
    intro k hk
    have hn : k ≠ 153 := by intro he; subst k; norm_num at hk
    simpa [B,hn] using hsmall k hk
  have hfreshB : ∀ k ∈ [(88 : Fin 168),89,90,91,92,104,105,108], B.R k = [] := by
    intro k hk
    have hn : k ≠ 153 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simpa [B,hn] using hfresh k hk
  have hpublicationB : ∀ k ∈ [(88 : Fin 168),89,90,92,95,104,106,131,134,135], B.R k = [] := by
    intro k hk
    have hn : k ≠ 153 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simpa [B,hn] using hpublication k hk
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := controlledPublishingPackedCellInputs_exec (body := body)
    C hhalo hNV offsets hne hdis hfit tail v₁ B
    (by simpa [B] using h165) (by simpa [B] using h166)
    (by simpa [B] using hwidth) (by simpa [B] using hrows)
    (by simpa [B] using hsource) hwV hcoords hunits originTail
    (by simpa [B] using hcount) (by simpa [B] using hpackets)
    (by simpa [B] using hV) (by simp [B]) (by simpa [B] using h155)
    (by simpa [B] using h154) hsmallB hpublicationB hfreshB
  let F : Stacks 168 A := {B with R := (Function.update (Function.update B.R 140
      (gatherControls A (packedCellGaps L w offsets)++B.R 140)) 110
    (offsets.flatMap (fun j => cstream A w (packedInterval (origin+j) L C))++B.R 110))}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) 153 v₂ F
  have hc : (F.R 153).length = V := by simp [F,B]
  rw [hwidth,hV] at hm₁
  refine ⟨v₃,m₁+(m₂+(2*V+2)),hu₃.trans (hu₂.trans hu₁),by omega,
    (Exec.seq he₁' (Exec.seq he₂ he₃)).cast (by rw [hc]) ?_⟩
  apply congrArg (mk v₃)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases h153' : k = 153 <;> by_cases h110 : k = 110 <;> by_cases h140 : k = 140 <;> simp [F,B,h153',h110,h140,h153]


def rawPublishingPackedCellInputs : Pr P 168 Q A U :=
  .seq (generateWordWidth 112 94 104) (.seq preparedPublishingPackedCellInputs (uclear 94))

theorem rawPublishingPackedCellInputs_exec {V N L w s origin q : ℕ}
    (C : ZMod s → GaussianInt) (hhalo : origin+N ≤ s) (hNV : N < 2^V)
    (offsets : List ℕ) (hne : offsets ≠ []) (hdis : offsets.Pairwise (fun i j => i+L ≤ j))
    (hfit : ∀ j ∈ offsets, j+L ≤ N)
    (tail : List (Fin (A+4))) (v : HS 168 Q A U) (S : Stacks 168 A)
    (h165 : S.R 165 = binSyms V N) (h166 : S.R 166 = [])
    (hq : (S.R 112).length = q) (h94 : S.R 94 = []) (hw : w = 2*q+8) (hrows : (S.R 102).length = L)
    (hsource : S.R 110 = cstream A w (packedInterval origin N C)++tail)
    (hwV : w < 2^V) (hcoords : origin+N < 2^V) (hunits : (origin+N)*w < 2^V)
    (originTail : List (Fin (A+4)))
    (hcount : S.R 116 = List.replicate offsets.length tick)
    (hpackets : S.R 109 = (offsets.map (origin+·)).flatMap (binSyms V)++originTail)
    (hV : (S.R 163).length = V) (h153 : S.R 153 = [])
    (h155 : S.R 155 = binSyms V origin) (h154 : S.R 154 = binSyms V 0)
    (hsmall : ∀ k : Fin 168, k.val < 19 → S.R k = [])
    (hpublication : ∀ k ∈ [(88 : Fin 168),89,90,92,95,104,106,131,134,135], S.R k = [])
    (hfresh : ∀ k ∈ [(88 : Fin 168),89,90,91,92,104,105,108], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ 8*q+2*w+11+(w*(4*V+10)+6*V+10+(offsets.length*(3*tblC V V+29*V+30)+8*N*w+78*V+91+
        ((12*N*w+21*offsets.length+6*L*w+9*L+27)+
          (offsets.length*(14*L*w+27)+32*N*w+17*N+11*V+6*L*w+9*L+60)))) ∧
      Exec body rawPublishingPackedCellInputs (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R 140
      (gatherControls A (packedCellGaps L w offsets)++S.R 140)) 110
          (offsets.flatMap (fun j => cstream A w (packedInterval (origin+j) L C))++S.R 110))}) := by
  obtain ⟨v₁,hu₁,he₁⟩ := generateWordWidth_exec (body := body)
    (precision := 112) (width := 94) (tmp := 104) (by decide) q v S hq h94 (hfresh 104 (by simp))
  let B : Stacks 168 A := {S with R := Function.update S.R 94 (List.replicate w tick)}
  have he₁' : Exec body (generateWordWidth 112 94 104) (mk v S) (8*q+9) (mk v₁ B) := by
    simpa only [← hw] using he₁
  have hsmallB : ∀ k : Fin 168, k.val < 19 → B.R k = [] := by
    intro k hk
    have hn : k ≠ 94 := by intro he; subst k; norm_num at hk
    simpa [B,hn] using hsmall k hk
  have hfreshB : ∀ k ∈ [(88 : Fin 168),89,90,91,92,104,105,108], B.R k = [] := by
    intro k hk
    have hn : k ≠ 94 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simpa [B,hn] using hfresh k hk
  have hpublicationB : ∀ k ∈ [(88 : Fin 168),89,90,92,95,104,106,131,134,135], B.R k = [] := by
    intro k hk
    have hn : k ≠ 94 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simpa [B,hn] using hpublication k hk
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := preparedPublishingPackedCellInputs_exec (body := body)
    C hhalo hNV offsets hne hdis hfit tail v₁ B
    (by simpa [B] using h165) (by simpa [B] using h166)
    (by simp [B]) (by simpa [B] using hrows)
    (by simpa [B] using hsource) hwV hcoords hunits originTail
    (by simpa [B] using hcount) (by simpa [B] using hpackets)
    (by simpa [B] using hV) (by simpa [B] using h153)
    (by simpa [B] using h155) (by simpa [B] using h154) hsmallB hpublicationB hfreshB
  let F : Stacks 168 A := {B with R := (Function.update (Function.update B.R 140
      (gatherControls A (packedCellGaps L w offsets)++B.R 140)) 110
    (offsets.flatMap (fun j => cstream A w (packedInterval (origin+j) L C))++B.R 110))}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) 94 v₂ F
  have hc : (F.R 94).length = w := by simp [F,B]
  refine ⟨v₃,(8*q+9)+(m₂+(2*w+2)),hu₃.trans (hu₂.trans hu₁),by omega,
    (Exec.seq he₁' (Exec.seq he₂ he₃)).cast (by rw [hc]) ?_⟩
  apply congrArg (mk v₃)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases h94' : k = 94 <;> by_cases h110 : k = 110 <;> by_cases h140 : k = 140 <;> simp [F,B,h94',h110,h140,h94]


end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
