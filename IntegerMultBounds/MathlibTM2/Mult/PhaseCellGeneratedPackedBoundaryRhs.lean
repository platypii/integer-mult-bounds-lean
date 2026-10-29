module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryMask

/-! Generate the local boundary mask and extract the packed residual in one
execution. The mask is retained for subsequent uses within the same halo. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

def generatedPackedBoundaryRhs : Pr P 117 Q A U :=
  .seq (couplingSourceIntervalMaskHost true) (gatherRecords 110 109 94 0 1 2 3 93 4 pairRe)

theorem generatedPackedBoundaryRhs_exec {V s t band a b origin N : ℕ} [NeZero s]
    (st : TblSt 17 A) (hs : st.val 0 = s) (ht : st.val 1 = t) (hband : st.val 2 = band)
    (ha : st.val 4 = a) (hb : st.val 5 = b) (hindex : st.val 3 = origin)
    (hcount : st.val 16 = origin+N) (hfit : origin+N ≤ s) (hacc : st.acc = [])
    (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hA : 4 ≤ A)
    (hB : ∀ i ∈ haloBoundary s t band a b, origin ≤ i.val ∧ i.val < origin+N)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V) (hbound : ∀ r, st.val r < 2^V)
    (C : ZMod s → GaussianInt) (w : ℕ) (tail : List (Fin (A+4)))
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hS : tblHolds intervalGuardReg S (tblRho V (List.replicate V tick) (List.replicate V tick) st))
    (hsrc : S.R 110 = cstream A w (packedInterval origin N C)++tail)
    (hmask : S.R 109 = []) (hw : (S.R 94).length = w) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ (29*N+2)*tblC V 1+66*V+2*N+70 + (N*(16*w+10)+16) ∧
      Exec body generatedPackedBoundaryRhs (mk v S) m
        (mk v' {S with R := (fun r => if r.val < 32 then [] else if r = 109 then
          couplingSourceIntervalMaskSymbols true A s t band a b origin N else if r = 93 then
          cstream A w ((bOrder s (haloBoundary s t band a b)).map C)++S.R r else S.R r)}) := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := couplingSourceIntervalMaskHost_exec (body := body) true st
    hs ht hband ha hb hindex hcount hfit hacc (NeZero.pos s) hst haS hbS hwide hbound v S hS
  let S₁ : Stacks 117 A := {S with R := fun r => if r.val < 32 then [] else if r = 109 then
    couplingSourceIntervalMaskSymbols true A s t band a b origin N++S.R r else S.R r}
  have hsrc₁ : S₁.R 110 = cstream A w (packedInterval origin N C)++tail := by simpa [S₁] using hsrc
  have hmask₁ : S₁.R 109 = couplingSourceIntervalMaskSymbols true A s t band a b origin N := by
    simp [S₁,hmask]
  have hw₁ : (S₁.R 94).length = w := by simpa [S₁] using hw
  have hfresh : ∀ k ∈ ([0,1,2,3] : List (Fin 117)), S₁.R k = [] := by
    intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl <;> simp [S₁]
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := packedBoundaryRhsHaloGather_exec (body := body)
    (src := 110) (mask := 109) (width := 94) (symbols := 0) (ts := 1) (tm := 2)
    (acc := 3) (out := 93) (cs := 4) (by decide) hst hA band a b hbS hfit hB C w tail
    v₁ S₁ hsrc₁ hmask₁ hw₁ hfresh
  refine ⟨v₂,m₁+m₂,hu₂.trans hu₁,by omega,?_⟩
  have he := Exec.seq he₁ he₂
  convert he using 1
  · rfl
  · congr 1
    refine Stacks.ext rfl rfl rfl ?_
    funext r
    by_cases h93 : r = 93
    · subst r; simp [S₁]
    · by_cases h109 : r = 109
      · subst r; simp [S₁,hmask]
      · simp [S₁,h93,h109]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
