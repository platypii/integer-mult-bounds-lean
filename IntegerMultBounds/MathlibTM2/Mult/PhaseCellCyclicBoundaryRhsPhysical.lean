module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicBoundaryRhsPrepare
public import IntegerMultBounds.MathlibTM2.Host.Embed

/-! Gather the two physical residual streams directly into the factor bank's RHS port. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix

def cyclicBoundaryRhsReg (i : Fin 151) : Fin 224 :=
  if i = 143 then 206 else ⟨i.val,by omega⟩

theorem cyclicBoundaryRhsReg_injective : Function.Injective cyclicBoundaryRhsReg := by
  let back : Fin 224 → Fin 151 := fun k =>
    if k.val = 206 then 143 else ⟨k.val % 151, Nat.mod_lt _ (by decide)⟩
  have hback : Function.LeftInverse back cyclicBoundaryRhsReg := by
    intro i
    by_cases hi143 : i = 143
    · subst i; rfl
    apply Fin.ext
    have hi := i.isLt
    simp [back,cyclicBoundaryRhsReg,hi143,show i.val ≠ 206 by omega,Nat.mod_eq_of_lt hi]
  exact hback.injective

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

def cyclicBoundaryRhsPhysical : Pr P 224 Q A U :=
  embProg cyclicBoundaryRhsReg Empty.elim (cyclicBoundaryRhsPrepare (P := Empty))

theorem cyclicBoundaryRhsPhysical_exec {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (q V a b : ℕ)
    (hA : 4 ≤ A) (hwide : s+s ≤ 2^V) (ha : a ≤ s) (hb : b ≤ s)
    (C D : ZMod s → GaussianInt) (pageTail tail : List (Fin (A+4))) (v : HS 224 Q A U) (S : Stacks 224 A)
    (hrows : (S.R 116).length = B.card) (hwidth : (S.R 115).length = V)
    (hpage : S.R 109 = cstream A V ((bFoldOrder s B).map
      (fun k : ZMod s => (⟨(k.val : ℤ),0⟩ : GaussianInt)))++pageTail)
    (hq : (S.R 119).length = q) (hs : (S.R 121).length = s)
    (haSrc : (S.R 144).length = a) (hbSrc : (S.R 145).length = b)
    (hsource : S.R 132 = cstream A (2*q+8) (chirpLine s D)++(cstream A (2*q+8) (chirpLine s C)++tail))
    (h0 : S.R 0 = [])
    (hfresh : ∀ k ∈ [(94 : Fin 224),106,134,135,136,137,138,139,140,150], S.R k = [])
    (hblank : ∀ k : Fin 224, k.val < 31 → k ≠ 0 → S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ cyclicBoundaryRhsPrepareCost B q V a b ∧
      Exec body cyclicBoundaryRhsPhysical (mk v S) m
        (mk v' {S with R := (Function.update S.R 206
          (cstream A (2*q+8) ((List.range B.card).map (fun j =>
            let i := bFoldAt s B j
            if a ≤ i.val ∧ i.val < b then C i else D i))++S.R 206))}) := by
  obtain ⟨v₁,m,hv₁,hm,he₁⟩ := cyclicBoundaryRhsPrepare_exec (body := fun e : Empty => nomatch e)
    B q V a b hA hwide ha hb C D pageTail tail (embDn cyclicBoundaryRhsReg v) (embStk cyclicBoundaryRhsReg S)
    (by simpa [embStk,cyclicBoundaryRhsReg] using hrows)
    (by simpa [embStk,cyclicBoundaryRhsReg] using hwidth)
    (by simpa [embStk,cyclicBoundaryRhsReg] using hpage)
    (by simpa [embStk,cyclicBoundaryRhsReg] using hq)
    (by simpa [embStk,cyclicBoundaryRhsReg] using hs)
    (by simpa [embStk,cyclicBoundaryRhsReg] using haSrc)
    (by simpa [embStk,cyclicBoundaryRhsReg] using hbSrc)
    (by simpa [embStk,cyclicBoundaryRhsReg] using hsource)
    (by simpa [embStk,cyclicBoundaryRhsReg] using h0)
    (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simpa [embStk,cyclicBoundaryRhsReg] using hfresh _ (by simp))
    (by
      intro k hk hk0
      have h143 : k ≠ 143 := by intro h; subst k; norm_num at hk
      simpa [embStk,cyclicBoundaryRhsReg,h143] using
        hblank (⟨k.val,by omega⟩ : Fin 224) hk (by intro h; apply hk0; exact Fin.ext (congrArg (fun j : Fin 224 => j.val) h)))
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (e := cyclicBoundaryRhsReg) (ι := Empty.elim) (body' := body)
    cyclicBoundaryRhsReg_injective (fun e => nomatch e) he₁ v rfl S rfl
  refine ⟨v₂,m,hu₂.trans hv₁,hm,he₂.cast rfl ?_⟩
  apply congrArg (mk v₂)
  rw [embOvr_updR cyclicBoundaryRhsReg_injective (embStk cyclicBoundaryRhsReg S) S 143 _,embOvr_stk]
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
