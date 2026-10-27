module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryRhsPrepare
public import IntegerMultBounds.MathlibTM2.Host.Embed

/-! Gather directly into the factor bank's RHS port, borrowing its word-width header. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix

def boundaryRhsReg (i : Fin 148) : Fin 224 :=
  if i = 94 then 160 else if i = 143 then 206 else ⟨i.val,by omega⟩

theorem boundaryRhsReg_injective : Function.Injective boundaryRhsReg := by
  let back : Fin 224 → Fin 148 := fun k =>
    if k.val = 160 then 94 else if k.val = 206 then 143 else ⟨k.val % 148, Nat.mod_lt _ (by decide)⟩
  have hback : Function.LeftInverse back boundaryRhsReg := by
    intro i
    by_cases hi94 : i = 94
    · subst i; rfl
    by_cases hi143 : i = 143
    · subst i; rfl
    apply Fin.ext
    have hi := i.isLt
    simp [back,boundaryRhsReg,hi94,hi143,show i.val ≠ 160 by omega,
      show i.val ≠ 206 by omega,Nat.mod_eq_of_lt hi]
  exact hback.injective

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

def boundaryRhsPhysical : Pr P 224 Q A U :=
  embProg boundaryRhsReg Empty.elim (boundaryRhsPrepare (P := Empty))

theorem boundaryRhsPhysical_exec {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (V w : ℕ)
    (hA : 4 ≤ A) (hs : s ≤ 2^V) (C D : ZMod s → GaussianInt) (hCD : ∀ i ∈ B, C i = D i)
    (coordinateTail rhsTail : List (Fin (A+4))) (v : HS 224 Q A U) (S : Stacks 224 A)
    (hN : (S.R 116).length = B.card) (hV : (S.R 115).length = V) (hw : (S.R 160).length = w)
    (hcoordinates : S.R 109 = cstream A V ((bFoldOrder s B).map
      (fun k : ZMod s => (⟨(k.val : ℤ),0⟩ : GaussianInt)))++coordinateTail)
    (hrhs : S.R 110 = cstream A w (chirpLine s C)++rhsTail)
    (h0 : S.R 0 = []) (h106 : S.R 106 = []) (h139 : S.R 139 = [])
    (hblank : ∀ r : Fin 224, 1 ≤ r.val → r.val < 7 → S.R r = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ boundaryRhsPrepareCost V w B.card s ∧
      Exec body boundaryRhsPhysical (mk v S) n
        (mk v' {S with R := (Function.update S.R 206
          (cstream A w ((List.range B.card).map (fun j => D (bFoldAt s B j)))++S.R 206))}) := by
  obtain ⟨v₁,n,hu₁,hn,he₁⟩ := boundaryRhsPrepare_exec (body := fun e : Empty => nomatch e)
    B V w hA hs C D hCD coordinateTail rhsTail (embDn boundaryRhsReg v) (embStk boundaryRhsReg S)
    (by simpa [embStk,boundaryRhsReg] using hN) (by simpa [embStk,boundaryRhsReg] using hV)
    (by simpa [embStk,boundaryRhsReg] using hw)
    (by simpa [embStk,boundaryRhsReg] using hcoordinates)
    (by simpa [embStk,boundaryRhsReg] using hrhs)
    (by simpa [embStk,boundaryRhsReg] using h0)
    (by simpa [embStk,boundaryRhsReg] using h106)
    (by simpa [embStk,boundaryRhsReg] using h139) (by
      intro r hr1 hr7
      have hr94 : r ≠ 94 := by intro h; subst r; simp at hr7
      have hr143 : r ≠ 143 := by intro h; subst r; simp at hr7
      simpa [embStk,boundaryRhsReg,hr94,hr143] using
        hblank (⟨r.val,by omega⟩ : Fin 224) hr1 hr7)
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (e := boundaryRhsReg) (ι := Empty.elim) (body' := body)
    boundaryRhsReg_injective (fun e => nomatch e) he₁ v rfl S rfl
  refine ⟨v₂,n,hu₂.trans hu₁,hn,he₂.cast rfl ?_⟩
  apply congrArg (mk v₂)
  rw [embOvr_updR boundaryRhsReg_injective (embStk boundaryRhsReg S) S 143 _,embOvr_stk]
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
