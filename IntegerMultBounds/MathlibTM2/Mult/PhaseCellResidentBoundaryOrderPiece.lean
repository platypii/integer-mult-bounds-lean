module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryOrderHeaders
public import IntegerMultBounds.MathlibTM2.Host.Embed

/-! Alias the ordinary boundary enumerator directly to retained physical geometry. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def boundaryPieceBase (i : Fin 117) : Fin 154 := ⟨i.val,by omega⟩
def boundaryPieceReg (right : Bool) (i : Fin 117) : Fin 154 :=
  Equiv.swap 103 (if right then 146 else 145)
    (Equiv.swap 101 (if right then 138 else 144)
      (Equiv.swap 100 124 (Equiv.swap 98 122 (Equiv.swap 97 121 (boundaryPieceBase i)))))

theorem boundaryPieceReg_injective (right : Bool) : Function.Injective (boundaryPieceReg right) := by
  apply (Equiv.injective (Equiv.swap _ _)).comp
  apply (Equiv.injective (Equiv.swap _ _)).comp
  apply (Equiv.injective (Equiv.swap _ _)).comp
  apply (Equiv.injective (Equiv.swap _ _)).comp
  apply (Equiv.injective (Equiv.swap _ _)).comp
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 154 => k.val) h)

theorem boundaryPieceReg_low (right : Bool) (i : Fin 117) (hi : i.val < 31) :
    boundaryPieceReg right i = boundaryPieceBase i := by
  have hne (k : Fin 154) (hk : 31 ≤ k.val) : boundaryPieceBase i ≠ k := by
    intro h
    have hv := congrArg (fun k : Fin 154 => k.val) h
    change i.val = k.val at hv
    omega
  cases right <;> simp [boundaryPieceReg,Equiv.swap_apply_def,
    hne 97 (by decide),hne 121 (by decide),hne 98 (by decide),hne 122 (by decide),
    hne 100 (by decide),hne 124 (by decide),hne 101 (by decide),hne 138 (by decide),
    hne 144 (by decide),hne 103 (by decide),hne 145 (by decide),hne 146 (by decide)]

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 154 Q A U}

def residentBoundaryOrderPiece (right : Bool) : Pr P 154 Q A U :=
  embProg (boundaryPieceReg right) Empty.elim (boundaryOrderFromHeaders (P₀ := Empty))

theorem residentBoundaryOrderPiece_exec (right : Bool) {V s t band a b : ℕ} [NeZero s]
    (hst : s < t) (ha : a ≤ s) (hb : b ≤ s) (hband : band ≤ s)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V)
    (v : HS 154 Q A U) (S : Stacks 154 A)
    (hsSrc : (S.R 121).length = s) (htSrc : (S.R 122).length = t)
    (hbandSrc : (S.R 124).length = band)
    (haSrc : (S.R (if right then 138 else 144)).length = a)
    (hbSrc : (S.R (if right then 146 else 145)).length = b)
    (hwidth : (S.R 115).length = V) (h106 : S.R 106 = []) (h108 : S.R 108 = [])
    (hlow : ∀ k : Fin 154, k.val < 31 → S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ boundaryOrderFromHeadersCost V s t band a b ∧
      Exec body (residentBoundaryOrderPiece right) (mk v S) m
        (mk v' {S with R := Function.update S.R 109 (boundaryOrderSymbols A V s t band a b++S.R 109)}) := by
  obtain ⟨vi,m,hu,hm,he⟩ := boundaryOrderFromHeaders_exec (body := fun e : Empty => nomatch e)
    (V := V) hst ha hb hband hwide (embDn (boundaryPieceReg right) v) (embStk (boundaryPieceReg right) S)
    (by cases right <;> simpa [embStk,boundaryPieceReg,boundaryPieceBase,Equiv.swap_apply_def] using hsSrc)
    (by cases right <;> simpa [embStk,boundaryPieceReg,boundaryPieceBase,Equiv.swap_apply_def] using htSrc)
    (by cases right <;> simpa [embStk,boundaryPieceReg,boundaryPieceBase,Equiv.swap_apply_def] using hbandSrc)
    (by cases right <;> simpa [embStk,boundaryPieceReg,boundaryPieceBase,Equiv.swap_apply_def] using haSrc)
    (by cases right <;> simpa [embStk,boundaryPieceReg,boundaryPieceBase,Equiv.swap_apply_def] using hbSrc)
    (by cases right <;> simpa [embStk,boundaryPieceReg,boundaryPieceBase,Equiv.swap_apply_def] using h108)
    (by cases right <;> simpa [embStk,boundaryPieceReg,boundaryPieceBase,Equiv.swap_apply_def] using hwidth)
    (by cases right <;> simpa [embStk,boundaryPieceReg,boundaryPieceBase,Equiv.swap_apply_def] using h106)
    (by intro k hk; change S.R (boundaryPieceReg right k) = []
        rw [boundaryPieceReg_low right k hk]; exact hlow _ hk)
  obtain ⟨vf,_,hv,hf⟩ := exec_emb_ovr (e := boundaryPieceReg right) (ι := Empty.elim) (body' := body)
    (boundaryPieceReg_injective right) (fun e => nomatch e) he v rfl S rfl
  refine ⟨vf,m,hv.trans hu,hm,hf.cast rfl ?_⟩
  apply congrArg (mk vf)
  rw [embOvr_updR (boundaryPieceReg_injective right) (embStk (boundaryPieceReg right) S) S 109 _,embOvr_stk]
  cases right <;> rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
