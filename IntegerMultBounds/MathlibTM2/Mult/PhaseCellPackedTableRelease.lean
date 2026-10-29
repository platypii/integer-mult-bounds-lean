module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetirePackedBandTable
public import IntegerMultBounds.MathlibTM2.Host.Embed

/-! Retire the routed raw table using retained factor dimensions and native scratch. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv

def packedTableReleasePerm : Equiv (Fin 248) (Fin 248) :=
  (Equiv.swap 132 220).trans ((Equiv.swap 190 204).trans
    ((Equiv.swap 116 206).trans ((Equiv.swap 160 174).trans
    ((Equiv.swap 152 104).trans ((Equiv.swap 151 105).trans
    ((Equiv.swap 131 106).trans ((Equiv.swap 134 107).trans
    ((Equiv.swap 135 108).trans ((Equiv.swap 136 109).trans
    ((Equiv.swap 137 111).trans (Equiv.swap 138 112)))))))))))

def packedTableReleaseReg (i : Fin 224) : Fin 248 :=
  packedTableReleasePerm (Fin.castLE (by decide) i)

theorem packedTableReleaseReg_injective : Function.Injective packedTableReleaseReg := by
  intro i j hij
  change packedTableReleasePerm (Fin.castLE (by decide) i) =
    packedTableReleasePerm (Fin.castLE (by decide) j) at hij
  have hh : Fin.castLE (by decide : 224 ≤ 248) i = Fin.castLE (by decide) j :=
    packedTableReleasePerm.injective hij
  apply Fin.ext
  exact congrArg (fun k : Fin 248 => k.val) hh

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 248 Q A U}

def packedTableRelease : Pr P 248 Q A U :=
  embProg packedTableReleaseReg Empty.elim retirePackedBandTable

theorem packedTableRelease_exec {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (W w : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hlen : columns.length = B.card)
    (tail : List (Fin (A+4))) (v : HS 248 Q A U) (S : Stacks 248 A)
    (hW : (S.R 204).length = W) (hN : (S.R 206).length = B.card) (hw : (S.R 174).length = w)
    (hsource : S.R 220 = bandTableWords A w B W columns 0++tail)
    (hfresh : ∀ i ∈ ([104,105,106,107,108,109,111,112] : List (Fin 248)), S.R i = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ retirePackedBandTableCost B.card W w ∧
      Exec body packedTableRelease (mk v S) n (mk v' {S with R := Function.update S.R 220 tail}) := by
  let T := embStk packedTableReleaseReg S
  have hz : ∀ i ∈ ([152,151,131,134,135,136,137,138] : List (Fin 224)), T.R i = [] := by
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact hfresh _ (by decide)
  obtain ⟨v₁,n,hu₁,hn,he⟩ := retirePackedBandTable_exec (body := fun p : Empty => nomatch p)
    B W w columns hlen tail (embDn packedTableReleaseReg v) T hW hN hw hsource hz
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    packedTableReleaseReg_injective (fun p => nomatch p) he v rfl S rfl
  refine ⟨v₂,n,hu₂.trans hu₁,hn,he₂.cast rfl ?_⟩
  apply congrArg (mk v₂)
  rw [embOvr_updR packedTableReleaseReg_injective,embOvr_stk]
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
