module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCanonicalOutput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFinalRoundFits
public import IntegerMultBounds.MathlibTM2.Mult.SignedRoundExec

/-! One signed word pass normalizes an arbitrary batch stream. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.LayerMachine IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def finalRoundWord (w q p j : ℕ) (z : GaussianInt) : GaussianInt :=
  tdivN (q-p+j) (symZ w z)

theorem finalRound_list_exec (hA : 4 ≤ A) {src dst tmp cW cS cE cD sp sg cy : Fin T}
    (hreg : [src,dst,tmp,cW,cS,cE,cD,sp,sg,cy].Nodup)
    (w q p j k : ℕ) (hp : p ≤ q) (hw : 1 ≤ w)
    (hsize : q-p+j+k ≤ w) (xs : List GaussianInt)
    (v : HS T Q A U) (S : Stacks T A) (hsrc : S.R src = cstream A w xs) (hdst : S.R dst = [])
    (hg : topShiftG tmp cW cS cE cD sp sg cy w (q-p+j) k S.R) :
    ∃ v', v'.user = v.user ∧
      Exec body (topPass src dst (topShiftWord src dst tmp cW cS cE cD sp sg cy))
        (mk v S) (1+(xs.length*(topShiftWordCost w (q-p+j) k+1)+1)+(2*(xs.length*k)+2))
        (mk v' {S with R := (Function.update S.R src (cstream A k (xs.map (finalRoundWord w q p j))))}) ∧
      ∀ z ∈ xs, value p (finalRoundWord w q p j z) =
          IntegerMultBounds.NLogN.rhoC p (((2 : ℂ)^j)⁻¹*value q (symZ w z)) := by
  have hfit : ∀ z ∈ xs.map (symZ w), TopFitsZ w z := by
    intro z hz
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hz
    exact topFitsZ_symZ hw x
  obtain ⟨v',hu,he⟩ := signedRound_exec (body := body) hA hreg w (q-p+j) k hw hsize
    (xs.map (symZ w)) hfit v S (hsrc.trans (cstream_symZ A w xs).symm) hdst hg
  refine ⟨v',hu,?_,?_⟩
  · unfold finalRoundWord
    simpa only [List.length_map,List.map_map,Function.comp_def] using he
  · intro z hz
    exact value_finalRound q p j hp _

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
