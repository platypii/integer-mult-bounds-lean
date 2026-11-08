module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellUnaryScalarResult
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicResidualIndex

/-! Compute the residual-bank address from ordinary rulers, exporting only the unary address. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def cyclicResidualIndexInputs (sPort aPort bPort iPort : Fin T) : List (Fin 5 × Fin T) :=
  [(0,sPort),(1,aPort),(2,bPort),(3,iPort)]

def cyclicResidualIndexFromUnary (rg : TblR 5 → Fin T)
    (header word saved tmp carry sPort aPort bPort iPort dst : Fin T) : Pr P T Q A U :=
  unaryScalarResult rg header word saved tmp carry (cyclicResidualIndexInputs sPort aPort bPort iPort)
    cyclicResidualIndexCode 4 dst

theorem cyclicResidualIndexFromUnary_exec (rg : TblR 5 → Fin T) (hrg : Function.Injective rg)
    (header word saved tmp carry sPort aPort bPort iPort dst : Fin T)
    (hheader : ∀ r, rg r ≠ header) (hoff : ∀ r, rg r ≠ dst)
    (hregs : ∀ src ∈ [sPort,aPort,bPort,iPort], [src,rg .wr,word,saved,tmp,header].Nodup)
    (W s a b i : ℕ) (ha : a ≤ s) (hb : b ≤ s) (hi : i < s) (hwide : s+s ≤ 2^W)
    (wl : List (Fin (A+4))) (hwl : wl.length = W) (v : HS T Q A U) (S : Stacks T A)
    (hsSrc : (S.R sPort).length = s) (haSrc : (S.R aPort).length = a)
    (hbSrc : (S.R bPort).length = b) (hiSrc : (S.R iPort).length = i)
    (hwidth : S.R (rg .wr) = wl) (hblank : ∀ r, r ≠ .wr → S.R (rg r) = [])
    (hwork : ∀ k ∈ [word,saved,tmp], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ unaryScalarResultCost S.R (cyclicResidualIndexInputs sPort aPort bPort iPort) W 3 (cyclicResidualIndex s a b i) ∧
      ∀ depth, ExecWithin body (fun j z => mnSize z+j ≤ mnSize (mk v S)+depth+
        3*unaryScalarResultCost S.R (cyclicResidualIndexInputs sPort aPort bPort iPort) W 3 (cyclicResidualIndex s a b i)) depth
        (cyclicResidualIndexFromUnary rg header word saved tmp carry sPort aPort bPort iPort dst) (mk v S) m
        (mk v' {S with R := Function.update S.R dst (List.replicate (cyclicResidualIndex s a b i) tick++S.R dst)}) := by
  let ports := cyclicResidualIndexInputs sPort aPort bPort iPort
  let st := unaryScalarInputState ports S.R
  have hst : st = loadedBinaryState [(0,s),(1,a),(2,b),(3,i)] (⟨fun _ => 0,[]⟩ : TblSt 5 A) := by
    simp only [st,ports,unaryScalarInputState,cyclicResidualIndexInputs,List.map_cons,List.map_nil,
      hsSrc,haSrc,hbSrc,hiSrc]
  have hvals : st.val 0 = s ∧ st.val 1 = a ∧ st.val 2 = b ∧ st.val 3 = i ∧ st.acc = [] := by
    simp [hst,loadedBinaryState]
  have hfit : ∀ k, st.val k < 2^W := by
    intro k
    simp only [hst,loadedBinaryState,Function.update_apply]
    split_ifs <;> omega
  have hcode : TblDo A W 0 cyclicResidualIndexCode st
      (fun F => F.val 4 = cyclicResidualIndex s a b i ∧ F.acc = [] ∧ ∀ k, F.val k < 2^W) 3 := by
    apply (cyclicResidualIndexCode_do st hvals.1 hvals.2.1 hvals.2.2.1 hvals.2.2.2.1 hi hwide).mono
    · intro F hF
      subst F
      refine ⟨by simp,hvals.2.2.2.2,?_⟩
      intro k
      by_cases hk : k = 4
      · subst k
        simp only [Function.update_self]
        exact (cyclicResidualIndex_lt hi).trans_le hwide
      · simpa only [Function.update_of_ne hk] using hfit k
    · exact le_rfl
  exact unaryScalarResult_exec (body := body) rg hrg header word saved tmp carry hheader ports
    (by simpa only [ports,cyclicResidualIndexInputs,List.map_cons,List.map_nil] using hregs)
    cyclicResidualIndexCode 4 dst hoff W 3 (cyclicResidualIndex s a b i) wl hwl v S hwidth hblank hwork hfit hcode

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
