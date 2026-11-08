module

public import IntegerMultBounds.MathlibTM2.Fast.TableDiagonalSetup
public import IntegerMultBounds.MathlibTM2.Fast.TableNativePush
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedInterval

/-! Execute a local D' page in the existing packed real-factor ABI. The page
uses global source indices and can be retained across all replicas of a core. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.Resampling.WeightTable
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def diagonalField (s t α p : ℕ) (i : ZMod s) : GaussianInt := ⟨tableD s t α p i,0⟩

theorem diagonalInterval_packed (A w s t α p c n : ℕ) (hfit : c+n ≤ s) :
    diagonalInterval A w s t α p c n = cstream A w (packedInterval c n (diagonalField s t α p)) := by
  have he : (List.range n).map (fun j => diagonalField s t α p ((c+j : ℕ) : ZMod s)) =
      packedInterval c n (diagonalField s t α p) := by
    apply List.ext_getElem (by simp [packedInterval_length _ hfit])
    intro j hj hj'
    have hjn : j < n := by simpa using hj
    rw [packedInterval_get _ hfit hjn]
    simp
  rw [←he]
  simp only [diagonalInterval,cstream,List.flatMap_map,diagonalField,csyms]

def ownedDiagonalPage (rg : TblR 48 → Fin T) (out : Fin T) : Pr P T Q A U :=
  tblHost rg tblOwnedDiagonal out

def ownedDiagonalPageCost (W w p n : ℕ) : ℕ :=
  ((160*p+450)+(n*(310*p+123)+2))*tblC W w+2*(n*w)+2

theorem ownedDiagonalPage_native (rg : TblR 48 → Fin T) (out : Fin T) :
    mnNativePushBound 3 (ownedDiagonalPage (P := P) (Q := Q) (A := A) (U := U) rg out) := by
  refine ⟨tblCompile_native ..,?_⟩
  simp [moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]

theorem ownedDiagonalPage_exec (rg : TblR 48 → Fin T) (hrg : Function.Injective rg)
    (out : Fin T) (hout : ∀ r, rg r ≠ out) {W w s t α p c n : ℕ}
    (wl nl : List (Fin (A+4))) (hwl : wl.length = W) (hnl : nl.length = w) (hw : w ≤ W)
    (st : TblSt 48 A) (hS : st.val 34 = s) (hT : st.val 35 = t) (huval : st.val 36 = α^2)
    (hpval : st.val 19 = p) (hc : st.val 37 = c) (hend : st.val 47 = c+n)
    (hs : 0 < s) (hfit : c+n ≤ s) (hp : 13 ≤ p) (hα : 2 ≤ α) (hαp : α^2 ≤ p)
    (hW : α^2*(s+t)^2*2^(13*p+8) < 2^W) (hbound : ∀ i, st.val i < 2^W) (hacc : st.acc = [])
    (v : HS T Q A U) (S : Stacks T A) (hholds : tblHolds rg S (tblRho W wl nl st)) :
    ∃ v' F m, v'.user = v.user ∧ m ≤ ownedDiagonalPageCost W w p n ∧
      Exec body (ownedDiagonalPage rg out) (Host.mk v S) m (Host.mk v' F) ∧
      F.R out = cstream A w (packedInterval c n (diagonalField s t α p))++S.R out ∧
      (∃ st', st'.acc = [] ∧ tblHolds rg F (tblRho W wl nl st')) ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      (∀ k, k ≠ out → (∀ r, rg r ≠ k) → F.R k = S.R k) ∧
      ∀ depth, ExecWithin body (fun j z => mnSize z+j ≤ mnSize (Host.mk v S)+depth+
        3*ownedDiagonalPageCost W w p n) depth (ownedDiagonalPage rg out) (Host.mk v S) m (Host.mk v' F) := by
  have hd := tblOwnedDiagonal_do (W := W) (w := w) st hS hT huval hpval hc hend hs hfit hp hα hαp hW
  obtain ⟨v',F,m,st',hpacc,hu,hm,he,hpage,ht,hi,ho,hl,hframe⟩ := tblHost_runs (body := body)
    hrg hout wl nl hwl hnl hw hd hbound v S hholds
  rw [hacc,List.append_nil] at hpacc
  rw [hpacc,List.reverse_reverse] at hpage
  rw [hpacc,List.length_reverse] at hm
  have hlen : (diagonalInterval A w s t α p c n).length = n*w := by
    simp [diagonalInterval,coeffSyms,List.length_flatMap]
  rw [hlen] at hm
  change m ≤ ownedDiagonalPageCost W w p n at hm
  rw [diagonalInterval_packed A w s t α p c n hfit] at hpage
  refine ⟨v',F,m,hu,hm,he,hpage,⟨⟨st'.val,[]⟩,rfl,ht⟩,hi,ho,hl,hframe,fun depth => ?_⟩
  exact mn_native_exec_within he 3 (ownedDiagonalPage_native ..) depth _ (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
