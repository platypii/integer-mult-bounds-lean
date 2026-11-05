module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellChunkDimensionBankStock

/-! The retained narrow crop count and replica clock determine widening volume.
Register 54 is outside the boundary metadata table and publication controls. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

def standardSeamWidenCount : Pr P 117 Q A U := unaryProduct 15 54 19 27 28

theorem standardSeamWidenCount_exec (N L w : ℕ) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hN : (S.R 15).length = N) (hbits : (S.R 54).length = L*w)
    (hcount : S.R 19 = []) (htmp : S.R 27 = []) (hsaved : S.R 28 = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ N*(4*(L*w)+9)+4 ∧
      Exec body standardSeamWidenCount (mk v S) n
        (mk v' {S with R := Function.update S.R 19 (List.replicate (N*L*w) tick)}) := by
  obtain ⟨v',n,hu,hn,he⟩ := unaryProduct_exec (body := body)
    (a := 15) (b := 54) (dst := 19) (t₁ := 27) (t₂ := 28) (by decide +kernel) v S htmp hsaved
  refine ⟨v',n,hu,?_,?_⟩
  · simpa only [hN,hbits] using hn
  · simpa only [standardSeamWidenCount,hN,hbits,hcount,List.append_nil,Nat.mul_assoc] using he

theorem standardSeamWidenCount_within (v v' : HS 117 Q A U) (S F : Stacks 117 A)
    (n depth : ℕ) (he : Exec body standardSeamWidenCount (mk v S) n (mk v' F)) :
    ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+2*n) depth
      standardSeamWidenCount (mk v S) n (mk v' F) :=
  mn_native_exec_within he 2 (unaryProduct_native 15 54 19 27 28) depth _ (by omega)

theorem standardSeamWidenCount_cost_le (N L w s : ℕ)
    (hs : 1 ≤ s) (hw : 1 ≤ w) (hL : L ≤ s) :
    N*(4*(L*w)+9)+4 ≤ 13*(N+1)*(s*w) := by
  have hvolume : 1 ≤ s*w := Nat.mul_pos hs hw
  have hbits := Nat.mul_le_mul_right w hL
  have hreplicas := Nat.mul_le_mul_left N hbits
  have hN : N ≤ N*(s*w) := by nlinarith
  nlinarith

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
