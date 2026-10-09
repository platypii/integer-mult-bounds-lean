import IntegerMultBounds.Machine.DescriptorStackControl
import IntegerMultBounds.Machine.Copy
import IntegerMultBounds.Machine.WordSegments
import IntegerMultBounds.Machine.LoopChain

/-! A fixed three-bit representation connects the six-symbol coefficient
streams to Boolean payload records. Each source symbol is retained and every
output bit is physically written; the converter has no width-dependent control. -/
namespace IntegerMultBounds.Machine.SymbolTripleEncode
noncomputable section

def bit (s : Fin 6) (i : Fin 3) : Bool := (s.val / 2^(2-i.val)) % 2 = 1

def code (s : Fin 6) : List Bool := List.ofFn (bit s)
def encoded (s : Fin 6) : List (Fin 6) := (code s).map bitSymbol

theorem code_length (s : Fin 6) : (code s).length=3 := by simp [code]
theorem code_injective : Function.Injective code := by
  intro s t he
  fin_cases s <;> fin_cases t <;> norm_num [code,bit,List.ofFn_succ] at *

def action (i : Fin 3) (move : Move) (sy : Fin 2 → Fin 6) (j : Fin 2) : Fin 6 × Move :=
  if j=0 then (sy 0,move) else (bitSymbol (bit (sy 0) i),.right)
def writer (i : Fin 3) (move : Move) := DescriptorStackControl.once (by decide : 0<2) (action i move)
def body := seq (seq (writer 0 .stay) (writer 1 .stay)) (writer 2 .right)

private theorem writer_runs (i : Fin 3) (move : Move) (f g : ℤ → Fin 6) (p r : ℤ) :
    HoareTime (writer i move) (fun v => v=Copy.tapes f g p r)
      (fun v => v=Copy.tapes f (Function.update g r (bitSymbol (bit (f p) i)))
        (p+move.offset) (r+1)) 1 := by
  have h := DescriptorStackControl.once_hoare (by decide : 0<2) (action i move) (Copy.tapes f g p r)
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro v rfl
  apply congrArg₂ Tapes.mk
  · funext j; fin_cases j <;> rfl
  · funext j z; fin_cases j
    · change (if z=p then f p else f z)=f z
      split_ifs with hz <;> simp_all
    · simp [action,Copy.tapes,Copy.cfg,Config.tapes,Function.update_apply]

theorem body_runs (f g : ℤ → Fin 6) (p r : ℤ) :
    HoareTime body (fun v => v=Copy.tapes f g p r)
      (fun v => v=Copy.tapes f (putWord g r (encoded (f p))) (p+1) (r+3)) 5 := by
  have h0 := writer_runs 0 .stay f g p r
  have h1 := writer_runs 1 .stay f (Function.update g r (bitSymbol (bit (f p) 0))) p (r+1)
  have h2 := writer_runs 2 .right f
    (Function.update (Function.update g r (bitSymbol (bit (f p) 0))) (r+1) (bitSymbol (bit (f p) 1))) p (r+2)
  have he : putWord g r (encoded (f p)) =
      Function.update (Function.update (Function.update g r (bitSymbol (bit (f p) 0)))
        (r+1) (bitSymbol (bit (f p) 1))) (r+2) (bitSymbol (bit (f p) 2)) := by
    change putWord g r [bitSymbol (bit (f p) 0),bitSymbol (bit (f p) 1),bitSymbol (bit (f p) 2)] = _
    rw [putWord_cons,putWord_cons,putWord]
    congr 1
    ring
  simp only [Move.offset,add_zero] at h0 h1 h2
  rw [he]
  rw [show r+1+1=r+2 by ring] at h1
  rw [show r+2+1=r+3 by ring] at h2
  exact (h0.seq h1).seq h2

end
end IntegerMultBounds.Machine.SymbolTripleEncode
