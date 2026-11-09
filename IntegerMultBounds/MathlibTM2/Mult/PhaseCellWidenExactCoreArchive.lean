module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExactCoreRowsWiden
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWidenedReplicaPublication

/-! One counted width conversion for a complete certified core archive.
The exact endpoint and accuracy refer to the same transformed batches. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.LayerMachine
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

theorem widenExactCoreArchive_exec {wide word count src work saved tmp extra : Fin T}
    (hreg : [wide,word,count,src,work,saved,tmp,extra].Nodup)
    (p w W width : ℕ) (hA : 4 ≤ A) (hw : 1 ≤ w) (hW : w ≤ W)
    (Fs : List (ZMod s → GaussianInt)) (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (ks : List ℕ) (batches : List (List (List GaussianInt)))
    (hrows : List.Forall₂ (fun k rows => ExactCoreRows (A := A) p w width k Fs J rows) ks batches)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hwide : (S.R wide).length = W) (hword : (S.R word).length = w)
    (hcount : (S.R count).length = batches.flatten.flatten.length*w)
    (hsrc : S.R src = (batches.map (fun rows => cstream A w rows.flatten)).flatten++tail)
    (hblank : ∀ r ∈ [work,saved,tmp,extra], S.R r = []) (depth : ℕ) :
    let wideBatches := batches.map (List.map (List.map (symZ w)))
    ∃ v' n, v'.user = v.user ∧ n ≤ 40*(batches.flatten.flatten.length+1)*W ∧
      List.Forall₂ (fun k rows => ExactCoreRows (A := A) p W width k Fs J rows) ks wideBatches ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        520*(batches.flatten.flatten.length+1)*W) depth
        (widenPackedPrefix wide word count src work saved tmp extra) (mk v S) n
        (mk v' {S with R := (Function.update S.R src
          ((wideBatches.map (fun rows => cstream A W rows.flatten)).flatten++tail))}) := by
  dsimp only
  have encode (B : List (List (List GaussianInt))) (q : ℕ) :
      cstream A q B.flatten.flatten = (B.map (fun rows => cstream A q rows.flatten)).flatten := by
    induction B with
    | nil => simp
    | cons rows B ih => simp [ih]
  obtain ⟨v',n,huser,htime,he⟩ := widenEncodedPrefix_exec (body := body) hreg w W hw hW
    batches.flatten.flatten tail v S hwide hword hcount (by rw [encode]; exact hsrc) hblank
  have htimeVolume := htime.trans (widenPackedPrefixCost_le_volume w W
    batches.flatten.flatten.length (hw.trans hW) hW)
  have hwithin := mn_native_exec_within he 13
    (widenPackedPrefix_native wide word count src work saved tmp extra) depth
    (mnSize (mk v S)+depth+520*(batches.flatten.flatten.length+1)*W) (by nlinarith only [htimeVolume])
  have hflat : (batches.map (List.map (List.map (symZ w)))).flatten.flatten =
      batches.flatten.flatten.map (symZ w) := by simp [List.map_flatten]
  refine ⟨v',n,huser,htimeVolume,exactCoreRows_widen_batches hrows hA hw hW,?_⟩
  rw [←hflat,encode] at hwithin
  exact hwithin

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
