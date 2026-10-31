module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReversePackedLines
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedReplicaGatherData

/-! Align the restored packed ambient bank with the gathered solver's reversed
replica order. Use the retained symbol volume and preserve the replica count. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A s : ℕ} {P U : Type} {body : P → Pr P 126 Q A U}

def reverseGatheredAmbient : Pr P 126 Q A U :=
  retainedReversePackedLines 121 125 123 124 110 122 7

theorem reverseGatheredAmbient_exec_within (origin span w : ℕ)
    (Fs : List (ZMod s → GaussianInt)) (hspan : origin+span ≤ s)
    (tail : List (Fin (A+4))) (v : HS 126 Q A U) (S : Stacks 126 A)
    (hcount : (S.R 121).length = Fs.length) (hvolume : (S.R 123).length = span*w)
    (hsrc : S.R 124 = Fs.flatMap (fun F => cstream A w (packedInterval origin span F))++tail)
    (hclean : ∀ k ∈ [(125 : Fin 126),122,7], S.R k = []) (depth : ℕ) :
    ∃ v' F n, v'.user = v.user ∧ n ≤ Fs.length*(6*(span*w)+13)+6 ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        2*(Fs.length*(6*(span*w)+13)+6)) depth reverseGatheredAmbient (mk v S) n (mk v' F) ∧
      F.R 124 = tail ∧
      F.R 110 = Fs.reverse.flatMap (fun F => cstream A w (packedInterval origin span F))++S.R 110 ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      ∀ k, k ≠ 124 → k ≠ 110 → F.R k = S.R k := by
  let lines := Fs.map (fun F => cstream A w (packedInterval origin span F))
  obtain ⟨v',F,n,hu,hn,he,hs,hd,hi,ho,hl,hframe⟩ := retainedReversePackedLines_exec (body := body)
    121 125 123 124 110 122 7 (by decide) lines (span*w)
    (by
      intro xs hx
      obtain ⟨C,_,rfl⟩ := List.mem_map.mp hx
      rw [length_cstream,packedInterval_length C hspan])
    tail v S (by simpa [lines] using hcount) hvolume (by simpa [lines,List.flatMap_def] using hsrc)
    (hclean 125 (by simp)) (hclean 122 (by simp)) (hclean 7 (by simp))
  have hn' : n ≤ Fs.length*(6*(span*w)+13)+6 := by simpa only [lines,List.length_map] using hn
  refine ⟨v',F,n,hu,hn',?_,hs,?_,hi,ho,hl,hframe⟩
  · exact mn_native_exec_within he 2 (retainedReversePackedLines_pushBound _ _ _ _ _ _ _) depth _ (by omega)
  · simpa only [lines,List.map_reverse,List.flatMap_def] using hd

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
