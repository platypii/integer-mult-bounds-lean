module

public import IntegerMultBounds.MathlibTM2.Routing.ProductBinaryHeader
public import IntegerMultBounds.MathlibTM2.Routing.FieldHeaderCopy

/-! Ordinary N,L,H,B,w,V masters produce all three binary halo metadata words.
Byte-width and doubled-halo intermediates are retired before the pass. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.HaloBinaryHeaders
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main FieldHeaderSetup FieldHeaderCopy
open IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

def run : Pr P 117 Q A U :=
  .seq (resetProduct 45 47 67 57 58)
    (.seq (toBinary 44 115 97 57 58 116)
      (.seq (ProductBinaryHeader.run 55 67 115 68 98 57 58 116)
        (.seq (resetCopy 65 69 57)
          (.seq (ucopy 65 69 57)
            (.seq (ProductBinaryHeader.run 69 67 115 68 100 57 58 116)
              (clearWords [67,69]))))))

def cost (N L H B w V : ℕ) :=
  B*(4*w+9)+6+(N*(4*V+10)+4*V+8)+ProductBinaryHeader.cost L (B*w) V+
    (4*H+6)+(4*H+4)+ProductBinaryHeader.cost (2*H) (B*w) V+2*(B*w+2*H)+5

def reserve (L H B w V : ℕ) :=
  2*(B*(4*w+9)+6)+(8*V+8)+ProductBinaryHeader.reserve L (B*w) V+
    2*(4*H+6)+2*(4*H+4)+ProductBinaryHeader.reserve (2*H) (B*w) V

def result (S : Stacks 117 A) (N L H B w V : ℕ) : Stacks 117 A :=
  {S with R := (Function.update (Function.update (Function.update S.R 97 (binSyms V N))
    98 (binSyms V (L*(B*w)))) 100 (binSyms V (2*H*(B*w))))}

theorem run_exec (N L H B w V : ℕ) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hN : (S.R 44).length = N) (hL : (S.R 55).length = L)
    (hH : (S.R 65).length = H) (hB : (S.R 45).length = B)
    (hw : (S.R 47).length = w) (hV : (S.R 115).length = V)
    (hblank : ∀ i ∈ [(67 : Fin 117),68,69,97,98,100,57,58], S.R i = []) :
    ∃ vf n, vf.user = v.user ∧ n ≤ cost N L H B w V ∧
      Exec body run (mk v S) n (mk vf (result S N L H B w V)) ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+reserve L H B w V)
        depth run (mk v S) n (mk vf (result S N L H B w V))) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := resetProduct_exec (body := body) 45 47 67 57 58 (by decide) v S
    (hblank _ (by simp)) (hblank _ (by simp))
  have hn₁' : n₁ ≤ B*(4*w+9)+6 := by simp [hB,hw,hblank] at hn₁; omega
  let F : Stacks 117 A := {S with R := Function.update S.R 67 (List.replicate (B*w) tick)}
  have he₁' : Exec body (resetProduct 45 47 67 57 58) (mk v S) n₁ (mk v₁ F) := by simpa [hB,hw] using he₁
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := toBinary_exec (body := body)
    (u := 44) (wR := 115) (c := 97) (t := 57) (tmp := 58) (by decide) 116 v₁ F
    (by simp [F,hblank]) (by simp [F,hblank]) (by simp [F,hblank])
  have hn₂' : n₂ ≤ N*(4*V+10)+4*V+8 := by simpa [F,hN,hV] using hn₂
  let G : Stacks 117 A := {F with R := Function.update F.R 97 (binSyms V N)}
  have he₂' : Exec body (toBinary 44 115 97 57 58 116) (mk v₁ F) n₂ (mk v₂ G) := by
    simpa [F,hN,hV] using he₂
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃,hs₃⟩ := ProductBinaryHeader.run_exec (body := body) 55 67 115 68 98 57 58 116
    (by decide) L (B*w) V v₂ G (by simp [G,F,hL]) (by simp [G,F]) (by simp [G,F,hV]) (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl <;> simp [G,F,hblank])
  let J : Stacks 117 A := {G with R := Function.update G.R 98 (binSyms V (L*(B*w)))}
  obtain ⟨v₄,hu₄,he₄⟩ := resetCopy_exec (body := body) 65 69 57 (by decide) v₃ J (by simp [J,G,F,hblank])
  let K : Stacks 117 A := {J with R := Function.update J.R 69 (List.replicate H tick)}
  have he₄' : Exec body (resetCopy 65 69 57) (mk v₃ J) (4*H+6) (mk v₄ K) := by
    simpa [J,G,F,hH,hblank] using he₄
  obtain ⟨v₅,hu₅,he₅⟩ := ucopy_exec (body := body) (a := 65) (b := 69) (t := 57)
    (by decide) (by decide) (by decide) v₄ K (by simp [K,J,G,F,hblank])
  let M : Stacks 117 A := {K with R := Function.update K.R 69 (List.replicate (2*H) tick)}
  have he₅' : Exec body (ucopy 65 69 57) (mk v₄ K) (4*H+4) (mk v₅ M) := by
    simpa [M,K,J,G,F,hH,←List.replicate_add,Nat.two_mul] using he₅
  obtain ⟨v₆,n₆,hu₆,hn₆,he₆,hs₆⟩ := ProductBinaryHeader.run_exec (body := body) 69 67 115 68 100 57 58 116
    (by decide) (2*H) (B*w) V v₅ M (by simp [M]) (by simp [M,K,J,G,F])
    (by simp [M,K,J,G,F,hV]) (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl <;> simp [M,K,J,G,F,hblank])
  let O : Stacks 117 A := {M with R := Function.update M.R 100 (binSyms V (2*H*(B*w)))}
  obtain ⟨vf,hu₇,he₇⟩ := clearWords_exec (body := body) [67,69] (by decide) v₆ O
  have h67 : (O.R 67).length = B*w := by simp [O,M,K,J,G,F]
  have h69 : (O.R 69).length = 2*H := by simp [O,M]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil,h67,h69] at he₇
  have hfinal : {O with R := (fun j => if j ∈ [(67 : Fin 117),69] then [] else O.R j)} = result S N L H B w V := by
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hi67 : i = 67
    · subst i; simp [result,hblank]
    by_cases hi69 : i = 69
    · subst i; simp [result,hblank]
    · simp [O,M,K,J,G,F,result,hi67,hi69,Function.update_apply]
  refine ⟨vf,n₁+(n₂+(n₃+((4*H+6)+((4*H+4)+(n₆+(2*(B*w+(2*H+0))+2*(0+1+1)+1)))))),
    hu₇.trans (hu₆.trans (hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))))),?_,?_,?_⟩
  · dsimp only [cost]
    omega
  · exact (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃ (Exec.seq he₄' (Exec.seq he₅'
      (Exec.seq he₆ he₇)))))).cast rfl (congrArg (mk vf) hfinal)


  · intro depth
    have hs₁ := mn_native_exec_within he₁' 2 (resetProduct_pushBound _ _ _ _ _) depth
      (mnSize (mk v S)+depth+2*(B*(4*w+9)+6)) (by omega)
    have hs₂ := toBinary_within 44 115 97 57 58 116 (by decide) v₁ F
      (by simp [F,hblank]) he₂' depth
    have hs₄ := mn_native_exec_within he₄' 2 (resetCopy_pushBound _ _ _) depth
      (mnSize (mk v₃ J)+depth+2*(4*H+6)) (by omega)
    have hs₅ := mn_native_exec_within he₅' 2 (by
      simp [ucopy,umulSym,scanR,keepIn,pushN,drainR,popDo,moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]) depth
      (mnSize (mk v₄ K)+depth+2*(4*H+4)) (by omega)
    have hs₇ := mn_native_exec_within he₇ 0 (clearWords_native _) depth
      (mnSize (mk v₆ O)+depth+0) (by simp)
    have hs := mn_seq_within_add hs₁ (mn_seq_within_add hs₂ (mn_seq_within_add (hs₃ depth)
      (mn_seq_within_add hs₄ (mn_seq_within_add hs₅ (mn_seq_within_add (hs₆ depth) hs₇)))))
    refine (hs.mono ?_).cast rfl (congrArg (mk vf) hfinal)
    intro d z hz
    simp only [F,Function.update_of_ne (by decide : (115 : Fin 117) ≠ 67),hV] at hz
    dsimp only [reserve]
    omega

end IntegerMultBounds.MathlibTM2.Routing.HaloBinaryHeaders
