module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateReplicaControls
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaGather
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBatchSetupHeaders
public import IntegerMultBounds.MathlibTM2.StackResources

/-! Gather a same-origin cell batch from raw consecutive RHS lines. Controls and temporary counts are generated and released; retained widths,
ambient input and its borrowed suffix survive. The payload has its own register. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def rawReplicaPayload : Pr P₀ 117 Q A U :=
  .seq generateReplicaControls
    (.seq (unaryProduct 116 97 10 6 7) (.seq (unaryProduct 10 94 11 6 7)
      (.seq (copyPrefix 11 110 92 6 7)
        (.seq (naturalGather 93 91 1 2 0 92 3 4 5 6 7 8 9 102 94)
          (clearWords [92,10,11,91])))))

def rawReplicaPayloadCost (w s p L B : ℕ) : ℕ :=
  let volume := (B+1)*s*w
  let controlLength := p*w+B*(s*w)+B+2
  generateReplicaControlsCost B s p w+((B+1)*(4*s+9)+4)+
    (((B+1)*s)*(4*w+9)+4)+(10*volume+10)+
    ((B+1)*(14*L*w+25)+12*volume+6*L*w+9*L+29)+
    (2*(2*volume+(B+1)*s+controlLength)+9)

theorem rawReplicaPayload_exec {s : ℕ} (w p L B : ℕ) (C : ℕ → ZMod s → GaussianInt)
    (hspan : p+L ≤ s) (borrowed : List (Fin (A+4))) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hw : (S.R 94).length = w) (hs : (S.R 97).length = s) (hp : (S.R 111).length = p)
    (hL : (S.R 102).length = L) (hB : (S.R 116).length = B+1)
    (hsrc : S.R 110 = cstream A w (replicaAmbientWords (B+1) C)++borrowed)
    (hblank : ∀ k : Fin 117, k.val < 13 → S.R k = [])
    (hfresh : ∀ k ∈ [(91 : Fin 117),92], S.R k = []) :
    let rhs := cstream A w ((List.range (B+1)).flatMap (cellSourceRows L (fun _ => (p : ZMod s)) C))
    ∃ v' n, v'.user = v.user ∧ n ≤ rawReplicaPayloadCost w s p L B ∧
      Exec body rawReplicaPayload (mk v S) n
        (mk v' { S with R := Function.update S.R 93 (rhs++S.R 93) }) := by
  dsimp only
  let volume := (B+1)*s*w
  let E := cstream A w (replicaAmbientWords (B+1) C)
  let rhs := cstream A w ((List.range (B+1)).flatMap (cellSourceRows L (fun _ => (p : ZMod s)) C))
  have hE : E.length = volume := by simp [E,volume]
  let v₁ := v
  let S₁ := S
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := generateReplicaControls_exec (body := body) B s p w v₁ S₁
    (by simpa [S₁] using hs) (by simpa [S₁] using hp) (by simpa [S₁] using hw) (by simpa [S₁] using hB) (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | simpa [S₁] using hblank _ (by decide) | simpa [S₁] using hfresh 91 (by simp))
  let S₂ : Stacks 117 A := { S₁ with R := Function.update S₁.R 91 (replicaGatherControls A (B+1) s p w) }
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := unaryProduct_exec (body := body)
    (show [(116 : Fin 117),97,10,6,7].Nodup by decide) v₂ S₂
    (by simpa [S₂,S₁] using hblank 6 (by decide)) (by simpa [S₂,S₁] using hblank 7 (by decide))
  let S₃ : Stacks 117 A := { S₂ with R := Function.update S₂.R 10 (List.replicate ((B+1)*s) tick) }
  have he₃' : Exec body (unaryProduct 116 97 10 6 7) (mk v₂ S₂) n₃ (mk v₃ S₃) := by
    simpa [S₃,S₂,S₁,hB,hs,hblank 10 (by decide)] using he₃
  obtain ⟨v₄,n₄,hu₄,hn₄,he₄⟩ := unaryProduct_exec (body := body)
    (show [(10 : Fin 117),94,11,6,7].Nodup by decide) v₃ S₃
    (by simpa [S₃,S₂,S₁] using hblank 6 (by decide)) (by simpa [S₃,S₂,S₁] using hblank 7 (by decide))
  let S₄ : Stacks 117 A := { S₃ with R := Function.update S₃.R 11 (List.replicate volume tick) }
  have he₄' : Exec body (unaryProduct 10 94 11 6 7) (mk v₃ S₃) n₄ (mk v₄ S₄) := by
    simpa [S₄,S₃,S₂,S₁,volume,hw,hblank 11 (by decide)] using he₄
  obtain ⟨v₅,hu₅,he₅⟩ := copyPrefix_exec (body := body)
    (show [(11 : Fin 117),110,92,6,7].Nodup by decide) v₄ S₄ E borrowed
    (by simpa [S₄,S₃,S₂,S₁] using hsrc) (by simp [S₄,hE])
    (by simpa [S₄,S₃,S₂,S₁] using hblank 6 (by decide))
    (by simpa [S₄,S₃,S₂,S₁] using hblank 7 (by decide))
  let S₅ : Stacks 117 A := { S₄ with R := Function.update S₄.R 92 E }
  have he₅' : Exec body (copyPrefix 11 110 92 6 7) (mk v₄ S₄) (10*volume+10) (mk v₅ S₅) := by
    simpa [S₅,S₄,S₃,S₂,S₁,hE,hfresh 92 (by simp)] using he₅
  obtain ⟨v₆,n₆,hu₆,hn₆,he₆⟩ := replicaGather_exec (body := body)
    (dst := 93) (control := 91) (savedControl := 1) (advance := 2) (window := 0) (src := 92)
    (acc := 3) (current := 4) (savedSource := 5) (buf := 6) (tmp := 7) (initialControl := 8)
    (initialSource := 9) (rowCount := 102) (wordR := 94) (by decide) (B+1) p L w C (by omega) hspan v₅ S₅
    (by simp [S₅,S₄,S₃,S₂]) (by simp [S₅,E]) (by simpa [S₅,S₄,S₃,S₂,S₁] using hL)
    (by simpa [S₅,S₄,S₃,S₂,S₁] using hw) (by
      intro k hk
      have hlo : k.val < 10 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      have hn (n : Fin 117) (h : 10 ≤ n.val) : k ≠ n := by intro he; subst k; omega
      simpa [S₅,S₄,S₃,S₂,S₁,hn 92 (by decide),hn 11 (by decide),hn 10 (by decide),
        hn 91 (by decide),hn 94 (by decide)] using hblank k (by omega))
  let S₆ : Stacks 117 A := { S₅ with R := Function.update S₅.R 93 (rhs++S₅.R 93) }
  obtain ⟨v₇,hu₇,he₇⟩ := clearWords_exec (body := body) [(92 : Fin 117),10,11,91] (by decide) v₆ S₆
  have hcontrolLength : (replicaGatherControls A (B+1) s p w).length = p*w+B*(s*w)+B+2 := by
    rw [replicaGatherControls_succ]
    simp [length_gatherControls]
    ring
  have hsum : ([(92 : Fin 117),10,11,91].map (fun k => (S₆.R k).length)).sum =
      2*volume+(B+1)*s+(p*w+B*(s*w)+B+2) := by
    simp [S₆,S₅,S₄,S₃,S₂,S₁,hE,hcontrolLength]
    ring
  let cleanupCost := 2*(2*volume+(B+1)*s+(p*w+B*(s*w)+B+2))+9
  refine ⟨v₇,n₂+(n₃+(n₄+((10*volume+10)+(n₆+cleanupCost)))),
    (hu₇.trans (hu₆.trans (hu₅.trans (hu₄.trans (hu₃.trans hu₂))))),?_,
    (Exec.seq he₂ (Exec.seq he₃' (Exec.seq he₄' (Exec.seq he₅' (Exec.seq he₆ he₇))))).cast
      (by rw [hsum]; rfl) ?_⟩
  · have hn₃' : n₃ ≤ (B+1)*(4*s+9)+4 := by simpa [S₂,S₁,hB,hs] using hn₃
    have hn₄' : n₄ ≤ ((B+1)*s)*(4*w+9)+4 := by simpa [S₃,S₂,S₁,hw] using hn₄
    dsimp only [rawReplicaPayloadCost,cleanupCost]
    dsimp only [volume] at *
    omega
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases h92 : k = 92
    · subst k; simp [hfresh 92 (by simp)]
    by_cases h10 : k = 10
    · subst k; simp [hblank 10 (by decide)]
    by_cases h11 : k = 11
    · subst k; simp [hblank 11 (by decide)]
    by_cases h91 : k = 91
    · subst k; simp [hfresh 91 (by simp)]
    simp [S₆,S₅,S₄,S₃,S₂,S₁,Function.update_apply,h92,h10,h11,h91,rhs]

/-- The transport is linear in the full encoded replica input volume. -/
theorem rawReplicaPayloadCost_le (w s p L B : ℕ) (hwpos : 0 < w) (hL : 0 < L) (hspan : p+L ≤ s) :
    rawReplicaPayloadCost w s p L B ≤ 250*((B+1)*s*w) := by
  have hw : 1 ≤ w := hwpos
  have hs : 1 ≤ s := by omega
  have hspanw := Nat.mul_le_mul_right w hspan
  have hspanBw := Nat.mul_le_mul_right w (Nat.mul_le_mul_left (B+1) hspan)
  have hRs : (B+1)*s ≤ (B+1)*s*w := Nat.le_mul_of_pos_right _ (by omega)
  have hR : B+1 ≤ (B+1)*s*w := (Nat.le_mul_of_pos_right _ (by omega : 0 < s)).trans hRs
  have hsw : s*w ≤ (B+1)*s*w := by nlinarith only [Nat.zero_le (B*s*w)]
  have hswpos : 1 ≤ s*w := by simpa using Nat.mul_le_mul hs hw
  have hsle : s ≤ s*w := Nat.le_mul_of_pos_right _ (by omega)
  have hwle : w ≤ s*w := Nat.le_mul_of_pos_left _ (by omega)
  dsimp only [rawReplicaPayloadCost,generateReplicaControlsCost]
  change _ ≤ 250*((B+1)*s*w)
  nlinarith only [hspan,hspanw,hspanBw,hRs,hR,hsw,hswpos,hsle,hwle]


open IntegerMultBounds.MathlibTM2.Fast.Main

theorem rawReplicaPayload_native : mnNativePushBound 2 (rawReplicaPayload (P₀ := P₀) (Q := Q) (A := A) (U := U)) := by
  simp [rawReplicaPayload,generateReplicaControls,repeatUnaryGatherControl,unaryGatherControl,
    naturalGather,gatherOffset,gatherBatch,gatherLoopBody,gatherPacket,gatherNext,gatherRead,gatherReadStep,WordCmd.peekRp,
    unaryProduct,copyPrefix,transfer,transferAct,clearWords,uclear,ucopy,umulSym,scanP,popPush,scanR,drainR,
    popDo,keepIn,pushN,copyR,copyStep,moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]

theorem rawReplicaPayload_exec_within {s : ℕ} (w p L B : ℕ) (C : ℕ → ZMod s → GaussianInt)
    (hwpos : 0 < w) (hLpos : 0 < L) (hspan : p+L ≤ s)
    (borrowed : List (Fin (A+4))) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hw : (S.R 94).length = w) (hs : (S.R 97).length = s) (hp : (S.R 111).length = p)
    (hL : (S.R 102).length = L) (hB : (S.R 116).length = B+1)
    (hsrc : S.R 110 = cstream A w (replicaAmbientWords (B+1) C)++borrowed)
    (hblank : ∀ k : Fin 117, k.val < 13 → S.R k = [])
    (hfresh : ∀ k ∈ [(91 : Fin 117),92], S.R k = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ rawReplicaPayloadCost w s p L B ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+500*((B+1)*s*w)) depth
        rawReplicaPayload (mk v S) n (mk v' {S with R := (Function.update S.R 93
          (cstream A w ((List.range (B+1)).flatMap (cellSourceRows L (fun _ => (p : ZMod s)) C))++S.R 93))}) := by
  obtain ⟨v',n,hu,hn,he⟩ := rawReplicaPayload_exec (body := body) w p L B C hspan borrowed v S
    hw hs hp hL hB hsrc hblank hfresh
  have htime := hn.trans (rawReplicaPayloadCost_le w s p L B hwpos hLpos hspan)
  exact ⟨v',n,hu,hn,mn_native_exec_within he 2 rawReplicaPayload_native depth _ (by omega)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
