module

public import IntegerMultBounds.MathlibTM2.Routing.HaloPassContext
public import IntegerMultBounds.MathlibTM2.Routing.FieldHeaderSetup
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupStock

/-! Produce the two coefficient-volume headers from ordinary axis dimensions.
The N*L intermediate is retired before entering the halo pass. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.HaloUnaryHeaders
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main FieldHeaderSetup
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

def run : Pr P 117 Q A U :=
  .seq (resetProduct 44 55 66 57 58)
    (.seq (resetProduct 66 45 31 57 58)
      (.seq (resetProduct 65 45 32 57 58) (uclear 66)))

def cost (N L H B : ℕ) := N*(4*L+9)+(N*L)*(4*B+11)+H*(4*B+9)+20

def result (S : Stacks 117 A) (N L H B : ℕ) : Stacks 117 A :=
  {S with R := (Function.update (Function.update S.R 31 (List.replicate (N*L*B) tick))
    32 (List.replicate (H*B) tick))}

theorem run_exec (N L H B : ℕ) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hN : (S.R 44).length = N) (hL : (S.R 55).length = L)
    (hH : (S.R 65).length = H) (hB : (S.R 45).length = B)
    (hblank : ∀ i ∈ [(31 : Fin 117),32,66,57,58], S.R i = []) :
    ∃ vf n, vf.user = v.user ∧ n ≤ cost N L H B ∧
      Exec body run (mk v S) n (mk vf (result S N L H B)) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := resetProduct_exec (body := body) 44 55 66 57 58 (by decide) v S
    (hblank _ (by simp)) (hblank _ (by simp))
  have hn₁' : n₁ ≤ N*(4*L+9)+6 := by simp [hN,hL,hblank] at hn₁; omega
  let F : Stacks 117 A := {S with R := Function.update S.R 66 (List.replicate (N*L) tick)}
  have he₁' : Exec body (resetProduct 44 55 66 57 58) (mk v S) n₁ (mk v₁ F) := by
    simpa only [hN,hL] using he₁
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := resetProduct_exec (body := body) 66 45 31 57 58 (by decide) v₁ F
    (by simp [F,hblank]) (by simp [F,hblank])
  have hn₂' : n₂ ≤ (N*L)*(4*B+9)+6 := by simp [F,hB,hblank] at hn₂; omega
  let G : Stacks 117 A := {F with R := Function.update F.R 31 (List.replicate (N*L*B) tick)}
  have he₂' : Exec body (resetProduct 66 45 31 57 58) (mk v₁ F) n₂ (mk v₂ G) := by
    simpa [F,hB] using he₂
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := resetProduct_exec (body := body) 65 45 32 57 58 (by decide) v₂ G
    (by simp [G,F,hblank]) (by simp [G,F,hblank])
  have hn₃' : n₃ ≤ H*(4*B+9)+6 := by simp [G,F,hH,hB,hblank] at hn₃; omega
  let J : Stacks 117 A := {G with R := Function.update G.R 32 (List.replicate (H*B) tick)}
  have he₃' : Exec body (resetProduct 65 45 32 57 58) (mk v₂ G) n₃ (mk v₃ J) := by
    simpa [G,F,hH,hB] using he₃
  obtain ⟨vf,hu₄,he₄⟩ := uclear_exec (body := body) 66 v₃ J
  have h66 : (J.R 66).length = N*L := by simp [J,G,F]
  rw [h66] at he₄
  have hfinal : {J with R := Function.update J.R 66 []} = result S N L H B := by
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hi : i = 66
    · subst i; simp [result,hblank]
    · simp [J,G,F,result,hi,Function.update_apply]
  refine ⟨vf,n₁+(n₂+(n₃+(2*(N*L)+2))),hu₄.trans (hu₃.trans (hu₂.trans hu₁)),?_,?_⟩
  · dsimp only [cost]
    nlinarith only [hn₁',hn₂',hn₃']
  · exact (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃' he₄))).cast rfl (congrArg (mk vf) hfinal)

theorem run_native : mnNativePushBound 2 (run (P := P) (Q := Q) (A := A) (U := U)) :=
  ⟨resetProduct_pushBound _ _ _ _ _,resetProduct_pushBound _ _ _ _ _,resetProduct_pushBound _ _ _ _ _,
    by simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]⟩

theorem run_exec_within (N L H B : ℕ) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hN : (S.R 44).length = N) (hL : (S.R 55).length = L)
    (hH : (S.R 65).length = H) (hB : (S.R 45).length = B)
    (hblank : ∀ i ∈ [(31 : Fin 117),32,66,57,58], S.R i = []) :
    ∃ vf n, vf.user = v.user ∧ n ≤ cost N L H B ∧
      Exec body run (mk v S) n (mk vf (result S N L H B)) ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+2*cost N L H B)
        depth run (mk v S) n (mk vf (result S N L H B))) := by
  obtain ⟨vf,n,hu,hn,he⟩ := run_exec (body := body) N L H B v S hN hL hH hB hblank
  refine ⟨vf,n,hu,hn,he,?_⟩
  intro depth
  exact mn_native_exec_within he 2 run_native depth _ (by omega)

end IntegerMultBounds.MathlibTM2.Routing.HaloUnaryHeaders
