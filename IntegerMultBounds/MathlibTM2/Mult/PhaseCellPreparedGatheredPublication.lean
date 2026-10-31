module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGatheredPublicationPages
public import IntegerMultBounds.MathlibTM2.StackStockComposition

/-! Generate publication pages, align and publish actual solver output, then
release both pages. All shared metadata and private scratch are restored. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A s L : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def preparedGatheredPublication (plan : ReplicaInteriorPlacement T) : Pr P T Q A U :=
  .seq (prepareGatheredPublicationPages plan) (.seq (routedGatheredPublication plan)
    (.seq (uclear (plan.gather 92)) (uclear (plan.gather 103))))

def preparedGatheredPublicationCost (N V span L w B : ℕ) :=
  prepareReplicaPublicationPagesCost V span L w B+
    (routedEncodedPublicationCost N (span*w)+(4*span*w+2*L*w+4))

def preparedGatheredPublicationWorkspace (Q A : ℕ) (U : Type) (N V span L w B : ℕ) :=
  mnProgPush (prepareReplicaPublicationPages (P := Empty) (Q := Q) (A := A) (U := U))*
    prepareReplicaPublicationPagesCost V span L w B+2*routedEncodedPublicationCost N (span*w)

theorem preparedGatheredPublication_exec_within (plan : ReplicaInteriorPlacement T)
    (V origin span : ℕ) (Fs : List (ZMod s → GaussianInt)) (hspan : origin+span ≤ s)
    (windows : PublicationWindows span L) {w q e : ℕ} (hw1 : 1 ≤ w)
    (hwV : w < 2^V) (hspanV : span < 2^V) (hunits : span*w < 2^V)
    (xs : BoundedEncodedStream A w q e)
    (hlen : xs.val.length = (Fs.length*windows.origins.length)*L*w)
    (sourceTail ambientTail suffix : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R (plan.solver 93) = xs.val++sourceTail)
    (hambient : S.R (plan.gather 124) = Fs.flatMap (fun F => cstream A w (packedInterval origin span F))++ambientTail)
    (hdst : S.R (plan.gather 110) = [])
    (hcount : (S.R (plan.gather 121)).length = Fs.length)
    (hvolume : (S.R (plan.gather 123)).length = span*w)
    (hV : (S.R (plan.gather 115)).length = V) (hw : (S.R (plan.gather 94)).length = w)
    (hL : (S.R (plan.gather 102)).length = L)
    (hpackets : S.R (plan.gather 109) = windows.origins.flatMap (binSyms V)++suffix)
    (hB : S.R (plan.gather 116) = List.replicate windows.origins.length tick)
    (hblank : ∀ k : Fin 126, k.val < 19 → S.R (plan.gather k) = [])
    (hfresh : ∀ k ∈ [(88 : Fin 126),89,90,91,92,103,104,105,106,107,122,125], S.R (plan.gather k) = []) (depth : ℕ) :
    ∃ v' F n, ∃ replicas : List (PublicationReplica A),
      replicas.map PublicationReplica.ambient = Fs.reverse.map (fun F => cstream A w (packedInterval origin span F)) ∧
      replicas.flatMap (PublicationReplica.input w) = xs.val ∧
      (∀ r ∈ replicas, r.Valid windows w 0) ∧ v'.user = v.user ∧
      n ≤ preparedGatheredPublicationCost Fs.length V span L w windows.origins.length ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        preparedGatheredPublicationWorkspace Q A U Fs.length V span L w windows.origins.length) depth
        (preparedGatheredPublication plan) (mk v S) n (mk v' F) ∧
      F.R (plan.solver 93) = sourceTail ∧ F.R (plan.gather 124) = ambientTail ∧
      F.R (plan.gather 110) = replicas.flatMap (PublicationReplica.output windows w) ∧
      F.R (plan.gather 121) = [] ∧ F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      ∀ i, i ≠ plan.solver 93 → i ≠ plan.gather 124 → i ≠ plan.gather 110 →
        i ≠ plan.gather 121 → F.R i = S.R i := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := prepareGatheredPublicationPages_exec_within (body := body)
    plan V w windows hw1 hwV hspanV hunits v S suffix hV hw hL hpackets hB hblank
    (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hfresh _ (by simp)) depth
  let M : Stacks T A := {S with R := (Function.update (Function.update S.R (plan.gather 103)
    (List.replicate (L*w) tick)) (plan.gather 92) (gatherControls A (windows.gaps w)))}
  have hg (k : Fin 126) (h103 : k ≠ 103) (h92 : k ≠ 92) : M.R (plan.gather k) = S.R (plan.gather k) := by
    simp [M,plan.gather_injective.ne h103,plan.gather_injective.ne h92]
  obtain ⟨v₂,F,n₂,replicas,ha,hinput,hvalid,hu₂,hn₂,he₂,hs₂,hd₂,hout₂,hclock₂,hi₂,ho₂,hl₂,hframe₂⟩ :=
    routedGatheredPublication_exec_within (body := body) plan origin span Fs hspan windows hw1 xs hlen
      sourceTail ambientTail v₁ M
      (by simpa [M,(plan.disjoint 103 93).symm,(plan.disjoint 92 93).symm] using hsrc)
      (by rw [hg 124 (by decide) (by decide)]; exact hambient)
      (by rw [hg 110 (by decide) (by decide)]; exact hdst)
      (by rw [hg 121 (by decide) (by decide)]; exact hcount)
      (by rw [hg 123 (by decide) (by decide)]; exact hvolume)
      (by simp [M])
      (by simp [M,plan.gather_injective.ne (by decide : (103 : Fin 126) ≠ 92)])
      (by
        intro k hk
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
        all_goals rw [hg _ (by decide) (by decide)]
        · exact hfresh _ (by simp)
        · exact hfresh _ (by simp)
        · exact hblank _ (by decide)
        · exact hfresh _ (by simp)
        · exact hblank _ (by decide)
        · exact hfresh _ (by simp)) depth
  have hpages (k : Fin 126) (hk : k = 92 ∨ k = 103) : F.R (plan.gather k) = M.R (plan.gather k) := by
    apply hframe₂
    · exact plan.disjoint k 93
    all_goals
      apply plan.gather_injective.ne
      rcases hk with rfl | rfl <;> decide
  have hc : F.R (plan.gather 92) = gatherControls A (windows.gaps w) := by rw [hpages 92 (Or.inl rfl)]; simp [M]
  have hwindow : F.R (plan.gather 103) = List.replicate (L*w) tick := by
    rw [hpages 103 (Or.inr rfl)]
    simp [M,plan.gather_injective.ne (by decide : (103 : Fin 126) ≠ 92)]
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) (plan.gather 92) v₂ F
  let N : Stacks T A := {F with R := Function.update F.R (plan.gather 92) []}
  obtain ⟨v₄,hu₄,he₄⟩ := uclear_exec (body := body) (plan.gather 103) v₃ N
  let G : Stacks T A := {N with R := Function.update N.R (plan.gather 103) []}
  have hlenN : (N.R (plan.gather 103)).length = L*w := by
    simp [N,hwindow,plan.gather_injective.ne (by decide : (103 : Fin 126) ≠ 92)]
  have hnclear : (2*(F.R (plan.gather 92)).length+2)+(2*(N.R (plan.gather 103)).length+2) ≤
      4*span*w+2*L*w+4 := by
    rw [hc,hlenN]
    have hh := windowPublicationControls_length_le (A := A) windows w hw1
    nlinarith only [hh]
  have heclear := Exec.seq he₃ he₄
  have hpush : mnNativePushBound 0 (.seq (uclear (plan.gather 92)) (uclear (plan.gather 103)) : Pr P T Q A U) := by
    simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]
  have hclear := mn_native_exec_within heclear 0 hpush depth (mnSize (mk v₂ F)+depth+0) (by simp)
  have hG (i : Fin T) (h92 : i ≠ plan.gather 92) (h103 : i ≠ plan.gather 103) : G.R i = F.R i := by
    simp [G,N,h92,h103]
  refine ⟨v₄,G,n₁+(n₂+((2*(F.R (plan.gather 92)).length+2)+(2*(N.R (plan.gather 103)).length+2))),replicas,ha,hinput,hvalid,hu₄.trans (hu₃.trans (hu₂.trans hu₁)),?_,?_,?_,?_,?_,?_,hi₂,ho₂,hl₂,?_⟩
  · exact Nat.add_le_add hn₁ (Nat.add_le_add hn₂ hnclear)
  · have he := mn_seq_within_add he₁ (mn_seq_within_add he₂ hclear)
    simpa only [preparedGatheredPublication,preparedGatheredPublicationWorkspace,Nat.add_zero] using he
  · rw [hG _ (plan.disjoint 92 93).symm (plan.disjoint 103 93).symm]; exact hs₂
  · rw [hG _ (plan.gather_injective.ne (by decide)) (plan.gather_injective.ne (by decide))]; exact hd₂
  · rw [hG _ (plan.gather_injective.ne (by decide)) (plan.gather_injective.ne (by decide))]; exact hout₂
  · rw [hG _ (plan.gather_injective.ne (by decide)) (plan.gather_injective.ne (by decide))]; exact hclock₂
  · intro i his hia hid hic
    by_cases h92 : i = plan.gather 92
    · subst i
      simp [G,N,plan.gather_injective.ne (by decide : (92 : Fin 126) ≠ 103),hfresh 92 (by simp)]
    by_cases h103 : i = plan.gather 103
    · subst i; simp [G,hfresh 103 (by simp)]
    rw [hG i h92 h103,hframe₂ i his hia hid hic]
    simp [M,h92,h103]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
