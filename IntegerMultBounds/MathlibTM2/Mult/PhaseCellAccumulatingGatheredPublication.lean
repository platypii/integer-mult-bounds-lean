module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGatheredPublicationPages
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedEncodedPublication
public import IntegerMultBounds.MathlibTM2.StackStockComposition

/-! One length class updates an independent accumulated output bank, preserving
the original packed RHS and every shared header for the following class. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A span L : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def accumulatingGatheredPublication (plan : ReplicaInteriorPlacement T) (dst : Fin T) : Pr P T Q A U :=
  .seq (prepareGatheredPublicationPages plan)
    (.seq (retainedEncodedPublication (plan.gather 121) (plan.gather 120) (plan.gather 92)
      (plan.gather 88) (plan.gather 89) (plan.gather 103) (plan.solver 93) dst (plan.gather 1)
      (plan.gather 125) (plan.gather 7) (plan.gather 123) (plan.gather 122))
      (.seq (uclear (plan.gather 92)) (uclear (plan.gather 103))))

def accumulatingGatheredPublicationCost (N V span L w B : ℕ) :=
  prepareReplicaPublicationPagesCost V span L w B+
    (retainedEncodedPublicationCost N (span*w)+(4*span*w+2*L*w+4))

def accumulatingGatheredPublicationWorkspace (Q A : ℕ) (U : Type) (N V span L w B : ℕ) :=
  mnProgPush (prepareReplicaPublicationPages (P := Empty) (Q := Q) (A := A) (U := U))*
    prepareReplicaPublicationPagesCost V span L w B+2*retainedEncodedPublicationCost N (span*w)

theorem accumulatingGatheredPublication_exec_within (plan : ReplicaInteriorPlacement T) (dst : Fin T)
    (hgd : ∀ i, plan.gather i ≠ dst) (hsd : ∀ i, plan.solver i ≠ dst)
    (V w : ℕ) (windows : PublicationWindows span L) (hw1 : 1 ≤ w)
    (hwV : w < 2^V) (hspanV : span < 2^V) (hunits : span*w < 2^V)
    {q e : ℕ} (xs : BoundedEncodedStream A w q e) (ambientRows : List (List (Fin (A+4))))
    (hambient : ∀ row ∈ ambientRows, row.length = span*w)
    (hlen : xs.val.length = ambientRows.length*(windows.origins.length*L)*w)
    (sourceTail outputTail suffix : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R (plan.solver 93) = xs.val++sourceTail) (hdst : S.R dst = ambientRows.flatten++outputTail)
    (hcount : (S.R (plan.gather 121)).length = ambientRows.length)
    (hvolume : (S.R (plan.gather 123)).length = span*w)
    (hV : (S.R (plan.gather 115)).length = V) (hw : (S.R (plan.gather 94)).length = w)
    (hL : (S.R (plan.gather 102)).length = L)
    (hpackets : S.R (plan.gather 109) = windows.origins.flatMap (binSyms V)++suffix)
    (hB : S.R (plan.gather 116) = List.replicate windows.origins.length tick)
    (hblank : ∀ k : Fin 126, k.val < 19 → S.R (plan.gather k) = [])
    (hfresh : ∀ k ∈ [(88 : Fin 126),89,90,91,92,103,104,105,106,107,120,122,125], S.R (plan.gather k) = []) (depth : ℕ) :
    ∃ v' F n, ∃ replicas : List (PublicationReplica A),
      replicas.map PublicationReplica.ambient = ambientRows ∧
      replicas.flatMap (PublicationReplica.input w) = xs.val ∧ (∀ r ∈ replicas, r.Valid windows w 0) ∧
      v'.user = v.user ∧ n ≤ accumulatingGatheredPublicationCost ambientRows.length V span L w windows.origins.length ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        accumulatingGatheredPublicationWorkspace Q A U ambientRows.length V span L w windows.origins.length) depth
        (accumulatingGatheredPublication plan dst) (mk v S) n (mk v' F) ∧
      F.R (plan.solver 93) = sourceTail ∧ F.R dst = replicas.flatMap (PublicationReplica.output windows w)++outputTail ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      ∀ i, i ≠ plan.solver 93 → i ≠ dst → F.R i = S.R i := by
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
  let regs : List (Fin 126 ⊕ Fin 121) :=
    [.inl 121,.inl 120,.inl 92,.inl 88,.inl 89,.inl 103,.inr 93,.inl 1,.inl 125,.inl 7,.inl 123,.inl 122]
  have hbase := List.Nodup.map plan.bank_injective (show regs.Nodup by decide)
  have hreg : [dst,plan.gather 121,plan.gather 120,plan.gather 92,plan.gather 88,plan.gather 89,
      plan.gather 103,plan.solver 93,plan.gather 1,plan.gather 125,plan.gather 7,plan.gather 123,plan.gather 122].Nodup := by
    apply List.nodup_cons.mpr
    constructor
    · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
      exact ⟨(hgd 121).symm,(hgd 120).symm,(hgd 92).symm,(hgd 88).symm,(hgd 89).symm,
        (hgd 103).symm,(hsd 93).symm,(hgd 1).symm,(hgd 125).symm,(hgd 7).symm,(hgd 123).symm,(hgd 122).symm⟩
    · simpa only [regs,List.map_cons,List.map_nil,ReplicaInteriorPlacement.bank,Sum.elim_inl,Sum.elim_inr] using hbase
  have hr := hreg
  regs_ne hr
  obtain ⟨v₂,F,n₂,replicas,ha,hinput,hvalid,hu₂,hn₂,he₂,hs₂,hd₂,hi₂,ho₂,hl₂,hframe₂,hpreserve⟩ :=
    retainedEncodedPublication_exec_within (body := body)
      (plan.gather 121) (plan.gather 120) (plan.gather 92) (plan.gather 88) (plan.gather 89)
      (plan.gather 103) (plan.solver 93) dst (plan.gather 1) (plan.gather 125) (plan.gather 7)
      (plan.gather 123) (plan.gather 122) (by regs_nodup) windows hw1 xs ambientRows hambient hlen
      sourceTail outputTail v₁ M
      (by simpa [M,(plan.disjoint 103 93).symm,(plan.disjoint 92 93).symm] using hsrc)
      (by simpa [M,(hgd 103).symm,(hgd 92).symm] using hdst)
      (by rw [hg 121 (by decide) (by decide)]; exact hcount)
      (by rw [hg 123 (by decide) (by decide)]; exact hvolume)
      (by simp [M]) (by simp [M,plan.gather_injective.ne (by decide : (103 : Fin 126) ≠ 92)])
      (by
        intro k hk
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals rw [hg _ (by decide) (by decide)]
        · exact hfresh _ (by simp)
        · exact hfresh _ (by simp)
        · exact hfresh _ (by simp)
        · exact hblank _ (by decide)
        · exact hfresh _ (by simp)
        · exact hblank _ (by decide)
        · exact hfresh _ (by simp)) depth
  have hpages (k : Fin 126) : F.R (plan.gather k) = M.R (plan.gather k) :=
    hframe₂ _ (plan.disjoint k 93) (hgd k)
  have hc : F.R (plan.gather 92) = gatherControls A (windows.gaps w) := by rw [hpages]; simp [M]
  have hwindow : F.R (plan.gather 103) = List.replicate (L*w) tick := by
    rw [hpages]
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
  have hG (i : Fin T) (h92 : i ≠ plan.gather 92) (h103 : i ≠ plan.gather 103) : G.R i = F.R i := by simp [G,N,h92,h103]
  refine ⟨v₄,G,n₁+(n₂+((2*(F.R (plan.gather 92)).length+2)+(2*(N.R (plan.gather 103)).length+2))),
    replicas,ha,hinput,hvalid,hu₄.trans (hu₃.trans (hu₂.trans hu₁)),Nat.add_le_add hn₁ (Nat.add_le_add hn₂ hnclear),?_,?_,?_,hi₂,ho₂,hl₂,?_⟩
  · simpa only [accumulatingGatheredPublication,accumulatingGatheredPublicationWorkspace,Nat.add_zero] using
      mn_seq_within_add he₁ (mn_seq_within_add he₂ hclear)
  · rw [hG _ (plan.disjoint 92 93).symm (plan.disjoint 103 93).symm]; exact hs₂
  · rw [hG _ (hgd 92).symm (hgd 103).symm]; exact hd₂
  · intro i his hid
    by_cases h92 : i = plan.gather 92
    · subst i; simp [G,N,plan.gather_injective.ne (by decide : (92 : Fin 126) ≠ 103),hfresh 92 (by simp)]
    by_cases h103 : i = plan.gather 103
    · subst i; simp [G,hfresh 103 (by simp)]
    rw [hG i h92 h103,hframe₂ i his hid]
    simp [M,h92,h103]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
