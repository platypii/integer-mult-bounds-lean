module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRepeatPrefix
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps
public import IntegerMultBounds.MathlibTM2.StackResources

/-! Copy one retained key's origin page once for factory setup and once per RHS.
No coordinate decoding occurs in the repeated work; all masters are restored. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def reloadReplicaOriginPackets (replicas cells width count batchSaved src dst saved tmp : Fin T) : Pr P T Q A U :=
  .seq (unaryProduct cells width count saved tmp)
    (.seq (repeatPrefix replicas batchSaved count src dst saved tmp)
      (.seq (copyPrefix count src dst saved tmp) (uclear count)))

def reloadReplicaOriginPacketsCost (N B V : ℕ) := N*(10*(B*V)+15)+16*(B*V)+9*B+20

theorem reloadReplicaOriginPackets_exec
    (replicas cells width count batchSaved src dst saved tmp : Fin T)
    (hreg : [replicas,cells,width,count,batchSaved,src,dst,saved,tmp].Nodup)
    (N B V : ℕ) (page suffix : List (Fin (A+4))) (hlen : page.length = B*V)
    (v : HS T Q A U) (S : Stacks T A)
    (hN : (S.R replicas).length = N) (hB : (S.R cells).length = B) (hV : (S.R width).length = V)
    (hsrc : S.R src = page++suffix) (hclean : ∀ k ∈ [count,batchSaved,saved,tmp], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ reloadReplicaOriginPacketsCost N B V ∧
      Exec body (reloadReplicaOriginPackets replicas cells width count batchSaved src dst saved tmp) (mk v S) m
        (mk v' {S with R := Function.update S.R dst (page++((List.replicate N page).flatten++S.R dst))}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := unaryProduct_exec (body := body)
    (a := cells) (b := width) (dst := count) (t₁ := saved) (t₂ := tmp) (by regs_nodup)
    v S (hclean _ (by simp)) (hclean _ (by simp))
  let M : Stacks T A := {S with R := Function.update S.R count (List.replicate (B*V) tick)}
  have he₁' : Exec body (unaryProduct cells width count saved tmp) (mk v S) m₁ (mk v₁ M) := by
    simpa only [hB,hV,hclean count (by simp),List.append_nil] using he₁
  have hM (k : Fin T) (hk : k ≠ count) : M.R k = S.R k := by simp [M,hk]
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := repeatPrefix_exec (body := body)
    (batch := replicas) (batchSaved := batchSaved) (count := count) (src := src) (dst := dst) (saved := saved) (tmp := tmp)
    (by regs_nodup) N page suffix v₁ M
    (by rw [hM _ ‹replicas ≠ count›]; exact hN) (by simp [M,hlen])
    (by rw [hM _ ‹count ≠ src›.symm]; exact hsrc)
    (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl
      all_goals rw [hM _ (by first | assumption | (apply Ne.symm; assumption))]; exact hclean _ (by simp))
  let K : Stacks T A := {M with R := Function.update M.R dst ((List.replicate N page).flatten++M.R dst)}
  obtain ⟨v₃,hu₃,he₃⟩ := copyPrefix_exec (body := body)
    (count := count) (src := src) (dst := dst) (saved := saved) (tmp := tmp) (by regs_nodup) v₂ K page suffix
    (by simpa [K,M,‹src ≠ dst›,‹count ≠ src›.symm] using hsrc)
    (by simp [K,M,‹count ≠ dst›,hlen])
    (by simpa [K,M,‹dst ≠ saved›.symm,‹count ≠ saved›.symm] using hclean saved (by simp))
    (by simpa [K,M,‹dst ≠ tmp›.symm,‹count ≠ tmp›.symm] using hclean tmp (by simp))
  let J : Stacks T A := {K with R := Function.update K.R dst (page++K.R dst)}
  obtain ⟨v₄,hu₄,he₄⟩ := uclear_exec (body := body) count v₃ J
  have hcount : (J.R count).length = B*V := by simp [J,K,M,‹count ≠ dst›]
  refine ⟨v₄,m₁+(m₂+((10*page.length+10)+(2*(J.R count).length+2))),
    hu₄.trans (hu₃.trans (hu₂.trans hu₁)),?_,?_⟩
  · rw [hB,hV] at hm₁
    rw [hlen] at hm₂
    rw [hlen,hcount]
    unfold reloadReplicaOriginPacketsCost
    nlinarith only [hm₁,hm₂]
  · have hfinal : {J with R := Function.update J.R count []} =
        {S with R := Function.update S.R dst (page++((List.replicate N page).flatten++S.R dst))} := by
      ext1
      · rfl
      · rfl
      · rfl
      · funext k
        by_cases hd : k = dst
        · subst k; simp [J,K,M,‹count ≠ dst›.symm]
        by_cases hc : k = count
        · subst k; simp [‹count ≠ dst›,hclean count (by simp)]
        simp [J,K,M,hd,hc]
    simpa only [reloadReplicaOriginPackets,hfinal] using Exec.seq he₁' (Exec.seq he₂ (Exec.seq he₃ he₄))

theorem reloadReplicaOriginPackets_native (replicas cells width count batchSaved src dst saved tmp : Fin T) :
    mnNativePushBound 2 (reloadReplicaOriginPackets (P := P) (Q := Q) (A := A) (U := U)
      replicas cells width count batchSaved src dst saved tmp) := by
  simp [reloadReplicaOriginPackets,repeatPrefix,copyPrefix,unaryProduct,scanP,ucopy,umulSym,
    transfer,copyR,copyStep,moveR,scanR,keepIn,transferAct,drainR,popDo,whileR,moveStep,peekR,pushN,popPush,
    uclear,mnNativePushBound,mnActPush]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
