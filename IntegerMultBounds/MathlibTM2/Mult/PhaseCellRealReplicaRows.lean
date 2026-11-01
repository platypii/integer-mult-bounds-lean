module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedReplicaFields
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRealPrefix
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps
public import IntegerMultBounds.MathlibTM2.StackResources

/-! Project a counted rectangular output prefix to its real component. Runtime
headers generate the count; all headers, scratch and borrowed suffixes survive. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def realReplicaRows (rows volume src count saved tmp : Fin T) : Pr P T Q A U :=
  .seq (unaryProduct rows volume count saved tmp)
    (.seq (realPrefix count src saved tmp) (uclear count))

def realReplicaRowsCost (N V : ℕ) := N*(12*V+9)+12

theorem realReplicaRows_exec_within (rows volume src count saved tmp : Fin T)
    (hreg : [rows,volume,src,count,saved,tmp].Nodup) (N V : ℕ)
    (v : HS T Q A U) (S : Stacks T A) (xs tail : List (Fin (A+4)))
    (hrows : (S.R rows).length = N) (hvolume : (S.R volume).length = V)
    (hsrc : S.R src = xs++tail) (hxs : xs.length = N*V)
    (hfresh : ∀ k ∈ [count,saved,tmp], S.R k = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ realReplicaRowsCost N V ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+2*realReplicaRowsCost N V) depth
        (realReplicaRows rows volume src count saved tmp) (mk v S) n
        (mk v' {S with R := Function.update S.R src (xs.map realPartSymbol++tail)}) := by
  have hr := hreg
  regs_ne hr
  have hp : [rows,volume,count,saved,tmp].Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_false_eq_true,not_or] at hreg ⊢
    tauto
  have hreal : [count,src,saved,tmp].Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_false_eq_true,not_or] at hreg ⊢
    tauto
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := unaryProduct_exec (body := body) hp v S
    (hfresh saved (by simp)) (hfresh tmp (by simp))
  let M : Stacks T A := {S with R := Function.update S.R count (List.replicate (N*V) tick)}
  have he₁' : Exec body (unaryProduct rows volume count saved tmp) (mk v S) n₁ (mk v₁ M) := by
    simpa only [hrows,hvolume,hfresh count (by simp),List.append_nil] using he₁
  have hn₁' : n₁ ≤ N*(4*V+9)+4 := by simpa only [hrows,hvolume] using hn₁
  obtain ⟨v₂,hu₂,he₂⟩ := realPrefix_exec (body := body) hreal v₁ M xs tail
    (by simpa [M,‹src ≠ count›] using hsrc) (by simp [M,hxs])
    (by simpa [M,‹count ≠ saved›.symm] using hfresh saved (by simp))
    (by simpa [M,‹count ≠ tmp›.symm] using hfresh tmp (by simp))
  let G : Stacks T A := {M with R := Function.update M.R src (xs.map realPartSymbol++tail)}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) count v₂ G
  have hc : (G.R count).length = N*V := by simp [G,M,‹src ≠ count›.symm]
  have hrestore : {G with R := Function.update G.R count []} =
      {S with R := Function.update S.R src (xs.map realPartSymbol++tail)} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk : k = count
    · subst k; simp [‹src ≠ count›.symm,hfresh count (by simp)]
    · simp [G,M,Function.update_apply,hk]
  rw [hc,hrestore] at he₃
  have he : Exec body (realReplicaRows rows volume src count saved tmp) (mk v S)
      (n₁+((6*(N*V)+6)+(2*(N*V)+2)))
      (mk v₃ {S with R := Function.update S.R src (xs.map realPartSymbol++tail)}) := by
    simpa only [hxs,realReplicaRows] using Exec.seq he₁' (Exec.seq he₂ he₃)
  have hn : n₁+((6*(N*V)+6)+(2*(N*V)+2)) ≤ realReplicaRowsCost N V := by
    unfold realReplicaRowsCost
    nlinarith only [hn₁']
  refine ⟨v₃,_,hu₃.trans (hu₂.trans hu₁),hn,mn_native_exec_within he 2 ?_ depth _
    (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hn) _)⟩
  simp [realReplicaRows,unaryProduct,realPrefix,transfer,transferAct,ucopy,umulSym,
    scanP,scanR,drainR,popDo,popPush,keepIn,pushN,moveR,moveStep,whileR,peekR,
    uclear,mnNativePushBound,mnActPush]

theorem packedReplicaFields_real {s : ℕ} (hA : 4 ≤ A) (a span w : ℕ)
    (fields : List (ZMod s → GaussianInt)) :
    ((fields.map (fun D => cstream A w (packedInterval a span D))).flatten).map realPartSymbol =
      (fields.map (fun D => cstream A w (packedInterval a span (fun i => realPartWord (D i))))).flatten := by
  rw [List.map_flatten,List.map_map]
  congr 1
  apply List.map_congr_left
  intro D hD
  dsimp only [Function.comp_apply]
  rw [realPartSymbol_cstream hA]
  congr 1
  simp [packedInterval,chirpLine,List.map_take,List.map_drop,List.map_map,Function.comp_def]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
