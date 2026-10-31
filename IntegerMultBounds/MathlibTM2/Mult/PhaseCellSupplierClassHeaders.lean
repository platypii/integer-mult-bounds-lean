module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInstallMasterHeaderBank
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateCoreLength

/-! Prepare seven invariant supplier headers once per movement class. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

/-- Sources: radius, replicas, word width, precision, halo length, scalar width.
Destinations add halo symbol volume and core length to the copied headers. -/
def supplierClassCopies (source : Fin 6 → Fin T) (dst : Fin 7 → Fin T) : List (Fin T × Fin T) :=
  [(source 0,dst 0),(source 1,dst 1),(source 2,dst 2),(source 3,dst 3),(source 5,dst 5)]

def supplierClassValues (R : Regs T A) (source : Fin 6 → Fin T) : Fin 7 → ℕ :=
  ![(R (source 0)).length,(R (source 1)).length,(R (source 2)).length,(R (source 3)).length,
    (R (source 4)).length*(R (source 2)).length,(R (source 5)).length,
    (R (source 4)).length-2*(R (source 0)).length]

def supplierClassHeaders (source : Fin 6 → Fin T) (dst : Fin 7 → Fin T) (saved tmp : Fin T) : Pr P T Q A U :=
  .seq (copyUnaryHeaders tmp (supplierClassCopies source dst))
    (.seq (unaryProduct (source 4) (source 2) (dst 4) saved tmp)
      (generateCoreLength (source 4) (source 0) (dst 6) saved))

theorem supplierClassHeaders_native (source : Fin 6 → Fin T) (dst : Fin 7 → Fin T) (saved tmp : Fin T) :
    mnNativePushBound 2 (supplierClassHeaders (P := P) (Q := Q) (A := A) (U := U) source dst saved tmp) := by
  refine ⟨copyUnaryHeaders_native _ _,?_,generateCoreLength_native _ _ _ _⟩
  simp [unaryProduct,scanP,ucopy,umulSym,scanR,drainR,popDo,keepIn,pushN,popPush,
    moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]

def supplierClassHeadersCost (R : Regs T A) (source : Fin 6 → Fin T) (dst : Fin 7 → Fin T) : ℕ :=
  copyUnaryHeadersCost (fun k => (R k).length) (supplierClassCopies source dst)+
    ((R (source 4)).length*(4*(R (source 2)).length+9)+4)+
    (4*(R (source 4)).length+8*(R (source 0)).length+12)

theorem supplierClassHeaders_exec_within (source : Fin 6 → Fin T) (dst : Fin 7 → Fin T)
    (hdst : Function.Injective dst) (hsep : ∀ i j, source i ≠ dst j)
    (saved tmp : Fin T) (hsource : ∀ i, [source i,saved,tmp].Nodup)
    (hdstScratch : ∀ i, [dst i,saved,tmp].Nodup)
    (hproduct : source 4 ≠ source 2) (hmargin : source 4 ≠ source 0)
    (v : HS T Q A U) (S : Stacks T A) (hblank : ∀ i, S.R (dst i) = [])
    (hsaved : S.R saved = []) (htmp : S.R tmp = []) (depth : ℕ) :
    ∃ v' F n, v'.user = v.user ∧ n ≤ supplierClassHeadersCost S.R source dst ∧
      ExecWithin body (fun d state => mnSize state+d ≤ mnSize (Host.mk v S)+depth+
        2*supplierClassHeadersCost S.R source dst) depth
        (supplierClassHeaders source dst saved tmp) (Host.mk v S) n (Host.mk v' F) ∧
      (∀ i, F.R (dst i) = List.replicate (supplierClassValues S.R source i) tick) ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      ∀ k, (∀ i, k ≠ dst i) → F.R k = S.R k := by
  have hregs : ∀ p ∈ supplierClassCopies source dst, [p.1,p.2,tmp].Nodup := by
    intro p hp
    simp only [supplierClassCopies,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [List.nodup_cons,List.mem_cons]
  have hcopiesSep : ∀ p ∈ supplierClassCopies source dst, ∀ q ∈ supplierClassCopies source dst, p.2 ≠ q.1 := by
    intro p hp q hq
    simp only [supplierClassCopies,List.mem_cons,List.not_mem_nil,or_false] at hp hq
    rcases hp with rfl | rfl | rfl | rfl | rfl <;>
      rcases hq with rfl | rfl | rfl | rfl | rfl <;> exact (hsep _ _).symm
  obtain ⟨v₁,hu₁,he₁⟩ := copyUnaryHeaders_exec (body := body) tmp (supplierClassCopies source dst)
    hregs hcopiesSep (fun k => (S.R k).length) v S (by intros; rfl) htmp
  let M : Stacks T A := {S with R := unaryCopiesR (fun k => (S.R k).length) S.R (supplierClassCopies source dst)}
  have hMoff (k : Fin T) (hk : ∀ i, k ≠ dst i) : M.R k = S.R k := by
    apply unaryCopiesR_off
    intro p hp
    simp only [supplierClassCopies,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> exact (hk _).symm
  have hMsource (i : Fin 6) : M.R (source i) = S.R (source i) := hMoff _ (hsep i)
  have hMsaved : M.R saved = [] := (hMoff _ (fun i => by
    have h := hdstScratch i
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at h
    exact Ne.symm h.1.1)).trans hsaved
  have hMtmp : M.R tmp = [] := (hMoff _ (fun i => by
    have h := hdstScratch i
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at h
    exact Ne.symm h.1.2)).trans htmp
  have hMblank (i : Fin 7) (hi : i ≠ 0 ∧ i ≠ 1 ∧ i ≠ 2 ∧ i ≠ 3 ∧ i ≠ 5) : M.R (dst i) = [] := by
    rw [show M.R (dst i) = S.R (dst i) from unaryCopiesR_off _ _ _ _ (by
      intro p hp
      simp only [supplierClassCopies,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl <;> exact hdst.ne (by tauto))]
    exact hblank i
  have hprodRegs : [source 4,source 2,dst 4,saved,tmp].Nodup := by
    have h₁ := hsource 4; have h₂ := hsource 2; have h₃ := hdstScratch 4
    simp_all [List.nodup_cons,List.mem_cons]
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := unaryProduct_exec (body := body) hprodRegs v₁ M hMsaved hMtmp
  let N : Stacks T A := {M with R := (Function.update M.R (dst 4)
    (List.replicate ((S.R (source 4)).length*(S.R (source 2)).length) tick))}
  have he₂' : Exec body (unaryProduct (source 4) (source 2) (dst 4) saved tmp) (Host.mk v₁ M) n₂ (Host.mk v₂ N) := by
    simpa only [hMsource,hMblank 4 (by decide),List.append_nil] using he₂
  have hn₂' : n₂ ≤ (S.R (source 4)).length*(4*(S.R (source 2)).length+9)+4 := by
    simpa only [hMsource] using hn₂
  have hcoreRegs : [source 4,source 0,dst 6,saved].Nodup := by
    have h₁ := hsource 4; have h₂ := hsource 0; have h₃ := hdstScratch 6
    simp_all [List.nodup_cons,List.mem_cons]
  obtain ⟨v₃,hu₃,he₃⟩ := generateCoreLength_exec (body := body) (source 4) (source 0) (dst 6) saved hcoreRegs v₂ N
    (by simp [N,hdst.ne (by decide : (6 : Fin 7) ≠ 4),hMblank 6 (by decide)])
    (by
      have h := hdstScratch 4
      regs_ne h
      simp [N,‹dst 4 ≠ saved›.symm,hMsaved])
  let F : Stacks T A := {N with R := (Function.update N.R (dst 6)
    (List.replicate ((S.R (source 4)).length-2*(S.R (source 0)).length) tick))}
  have he₃' : Exec body (generateCoreLength (source 4) (source 0) (dst 6) saved) (Host.mk v₂ N)
      (4*(S.R (source 4)).length+8*(S.R (source 0)).length+12) (Host.mk v₃ F) := by
    simpa only [N,Function.update_of_ne (hsep 4 4),Function.update_of_ne (hsep 0 4),hMsource] using he₃
  have hex := Exec.seq he₁ (Exec.seq he₂' he₃')
  have hn : copyUnaryHeadersCost (fun k => (S.R k).length) (supplierClassCopies source dst)+
      (n₂+(4*(S.R (source 4)).length+8*(S.R (source 0)).length+12)) ≤ supplierClassHeadersCost S.R source dst := by
    unfold supplierClassHeadersCost
    omega
  refine ⟨v₃,F,_,hu₃.trans (hu₂.trans hu₁),hn,
    mn_native_exec_within hex 2 (supplierClassHeaders_native _ _ _ _) depth _ (by omega),?_,rfl,rfl,rfl,?_⟩
  · have hnd : ((supplierClassCopies source dst).map Prod.snd).Nodup := by simp [supplierClassCopies,hdst.eq_iff]
    have hcopied (i : Fin 6) (j : Fin 7) (hmem : (source i,dst j) ∈ supplierClassCopies source dst) :
        M.R (dst j) = List.replicate (S.R (source i)).length tick := by
      simpa only [hblank,List.append_nil] using unaryCopiesR_at (fun k => (S.R k).length) S.R _ hnd _ hmem
    intro i
    fin_cases i
    · simpa [F,N,supplierClassValues,hdst.eq_iff] using hcopied 0 0 (by simp [supplierClassCopies])
    · simpa [F,N,supplierClassValues,hdst.eq_iff] using hcopied 1 1 (by simp [supplierClassCopies])
    · simpa [F,N,supplierClassValues,hdst.eq_iff] using hcopied 2 2 (by simp [supplierClassCopies])
    · simpa [F,N,supplierClassValues,hdst.eq_iff] using hcopied 3 3 (by simp [supplierClassCopies])
    · simp [F,N,supplierClassValues,hdst.eq_iff]
    · simpa [F,N,supplierClassValues,hdst.eq_iff] using hcopied 5 5 (by simp [supplierClassCopies])
    · simp [F,N,supplierClassValues]
  · intro k hk
    simp only [F,N,Function.update_of_ne (hk 6),Function.update_of_ne (hk 4)]
    exact hMoff k hk
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
