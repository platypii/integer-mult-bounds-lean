module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaCoreGatherStep
public import IntegerMultBounds.MathlibTM2.Node.ScanPStock

/-! A restoring runtime replica scan advances each ambient row once. Payloads
are prepended in reverse replica order; source and replica counter are restored. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def replicaCoreGatherLoop (e : Fin 168 → Fin T)
    (count source archive saved tmp replicas savedReplicas : Fin T) : Pr P T Q A U :=
  .seq (scanP replicas savedReplicas (replicaCoreGatherStep e count source archive saved tmp))
    (moveR archive source id)

def replicaCoreGatherLoopCost (V s width radius L w B : ℕ) : ℕ :=
  B*(replicaCoreGatherStepCost V s width radius L w+5)+4+2*(B*s*w)+2

theorem replicaCoreGatherLoop_exec_within (e : Fin 168 → Fin T) (he : Function.Injective e) (count source archive saved tmp replicas savedReplicas : Fin T)
    (hreg : [count,source,archive,saved,tmp,replicas,savedReplicas].Nodup)
    (hsep : ∀ k ∈ [count,source,archive,saved,tmp,replicas,savedReplicas], ∀ i, k ≠ e i)
    (borrowed : List (Fin (A+4))) {V s width radius L w : ℕ}
    (hwidth : 0 < width) (hwide : s+width+2*radius < 2^V) (hLfit : L < 2^V)
    (hwV : w < 2^V) (hvol : s*w < 2^V) (hA : 4 ≤ A) (hVpos : 0 < V)
    (hgroup : 0 < (coreGatherIndices s width radius L).length)
    (Fs : List (ZMod s → GaussianInt)) (v : HS T Q A U) (S : Stacks T A)
    (h163 : (S.R (e 163)).length = V) (h115 : S.R (e 115) = []) (h103 : S.R (e 103) = []) (h105 : S.R (e 105) = [])
    (hs : S.R (e 145) = binSyms V s) (hw : S.R (e 150) = binSyms V width)
    (hr : S.R (e 152) = binSyms V radius) (hL : S.R (e 165) = binSyms V L) (hz : S.R (e 154) = [])
    (hblank : ∀ k : Fin 168, k.val < 31 → S.R (e k) = [])
    (h104 : S.R (e 104) = []) (h106 : S.R (e 106) = []) (h116 : S.R (e 116) = [])
    (hsource : S.R source = Fs.flatMap (fun C => cstream A w (chirpLine s C))++borrowed)
    (harchive : S.R archive = [])
    (hreplicas : (S.R replicas).length = Fs.length) (hsavedReplicas : S.R savedReplicas = [])
    (hlocal : S.R (e 110) = [])
    (hcount : (S.R count).length = s*w) (hsaved : S.R saved = []) (htmp : S.R tmp = [])
    (hword : (S.R (e 94)).length = w) (hcontrol : S.R (e 91) = []) (horigin : S.R (e 109) = [])
    (hclean : ∀ k ∈ [(92 : Fin 168),93,95,96,97,98,99,100,101,102], S.R (e k) = [])
    (hfresh : ∀ k ∈ [(88 : Fin 168),89,90], S.R (e k) = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ replicaCoreGatherLoopCost V s width radius L w Fs.length ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        (Fs.length*(coreGatherIndices s width radius L).length*L*w+
          3*(replicaCoreGatherStepCost V s width radius L w+2))) depth (replicaCoreGatherLoop e count source archive saved tmp replicas savedReplicas)
        (Host.mk v S) n (Host.mk v' {S with R := (Function.update S.R (e 108)
          (cstream A w (coreGatherPayload width radius L Fs.reverse)++S.R (e 108)))}) := by
  have hr := hreg
  regs_ne hr
  have hoff (k : Fin T) (hk : k ∈ [count,source,archive,saved,tmp,replicas,savedReplicas]) (i : Fin 168) := hsep k hk i
  have h8 : [e 110,count,source,archive,saved,tmp,replicas,savedReplicas].Nodup :=
    List.nodup_cons.mpr ⟨fun h => (hsep _ h 110) rfl,hreg⟩
  have hr8 := h8
  regs_ne hr8
  let row := fun C : ZMod s → GaussianInt => cstream A w (chirpLine s C)
  let payload := fun C : ZMod s → GaussianInt => cstream A w (coreGatherPayload width radius L [C])
  let Ψ := fun j => Function.update (Function.update (Function.update S.R source
    ((Fs.drop j).flatMap row++borrowed)) archive ((Fs.take j).flatMap row).reverse)
      (e 108) ((Fs.take j).reverse.flatMap payload++S.R (e 108))
  have hstep : IterStockSpec body (replicaCoreGatherStep e count source archive saved tmp)
      replicas savedReplicas Ψ (replicaCoreGatherStepCost V s width radius L w) Fs.length := by
    intro j hj v₀ F hR
    have hbase (k : Fin T) (hkSource : k ≠ source) (hkArchive : k ≠ archive)
        (hkResult : k ≠ e 108) (hkReplicas : k ≠ replicas) (hkSaved : k ≠ savedReplicas) : F.R k = S.R k := by
      rw [hR k hkReplicas hkSaved]
      simp [Ψ,hkSource,hkArchive,hkResult]
    have hwork (k : Fin 168) (hk : k ≠ 108) : F.R (e k) = S.R (e k) :=
      hbase (e k) (hoff source (by simp) k).symm (hoff archive (by simp) k).symm
        (fun h => hk (he h)) (hoff replicas (by simp) k).symm (hoff savedReplicas (by simp) k).symm
    have hexternal (k : Fin T) (hk : k ∈ [count,saved,tmp]) : F.R k = S.R k := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl
      all_goals apply hbase <;> first | assumption | (apply Ne.symm; assumption) | (apply hoff; simp)
    have hsrc : F.R source = row Fs[j]++((Fs.drop (j+1)).flatMap row++borrowed) := by
      rw [hR source ‹source ≠ replicas› ‹source ≠ savedReplicas›]
      simp only [Ψ,Function.update_of_ne (hoff source (by simp) 108),
        Function.update_of_ne ‹source ≠ archive›,Function.update_self]
      rw [List.drop_eq_getElem_cons hj,List.flatMap_cons,List.append_assoc]
    have ha : F.R archive = ((Fs.take j).flatMap row).reverse := by
      rw [hR archive ‹archive ≠ replicas› ‹archive ≠ savedReplicas›]
      simp [Ψ,hoff archive (by simp) 108]
    have hout : F.R (e 108) = (Fs.take j).reverse.flatMap payload++S.R (e 108) := by
      rw [hR (e 108) (hoff replicas (by simp) 108).symm (hoff savedReplicas (by simp) 108).symm]
      simp [Ψ]
    obtain ⟨v₁,n,hu,hn,hex⟩ := replicaCoreGatherStep_exec (body := body) e he count source archive saved tmp
      (by regs_nodup) (hoff source (by simp)) (hoff archive (by simp))
      ((Fs.drop (j+1)).flatMap row++borrowed) hwidth hwide hLfit hwV hvol hA hVpos hgroup Fs[j] v₀ F
      (by simpa only [hwork 163 (by decide)] using h163)
      (by simpa only [hwork 115 (by decide)] using h115)
      (by simpa only [hwork 103 (by decide)] using h103)
      (by simpa only [hwork 105 (by decide)] using h105)
      (by simpa only [hwork 145 (by decide)] using hs)
      (by simpa only [hwork 150 (by decide)] using hw)
      (by simpa only [hwork 152 (by decide)] using hr)
      (by simpa only [hwork 165 (by decide)] using hL)
      (by simpa only [hwork 154 (by decide)] using hz)
      (by intro k hk; rw [hwork k (by intro h; subst k; norm_num at hk)]; exact hblank k hk)
      (by simpa only [hwork 104 (by decide)] using h104)
      (by simpa only [hwork 106 (by decide)] using h106)
      (by simpa only [hwork 116 (by decide)] using h116)
      hsrc (by simpa only [hwork 110 (by decide)] using hlocal)
      (by simpa only [hexternal count (by simp)] using hcount)
      (by simpa only [hexternal saved (by simp)] using hsaved)
      (by simpa only [hexternal tmp (by simp)] using htmp)
      (by simpa only [hwork 94 (by decide)] using hword)
      (by simpa only [hwork 91 (by decide)] using hcontrol)
      (by simpa only [hwork 109 (by decide)] using horigin)
      (by intro k hk; rw [hwork k (by intro h; subst k; simp at hk)]; exact hclean k hk)
      (by intro k hk; rw [hwork k (by intro h; subst k; simp at hk)]; exact hfresh k hk)
    let R := Function.update (Function.update (Function.update F.R source
      ((Fs.drop (j+1)).flatMap row++borrowed)) archive ((row Fs[j]).reverse++F.R archive))
        (e 108) (payload Fs[j]++F.R (e 108))
    refine ⟨v₁,R,n,hu,hn,hex,?_,?_,?_,?_⟩
    · simp [R,‹source ≠ replicas›.symm,‹archive ≠ replicas›.symm,hoff replicas (by simp) 108]
    · simp [R,‹source ≠ savedReplicas›.symm,‹archive ≠ savedReplicas›.symm,hoff savedReplicas (by simp) 108]
    · intro k hkReplicas hkSaved
      by_cases hkResult : k = e 108
      · subst k
        simp only [R,Ψ,Function.update_self]
        rw [hout,List.take_succ_eq_append_getElem hj]
        simp only [List.reverse_append,List.reverse_singleton,List.flatMap_append,List.flatMap_cons,
          List.flatMap_nil,List.append_nil,List.append_assoc]
      by_cases hkArchive : k = archive
      · subst k
        simp only [R,Ψ,Function.update_of_ne (hoff archive (by simp) 108),Function.update_self]
        rw [ha,List.take_succ_eq_append_getElem hj]
        simp only [List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.reverse_append]
      by_cases hkSource : k = source
      · subst k
        simp [R,Ψ,hoff source (by simp) 108,‹source ≠ archive›]
      simp only [R,Ψ,Function.update_of_ne hkResult,Function.update_of_ne hkArchive,Function.update_of_ne hkSource]
      exact hbase k hkSource hkArchive hkResult hkReplicas hkSaved
    · have hsize : mnSize (Host.mk v₁ {F with R := R}) = mnSize (Host.mk v₀ F)+
          (coreGatherIndices s width radius L).length*L*w :=
        replicaCoreGatherStep_boundary_size e source archive (by
          simp [List.nodup_cons,‹source ≠ archive›,hoff source (by simp) 108,hoff archive (by simp) 108])
          width radius L w Fs[j] v₀ v₁ F ((Fs.drop (j+1)).flatMap row++borrowed) hsrc
      rw [hsize]
      exact Nat.le_add_right _ _
  have hzero : Ψ 0 = S.R := by
    simp only [Ψ,List.take_zero,List.drop_zero,List.flatMap_nil,List.reverse_nil,List.nil_append]
    change Function.update (Function.update (Function.update S.R source
      (Fs.flatMap (fun C => cstream A w (chirpLine s C))++borrowed)) archive []) (e 108) (S.R (e 108)) = S.R
    rw [←hsource,←harchive]
    simp only [Function.update_eq_self]
  obtain ⟨v₁,R,n,hu,hn,hex,hrep,hsrep,hR⟩ := scanP_exec (body := body) ‹replicas ≠ savedReplicas› hstep.toIterSpec 0 v S
    (by simpa only [hreplicas,Nat.zero_add] using Nat.le_refl Fs.length)
    (by intro k _ _; rw [hzero])
  have hscan := scanP_within_final_stock ‹replicas ≠ savedReplicas› (by decide : 1 ≤ 3)
    (replicaCoreGatherStep_native e count source archive saved tmp) hstep 0 v S
    (by simpa only [hreplicas,Nat.zero_add] using Nat.le_refl Fs.length)
    (by intro k _ _; rw [hzero]) hex depth
  let F : Stacks T A := {S with R := R}
  have ha : F.R archive = (Fs.flatMap row).reverse := by
    change R archive = _
    rw [hR archive ‹archive ≠ replicas› ‹archive ≠ savedReplicas›]
    simp [Ψ,hreplicas,hoff archive (by simp) 108]
  have hs : F.R source = borrowed := by
    change R source = _
    rw [hR source ‹source ≠ replicas› ‹source ≠ savedReplicas›]
    simp [Ψ,hreplicas,hoff source (by simp) 108,‹source ≠ archive›]
  have hp : F.R (e 108) = Fs.reverse.flatMap payload++S.R (e 108) := by
    change R (e 108) = _
    rw [hR (e 108) (hoff replicas (by simp) 108).symm (hoff savedReplicas (by simp) 108).symm]
    simp [Ψ,hreplicas]
  have hflatLength : (Fs.flatMap row).length = Fs.length*s*w := by
    simp [row,List.length_flatMap]
    ring
  obtain ⟨v₂,hu₂,he₂⟩ := moveR_exec body archive source ‹source ≠ archive›.symm id v₁ F
  have hend : Host.mk v₂ {F with R := movedR F.R archive source id (F.R archive)} =
      Host.mk v₂ {S with R := (Function.update S.R (e 108)
        (cstream A w (coreGatherPayload width radius L Fs.reverse)++S.R (e 108)))} := by
    apply congrArg (Host.mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    change movedR R archive source id (F.R archive) k = _
    by_cases hkSource : k = source
    · subst k
      simp only [movedR,Function.update_self,List.map_id,ha,List.reverse_reverse,
        Function.update_of_ne (hoff source (by simp) 108)]
      rw [show R source = borrowed from hs]
      exact hsource.symm
    by_cases hkArchive : k = archive
    · subst k
      simp [movedR,‹source ≠ archive›.symm,harchive,hoff archive (by simp) 108]
    by_cases hkResult : k = e 108
    · subst k
      simp only [movedR,Function.update_of_ne (hoff source (by simp) 108).symm,
        Function.update_of_ne (hoff archive (by simp) 108).symm,Function.update_self]
      simpa [payload,coreGatherPayload,cstream,List.flatMap_assoc] using hp
    by_cases hkReplicas : k = replicas
    · subst k
      simp [movedR,‹source ≠ replicas›.symm,‹archive ≠ replicas›.symm,hrep,hsavedReplicas,hoff replicas (by simp) 108]
    by_cases hkSaved : k = savedReplicas
    · subst k
      simp [movedR,‹source ≠ savedReplicas›.symm,‹archive ≠ savedReplicas›.symm,hsrep,hsavedReplicas,
        hoff savedReplicas (by simp) 108]
    simp only [movedR,Function.update_of_ne hkSource,Function.update_of_ne hkArchive,Function.update_of_ne hkResult]
    rw [hR k hkReplicas hkSaved]
    simp [Ψ,hkSource,hkArchive,hkResult]
  have hmoveSize := mn_movedR_size source archive ‹source ≠ archive› v₁ v₂ F
  rw [hend] at hmoveSize
  rw [mn_appendR_size] at hmoveSize
  have hsize : mnSize (Host.mk v₁ F) = mnSize (Host.mk v S)+
      Fs.length*(coreGatherIndices s width radius L).length*L*w := by
    simpa only [length_cstream,coreGatherPayload_length,List.length_reverse] using hmoveSize.symm
  let budget := mnSize (Host.mk v S)+depth+
    (Fs.length*(coreGatherIndices s width radius L).length*L*w+
      3*(replicaCoreGatherStepCost V s width radius L w+2))
  have hwscan : ExecWithin body (fun d z => mnSize z+d ≤ budget) depth
      (scanP replicas savedReplicas (replicaCoreGatherStep e count source archive saved tmp))
      (Host.mk v S) n (Host.mk v₁ F) := hscan.mono (by
    intro d z hz
    change mnSize z+d ≤ mnSize (Host.mk v₁ F)+depth+3*(replicaCoreGatherStepCost V s width radius L w+2) at hz
    rw [hsize] at hz
    dsimp only [budget]
    omega)
  have hmove := Host.moveR_within archive source id he₂ depth budget (by
    rw [hsize]
    dsimp only [budget]
    omega)
  refine ⟨v₂,n+(2*(F.R archive).length+2),hu₂.trans hu,?_,
    hend ▸ (ExecWithin.seq hwscan hmove)⟩
  simp only [hreplicas,hsavedReplicas,List.length_nil,Finset.sum_const,Finset.card_range,
    Nat.add_zero,Nat.mul_zero,nsmul_eq_mul,Nat.cast_id] at hn
  rw [ha,List.length_reverse,hflatLength]
  dsimp only [replicaCoreGatherLoopCost]
  nlinarith only [hn]

theorem replicaCoreGatherLoop_exec (e : Fin 168 → Fin T) (he : Function.Injective e) (count source archive saved tmp replicas savedReplicas : Fin T)
    (hreg : [count,source,archive,saved,tmp,replicas,savedReplicas].Nodup)
    (hsep : ∀ k ∈ [count,source,archive,saved,tmp,replicas,savedReplicas], ∀ i, k ≠ e i)
    (borrowed : List (Fin (A+4))) {V s width radius L w : ℕ}
    (hwidth : 0 < width) (hwide : s+width+2*radius < 2^V) (hLfit : L < 2^V)
    (hwV : w < 2^V) (hvol : s*w < 2^V) (hA : 4 ≤ A) (hVpos : 0 < V)
    (hgroup : 0 < (coreGatherIndices s width radius L).length)
    (Fs : List (ZMod s → GaussianInt)) (v : HS T Q A U) (S : Stacks T A)
    (h163 : (S.R (e 163)).length = V) (h115 : S.R (e 115) = []) (h103 : S.R (e 103) = []) (h105 : S.R (e 105) = [])
    (hs : S.R (e 145) = binSyms V s) (hw : S.R (e 150) = binSyms V width)
    (hr : S.R (e 152) = binSyms V radius) (hL : S.R (e 165) = binSyms V L) (hz : S.R (e 154) = [])
    (hblank : ∀ k : Fin 168, k.val < 31 → S.R (e k) = [])
    (h104 : S.R (e 104) = []) (h106 : S.R (e 106) = []) (h116 : S.R (e 116) = [])
    (hsource : S.R source = Fs.flatMap (fun C => cstream A w (chirpLine s C))++borrowed)
    (harchive : S.R archive = [])
    (hreplicas : (S.R replicas).length = Fs.length) (hsavedReplicas : S.R savedReplicas = [])
    (hlocal : S.R (e 110) = [])
    (hcount : (S.R count).length = s*w) (hsaved : S.R saved = []) (htmp : S.R tmp = [])
    (hword : (S.R (e 94)).length = w) (hcontrol : S.R (e 91) = []) (horigin : S.R (e 109) = [])
    (hclean : ∀ k ∈ [(92 : Fin 168),93,95,96,97,98,99,100,101,102], S.R (e k) = [])
    (hfresh : ∀ k ∈ [(88 : Fin 168),89,90], S.R (e k) = [])  :
    ∃ v' n, v'.user = v.user ∧ n ≤ replicaCoreGatherLoopCost V s width radius L w Fs.length ∧
      Exec body (replicaCoreGatherLoop e count source archive saved tmp replicas savedReplicas)
        (Host.mk v S) n (Host.mk v' {S with R := (Function.update S.R (e 108)
          (cstream A w (coreGatherPayload width radius L Fs.reverse)++S.R (e 108)))}) := by
  obtain ⟨v',n,hu,hn,he⟩ := replicaCoreGatherLoop_exec_within (body := body) e he count source archive saved tmp
    replicas savedReplicas hreg hsep borrowed hwidth hwide hLfit hwV hvol hA hVpos hgroup Fs v S
    h163 h115 h103 h105 hs hw hr hL hz hblank h104 h106 h116 hsource harchive hreplicas hsavedReplicas
    hlocal hcount hsaved htmp hword hcontrol horigin hclean hfresh 0
  exact ⟨v',n,hu,hn,he.toExec⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
