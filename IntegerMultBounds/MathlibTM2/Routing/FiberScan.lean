module

public import IntegerMultBounds.MathlibTM2.Routing.SmallFieldMove

/-! Scan complete prefix fibers with one fixed body and one private archive.
The structural composition theorem is shared by forward and inverse field moves. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.FiberScan
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A : ℕ} {P U α : Type} {body : P → Pr P T Q A U}

/-- A fiber body consumes its source prefix and prepends the reversed result to
an archive. Concatenation restores the order of fibers and their contents. -/
def scanFibers (clock src archive : Fin T) (p : Pr P T Q A U) : Pr P T Q A U :=
  .seq (countedLoop clock p) (moveR archive src id)

theorem scanFibers_exec (clock src archive : Fin T) (hreg : [clock,src,archive].Nodup)
    (p : Pr P T Q A U) (fibers : List α) (input output : α → List (Fin (A+4))) (c : ℕ)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hstep : ∀ x ∈ fibers, ∀ (vi : HS T Q A U) (F : Stacks T A) rest,
      (∀ i, i ≠ src → i ≠ archive → i ≠ clock → F.R i = S.R i) →
      F.R src = input x++rest →
      ∃ v' n, v'.user = vi.user ∧ n ≤ c ∧ Exec body p (mk vi F) n
        (mk v' {F with R := (Function.update (Function.update F.R src rest)
          archive ((output x).reverse++F.R archive))}))
    (hclock : (S.R clock).length = fibers.length)
    (hsrc : S.R src = fibers.flatMap input++tail) (harchive : S.R archive = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ fibers.length*(c+3)+2*(fibers.flatMap output).length+4 ∧
      Exec body (scanFibers clock src archive p) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R src
          (fibers.flatMap output++tail)) clock [])}) := by
  have hr := hreg
  regs_ne hr
  let Inv := fun j (F : Stacks T A) => ∃ done todo : List α,
    fibers = done++todo ∧ done.length = j ∧ F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
    (∀ i, i ≠ src → i ≠ archive → i ≠ clock → F.R i = S.R i) ∧
    F.R src = todo.flatMap input++tail ∧
    F.R archive = (done.flatMap output).reverse
  obtain ⟨v₁,F,n,hu₁,hn,he,hc,hI⟩ := countedLoop_exec (body := body) clock p fibers.length c Inv
    (by
      intro j F xs hI
      obtain ⟨done,todo,hd,hj,hi,ho,hl,hframe,hs,ha⟩ := hI
      refine ⟨done,todo,hd,hj,hi,ho,hl,?_,?_,?_⟩
      · intro i his hia hic
        simpa only [Function.update_of_ne hic] using hframe i his hia hic
      · simpa only [Function.update_of_ne ‹clock ≠ src›.symm] using hs
      · simpa only [Function.update_of_ne ‹clock ≠ archive›.symm] using ha)
    (by
      intro j hj vi F hI
      obtain ⟨done,todo,hd,hj',hi,ho,hl,hframe,hs,ha⟩ := hI
      cases todo with
      | nil => simp only [List.append_nil] at hd; subst fibers; omega
      | cons x todo =>
        have hx : x ∈ fibers := by rw [hd]; simp
        obtain ⟨v',m,hu,hm,hex⟩ := hstep x hx vi F (todo.flatMap input++tail) hframe
          (by simpa only [List.flatMap_cons,List.append_assoc] using hs)
        let F' : Stacks T A := {F with R := (Function.update (Function.update F.R src
          (todo.flatMap input++tail)) archive ((output x).reverse++F.R archive))}
        refine ⟨v',F',m,hu,hm,hex,?_,done++[x],todo,?_,?_,hi,ho,hl,?_,?_,?_⟩
        · simp [F',‹clock ≠ src›,‹clock ≠ archive›]
        · simpa only [List.append_assoc,List.singleton_append] using hd
        · simp [hj']
        · intro i his hia hic
          simpa only [F',Function.update_of_ne his,Function.update_of_ne hia] using hframe i his hia hic
        · simp [F',‹src ≠ archive›]
        · simp [F',ha,List.flatMap_append,List.reverse_append])
    v S hclock ⟨[],fibers,rfl,rfl,rfl,rfl,rfl,(by intros; rfl),hsrc,by simpa using harchive⟩
  obtain ⟨done,todo,hd,hj,hi,ho,hl,hframe,hs,ha⟩ := hI
  have ht : todo = [] := by
    have hh := congrArg List.length hd
    simp only [List.length_append] at hh
    exact List.eq_nil_of_length_eq_zero (by omega)
  subst todo
  simp only [List.append_nil] at hd
  subst done
  simp only [List.flatMap_nil,List.nil_append] at hs
  obtain ⟨v₂,hu₂,he₂⟩ := moveR_exec body archive src ‹src ≠ archive›.symm id v₁ F
  refine ⟨v₂,n+(2*(F.R archive).length+2),hu₂.trans hu₁,?_,(Exec.seq he he₂).cast rfl ?_⟩
  · rw [ha,List.length_reverse]; omega
  · apply congrArg (mk v₂)
    refine Stacks.ext hi ho hl ?_
    funext i
    by_cases his : i = src
    · subst i; simp [movedR,ha,hs,‹clock ≠ src›.symm]
    by_cases hia : i = archive
    · subst i; simp [movedR,‹src ≠ archive›.symm,‹clock ≠ archive›.symm,harchive]
    by_cases hic : i = clock
    · subst i; simp [movedR,‹clock ≠ src›,‹clock ≠ archive›,hc]
    · simp [movedR,his,hia,hic,hframe i his hia hic]

open SmallFieldMove

def splitPlanes {β : Type} (rows : List (List β × List β)) : List β :=
  rows.flatMap Prod.fst++rows.flatMap Prod.snd

theorem splitPlanes_length {β : Type} (rows : List (List β × List β)) :
    (splitPlanes rows).length = (pairStream rows).length := by
  simp only [splitPlanes,List.length_append,pairStream_length]

/-- Split the current complete fiber, then advance past it into the output
archive. Both passes have a bounded extent supplied by retained headers. -/
def splitFiber (count clock volume fiberVolume src archive zeroBank oneBank tmp : Fin T) : Pr P T Q A U :=
  .seq (retainedSplitBlockPairs count clock volume src zeroBank oneBank tmp)
    (transfer fiberVolume src archive tmp)

theorem splitFiber_exec (count clock volume fiberVolume src archive zeroBank oneBank tmp : Fin T)
    (hreg : [count,clock,volume,fiberVolume,src,archive,zeroBank,oneBank,tmp].Nodup)
    (rows : List (List (Fin (A+4)) × List (Fin (A+4)))) (R : ℕ)
    (hlen : ∀ r ∈ rows, r.1.length = R ∧ r.2.length = R)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hcount : (S.R count).length = rows.length) (hvolume : (S.R volume).length = R)
    (hfiber : (S.R fiberVolume).length = 2*(rows.length*R))
    (hsrc : S.R src = pairStream rows++tail)
    (hclock : S.R clock = []) (hzero : S.R zeroBank = [])
    (hone : S.R oneBank = []) (htmp : S.R tmp = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ rows.length*(20*R+15)+14 ∧
      Exec body (splitFiber count clock volume fiberVolume src archive zeroBank oneBank tmp) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R src tail)
          archive ((splitPlanes rows).reverse++S.R archive))}) := by
  have hr := hreg
  regs_ne hr
  have hzlen : (rows.flatMap Prod.fst).length = rows.length*R := by
    rw [List.length_flatMap,List.map_eq_replicate_iff.mpr (by intro r hr; exact (hlen r hr).1),
      List.sum_replicate,smul_eq_mul]
  have holen : (rows.flatMap Prod.snd).length = rows.length*R := by
    rw [List.length_flatMap,List.map_eq_replicate_iff.mpr (by intro r hr; exact (hlen r hr).2),
      List.sum_replicate,smul_eq_mul]
  have hlenPlanes : (splitPlanes rows).length = 2*(rows.length*R) := by
    simp only [splitPlanes,List.length_append,hzlen,holen]; omega
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := retainedSplitBlockPairs_exec (body := body)
    count clock volume src zeroBank oneBank tmp (by regs_nodup) rows R hlen tail v S
    hcount hvolume hsrc hclock hzero hone htmp
  let M : Stacks T A := {S with R := Function.update S.R src (splitPlanes rows++tail)}
  have he₁' : Exec body (retainedSplitBlockPairs count clock volume src zeroBank oneBank tmp)
      (mk v S) n₁ (mk v₁ M) := by
    simpa only [M,splitPlanes,List.append_assoc] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := transfer_exec (body := body) (count := fiberVolume) (src := src)
    (dst := archive) (tmp := tmp) (by regs_nodup) v₁ M (splitPlanes rows) tail
    (by simp [M]) (by simp [M,‹fiberVolume ≠ src›,hfiber,hlenPlanes])
    (by simp [M,‹src ≠ tmp›.symm,htmp])
  refine ⟨v₂,n₁+(4*(splitPlanes rows).length+4),hu₂.trans hu₁,?_,(Exec.seq he₁' he₂).cast rfl ?_⟩
  · rw [hlenPlanes]; nlinarith only [hn₁]
  · apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases his : i = src <;> by_cases hia : i = archive <;>
      simp_all [M,Function.update_apply]

def splitFibers (prefixClock count clock volume fiberVolume src archive zeroBank oneBank tmp : Fin T) :
    Pr P T Q A U :=
  scanFibers prefixClock src archive (splitFiber count clock volume fiberVolume src archive zeroBank oneBank tmp)

theorem splitFibers_exec (prefixClock count clock volume fiberVolume src archive zeroBank oneBank tmp : Fin T)
    (hreg : [prefixClock,count,clock,volume,fiberVolume,src,archive,zeroBank,oneBank,tmp].Nodup)
    (fibers : List (List (List (Fin (A+4)) × List (Fin (A+4))))) (B R : ℕ)
    (hlen : ∀ rows ∈ fibers, rows.length = B ∧ ∀ r ∈ rows, r.1.length = R ∧ r.2.length = R)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hprefix : (S.R prefixClock).length = fibers.length)
    (hcount : (S.R count).length = B) (hvolume : (S.R volume).length = R)
    (hfiber : (S.R fiberVolume).length = 2*(B*R))
    (hsrc : S.R src = fibers.flatMap pairStream++tail)
    (hclock : S.R clock = []) (harchive : S.R archive = [])
    (hzero : S.R zeroBank = []) (hone : S.R oneBank = []) (htmp : S.R tmp = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ fibers.length*(24*(B*R)+15*B+17)+4 ∧
      Exec body (splitFibers prefixClock count clock volume fiberVolume src archive zeroBank oneBank tmp)
        (mk v S) n (mk v' {S with R := (Function.update (Function.update S.R src
          (fibers.flatMap splitPlanes++tail)) prefixClock [])}) := by
  have hr := hreg
  regs_ne hr
  have hlenOutput : (fibers.flatMap splitPlanes).length = fibers.length*(2*(B*R)) := by
    rw [List.length_flatMap,List.map_eq_replicate_iff.mpr ?_,List.sum_replicate,smul_eq_mul]
    intro rows hm
    have hh := hlen rows hm
    have hz : (rows.flatMap Prod.fst).length = B*R := by
      rw [List.length_flatMap,List.map_eq_replicate_iff.mpr (by intro r hr; exact (hh.2 r hr).1),
        List.sum_replicate,smul_eq_mul,hh.1]
    have ho : (rows.flatMap Prod.snd).length = B*R := by
      rw [List.length_flatMap,List.map_eq_replicate_iff.mpr (by intro r hr; exact (hh.2 r hr).2),
        List.sum_replicate,smul_eq_mul,hh.1]
    simp only [splitPlanes,List.length_append,hz,ho]; omega
  obtain ⟨v',n,hu,hn,he⟩ := scanFibers_exec (body := body) prefixClock src archive
    (by regs_nodup) (splitFiber count clock volume fiberVolume src archive zeroBank oneBank tmp)
    fibers pairStream splitPlanes (B*(20*R+15)+14) tail v S
    (by
      intro rows hm vi F rest hframe hs
      have hkeep (i : Fin T) (hi : i ∈ [count,clock,volume,fiberVolume,zeroBank,oneBank,tmp]) :
          F.R i = S.R i := by
        apply hframe
        all_goals
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
          rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
          all_goals first | assumption | (apply Ne.symm; assumption)
      obtain ⟨vf,m,hu,hn,he⟩ := splitFiber_exec (body := body)
        count clock volume fiberVolume src archive zeroBank oneBank tmp (by regs_nodup)
        rows R (hlen rows hm).2 rest vi F
        (by rw [hkeep _ (by simp),hcount,(hlen rows hm).1])
        (by rw [hkeep _ (by simp)]; exact hvolume)
        (by rw [hkeep _ (by simp),hfiber,(hlen rows hm).1]) hs
        (by rw [hkeep _ (by simp)]; exact hclock)
        (by rw [hkeep _ (by simp)]; exact hzero)
        (by rw [hkeep _ (by simp)]; exact hone)
        (by rw [hkeep _ (by simp)]; exact htmp)
      exact ⟨vf,m,hu,by simpa only [(hlen rows hm).1] using hn,he⟩)
    hprefix hsrc harchive
  refine ⟨v',n,hu,?_,he⟩
  rw [hlenOutput] at hn
  nlinarith only [hn]

/-- Retain the prefix count for the next bit pass. -/
def retainedSplitFibers
    (prefixCount prefixClock count clock volume fiberVolume src archive zeroBank oneBank tmp : Fin T) :
    Pr P T Q A U :=
  .seq (copyR prefixCount prefixClock tmp (fun _ => tick))
    (splitFibers prefixClock count clock volume fiberVolume src archive zeroBank oneBank tmp)

theorem retainedSplitFibers_exec
    (prefixCount prefixClock count clock volume fiberVolume src archive zeroBank oneBank tmp : Fin T)
    (hreg : [prefixCount,prefixClock,count,clock,volume,fiberVolume,src,archive,zeroBank,oneBank,tmp].Nodup)
    (fibers : List (List (List (Fin (A+4)) × List (Fin (A+4))))) (B R : ℕ)
    (hlen : ∀ rows ∈ fibers, rows.length = B ∧ ∀ r ∈ rows, r.1.length = R ∧ r.2.length = R)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hprefix : (S.R prefixCount).length = fibers.length)
    (hcount : (S.R count).length = B) (hvolume : (S.R volume).length = R)
    (hfiber : (S.R fiberVolume).length = 2*(B*R))
    (hsrc : S.R src = fibers.flatMap pairStream++tail)
    (hprefixClock : S.R prefixClock = []) (hclock : S.R clock = [])
    (harchive : S.R archive = []) (hzero : S.R zeroBank = [])
    (hone : S.R oneBank = []) (htmp : S.R tmp = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ fibers.length*(24*(B*R)+15*B+21)+8 ∧
      Exec body (retainedSplitFibers prefixCount prefixClock count clock volume fiberVolume
        src archive zeroBank oneBank tmp) (mk v S) n
        (mk v' {S with R := Function.update S.R src (fibers.flatMap splitPlanes++tail)}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := copyR_exec (body := body) prefixCount prefixClock tmp
    ‹prefixCount ≠ prefixClock› ‹prefixCount ≠ tmp› ‹prefixClock ≠ tmp› (fun _ => tick) v S htmp
  let M : Stacks T A := {S with R := (Function.update S.R prefixClock
    (((S.R prefixCount).map (fun _ => tick)).reverse++S.R prefixClock))}
  have hoff (i : Fin T) (hi : i ≠ prefixClock) : M.R i = S.R i := by simp [M,hi]
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := splitFibers_exec (body := body)
    prefixClock count clock volume fiberVolume src archive zeroBank oneBank tmp (by regs_nodup)
    fibers B R hlen tail v₁ M (by simp [M,hprefixClock,hprefix])
    (by rw [hoff count ‹prefixClock ≠ count›.symm]; exact hcount)
    (by rw [hoff volume ‹prefixClock ≠ volume›.symm]; exact hvolume)
    (by rw [hoff fiberVolume ‹prefixClock ≠ fiberVolume›.symm]; exact hfiber)
    (by rw [hoff src ‹prefixClock ≠ src›.symm]; exact hsrc)
    (by rw [hoff clock ‹prefixClock ≠ clock›.symm]; exact hclock)
    (by rw [hoff archive ‹prefixClock ≠ archive›.symm]; exact harchive)
    (by rw [hoff zeroBank ‹prefixClock ≠ zeroBank›.symm]; exact hzero)
    (by rw [hoff oneBank ‹prefixClock ≠ oneBank›.symm]; exact hone)
    (by rw [hoff tmp ‹prefixClock ≠ tmp›.symm]; exact htmp)
  refine ⟨v₂,(4*(S.R prefixCount).length+4)+n₂,hu₂.trans hu₁,?_,(Exec.seq he₁ he₂).cast rfl ?_⟩
  · rw [hprefix]; nlinarith only [hn₂]
  · apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hic : i = prefixClock
    · subst i; simp [M,‹prefixClock ≠ src›,hprefixClock]
    · simp [M,Function.update_apply,hic]

/-- The traversal adds no payload-dependent push bound. -/
theorem scanFibers_pushBound (clock src archive : Fin T) (p : Pr P T Q A U)
    (hp : mnNativePushBound 2 p) : mnNativePushBound 2 (scanFibers clock src archive p) := by
  simp [scanFibers,countedLoop,countedLoopBody,moveR,whileR,moveStep,peekR,mnNativePushBound,mnActPush] at *
  exact hp

theorem retainedSplitFibers_pushBound
    (prefixCount prefixClock count clock volume fiberVolume src archive zeroBank oneBank tmp : Fin T) :
    mnNativePushBound 2 (retainedSplitFibers (P := P) (Q := Q) (A := A) (U := U)
      prefixCount prefixClock count clock volume fiberVolume src archive zeroBank oneBank tmp) := by
  simp only [retainedSplitFibers,mnNativePushBound]
  constructor
  · simp [copyR,copyStep,moveR,whileR,moveStep,peekR,mnNativePushBound,mnActPush]
  · apply scanFibers_pushBound
    simp only [splitFiber,mnNativePushBound]
    constructor
    · exact retainedSplitBlockPairs_pushBound _ _ _ _ _ _ _
    · simp [transfer,moveR,moveStep,scanR,keepIn,transferAct,drainR,popDo,whileR,peekR,mnNativePushBound,mnActPush]

end IntegerMultBounds.MathlibTM2.Routing.FiberScan
