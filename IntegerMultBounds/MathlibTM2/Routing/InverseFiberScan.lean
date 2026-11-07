module

public import IntegerMultBounds.MathlibTM2.Routing.FiberScan

/-! Inverse complete-field passes over arbitrary prefix fibers. The accumulating
output archive stays separate from the private inverse-movement scratch. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.InverseFiberScan
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  SmallFieldMove FiberScan
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

/-- Transfer two consecutive header-sized pieces, without allocating a doubled header. -/
def transferTwice (volume src dst tmp : Fin T) : Pr P T Q A U :=
  .seq (transfer volume src dst tmp) (transfer volume src dst tmp)

theorem transferTwice_exec (volume src dst tmp : Fin T) (hreg : [volume,src,dst,tmp].Nodup)
    (xs tail : List (Fin (A+4))) (m : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = xs++tail) (hvolume : (S.R volume).length = m)
    (hlen : xs.length = 2*m) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧ Exec body (transferTwice volume src dst tmp) (mk v S) (4*xs.length+8)
      (mk v' {S with R := (Function.update (Function.update S.R src tail) dst (xs.reverse++S.R dst))}) := by
  have hr := hreg
  regs_ne hr
  have htake : (xs.take m).length = m := by rw [List.length_take,hlen]; omega
  have hdrop : (xs.drop m).length = m := by rw [List.length_drop,hlen]; omega
  obtain ⟨v₁,hu₁,he₁⟩ := transfer_exec (body := body) (count := volume) (src := src)
    (dst := dst) (tmp := tmp) hreg v S (xs.take m) (xs.drop m++tail)
    (by rw [←List.append_assoc,List.take_append_drop]; exact hsrc) (hvolume.trans htake.symm) htmp
  let M : Stacks T A := {S with R := (Function.update (Function.update S.R src (xs.drop m++tail))
    dst ((xs.take m).reverse++S.R dst))}
  obtain ⟨v₂,hu₂,he₂⟩ := transfer_exec (body := body) (count := volume) (src := src)
    (dst := dst) (tmp := tmp) hreg v₁ M (xs.drop m) tail
    (by simp [M,‹src ≠ dst›])
    (by simp [M,‹volume ≠ src›,‹volume ≠ dst›,hvolume,hdrop])
    (by simp [M,‹src ≠ tmp›.symm,‹dst ≠ tmp›.symm,htmp])
  refine ⟨v₂,hu₂.trans hu₁,(Exec.seq he₁ he₂).cast ?_ ?_⟩
  · rw [htake,hdrop,hlen]; omega
  · apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    have hrev : (xs.drop m).reverse++(xs.take m).reverse = xs.reverse := by
      rw [←List.reverse_append,List.take_append_drop]
    funext i
    by_cases his : i = src <;> by_cases hid : i = dst <;>
      simp_all [M,←List.append_assoc]

/-- Undo one fiber permutation, then advance that fiber into the shared output
archive. The one-bank tape is private scratch for the inner inverse operation. -/
def mergeFiber (count clock volume planeVolume src archive zeroBank oneBank tmp : Fin T) : Pr P T Q A U :=
  .seq (mergeBlockPairs count clock volume planeVolume src zeroBank oneBank tmp)
    (transferTwice planeVolume src archive tmp)

theorem mergeFiber_exec (count clock volume planeVolume src archive zeroBank oneBank tmp : Fin T)
    (hreg : [count,clock,volume,planeVolume,src,archive,zeroBank,oneBank,tmp].Nodup)
    (rows : List (List (Fin (A+4)) × List (Fin (A+4)))) (R : ℕ)
    (hlen : ∀ r ∈ rows, r.1.length = R ∧ r.2.length = R)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hcount : (S.R count).length = rows.length) (hvolume : (S.R volume).length = R)
    (hplane : (S.R planeVolume).length = rows.length*R)
    (hsrc : S.R src = splitPlanes rows++tail)
    (hclock : S.R clock = []) (hzero : S.R zeroBank = [])
    (hone : S.R oneBank = []) (htmp : S.R tmp = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ rows.length*(26*R+15)+22 ∧
      Exec body (mergeFiber count clock volume planeVolume src archive zeroBank oneBank tmp) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R src tail)
          archive ((pairStream rows).reverse++S.R archive))}) := by
  have hr := hreg
  regs_ne hr
  have hzlen : (rows.flatMap Prod.fst).length = rows.length*R := by
    rw [List.length_flatMap,List.map_eq_replicate_iff.mpr (by intro r hr; exact (hlen r hr).1),
      List.sum_replicate,smul_eq_mul]
  have holen : (rows.flatMap Prod.snd).length = rows.length*R := by
    rw [List.length_flatMap,List.map_eq_replicate_iff.mpr (by intro r hr; exact (hlen r hr).2),
      List.sum_replicate,smul_eq_mul]
  have hlenStream : (pairStream rows).length = 2*(rows.length*R) := by
    rw [pairStream_length,hzlen,holen]; omega
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := mergeBlockPairs_exec (body := body)
    count clock volume planeVolume src zeroBank oneBank tmp (by regs_nodup) rows R hlen tail v S
    hcount hvolume hplane (by simpa only [splitPlanes,List.append_assoc] using hsrc) hclock hzero hone htmp
  let M : Stacks T A := {S with R := Function.update S.R src (pairStream rows++tail)}
  obtain ⟨v₂,hu₂,he₂⟩ := transferTwice_exec (body := body) planeVolume src archive tmp (by regs_nodup)
    (pairStream rows) tail (rows.length*R) v₁ M (by simp [M])
    (by simp [M,‹planeVolume ≠ src›,hplane]) hlenStream
    (by simp [M,‹src ≠ tmp›.symm,htmp])
  refine ⟨v₂,n₁+(4*(pairStream rows).length+8),hu₂.trans hu₁,?_,(Exec.seq he₁ he₂).cast rfl ?_⟩
  · rw [hlenStream]; nlinarith only [hn₁]
  · apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases his : i = src <;> by_cases hia : i = archive <;>
      simp_all [M,Function.update_apply]

def mergeFibers (prefixClock count clock volume planeVolume src archive zeroBank oneBank tmp : Fin T) :
    Pr P T Q A U :=
  scanFibers prefixClock src archive (mergeFiber count clock volume planeVolume src archive zeroBank oneBank tmp)

theorem mergeFibers_exec (prefixClock count clock volume planeVolume src archive zeroBank oneBank tmp : Fin T)
    (hreg : [prefixClock,count,clock,volume,planeVolume,src,archive,zeroBank,oneBank,tmp].Nodup)
    (fibers : List (List (List (Fin (A+4)) × List (Fin (A+4))))) (B R : ℕ)
    (hlen : ∀ rows ∈ fibers, rows.length = B ∧ ∀ r ∈ rows, r.1.length = R ∧ r.2.length = R)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hprefix : (S.R prefixClock).length = fibers.length)
    (hcount : (S.R count).length = B) (hvolume : (S.R volume).length = R)
    (hfiber : (S.R planeVolume).length = (B*R))
    (hsrc : S.R src = fibers.flatMap splitPlanes++tail)
    (hclock : S.R clock = []) (harchive : S.R archive = [])
    (hzero : S.R zeroBank = []) (hone : S.R oneBank = []) (htmp : S.R tmp = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ fibers.length*(30*(B*R)+15*B+25)+4 ∧
      Exec body (mergeFibers prefixClock count clock volume planeVolume src archive zeroBank oneBank tmp)
        (mk v S) n (mk v' {S with R := (Function.update (Function.update S.R src
          (fibers.flatMap pairStream++tail)) prefixClock [])}) := by
  have hr := hreg
  regs_ne hr
  have hlenOutput : (fibers.flatMap pairStream).length = fibers.length*(2*(B*R)) := by
    rw [List.length_flatMap,List.map_eq_replicate_iff.mpr ?_,List.sum_replicate,smul_eq_mul]
    intro rows hm
    have hh := hlen rows hm
    have hz : (rows.flatMap Prod.fst).length = B*R := by
      rw [List.length_flatMap,List.map_eq_replicate_iff.mpr (by intro r hr; exact (hh.2 r hr).1),
        List.sum_replicate,smul_eq_mul,hh.1]
    have ho : (rows.flatMap Prod.snd).length = B*R := by
      rw [List.length_flatMap,List.map_eq_replicate_iff.mpr (by intro r hr; exact (hh.2 r hr).2),
        List.sum_replicate,smul_eq_mul,hh.1]
    simp only [pairStream_length,hz,ho]; omega
  obtain ⟨v',n,hu,hn,he⟩ := scanFibers_exec (body := body) prefixClock src archive
    (by regs_nodup) (mergeFiber count clock volume planeVolume src archive zeroBank oneBank tmp)
    fibers splitPlanes pairStream (B*(26*R+15)+22) tail v S
    (by
      intro rows hm vi F rest hframe hs
      have hkeep (i : Fin T) (hi : i ∈ [count,clock,volume,planeVolume,zeroBank,oneBank,tmp]) :
          F.R i = S.R i := by
        apply hframe
        all_goals
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
          rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
          all_goals first | assumption | (apply Ne.symm; assumption)
      obtain ⟨vf,m,hu,hn,he⟩ := mergeFiber_exec (body := body)
        count clock volume planeVolume src archive zeroBank oneBank tmp (by regs_nodup)
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
def retainedMergeFibers
    (prefixCount prefixClock count clock volume planeVolume src archive zeroBank oneBank tmp : Fin T) :
    Pr P T Q A U :=
  .seq (copyR prefixCount prefixClock tmp (fun _ => tick))
    (mergeFibers prefixClock count clock volume planeVolume src archive zeroBank oneBank tmp)

theorem retainedMergeFibers_exec
    (prefixCount prefixClock count clock volume planeVolume src archive zeroBank oneBank tmp : Fin T)
    (hreg : [prefixCount,prefixClock,count,clock,volume,planeVolume,src,archive,zeroBank,oneBank,tmp].Nodup)
    (fibers : List (List (List (Fin (A+4)) × List (Fin (A+4))))) (B R : ℕ)
    (hlen : ∀ rows ∈ fibers, rows.length = B ∧ ∀ r ∈ rows, r.1.length = R ∧ r.2.length = R)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hprefix : (S.R prefixCount).length = fibers.length)
    (hcount : (S.R count).length = B) (hvolume : (S.R volume).length = R)
    (hfiber : (S.R planeVolume).length = (B*R))
    (hsrc : S.R src = fibers.flatMap splitPlanes++tail)
    (hprefixClock : S.R prefixClock = []) (hclock : S.R clock = [])
    (harchive : S.R archive = []) (hzero : S.R zeroBank = [])
    (hone : S.R oneBank = []) (htmp : S.R tmp = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ fibers.length*(30*(B*R)+15*B+29)+8 ∧
      Exec body (retainedMergeFibers prefixCount prefixClock count clock volume planeVolume
        src archive zeroBank oneBank tmp) (mk v S) n
        (mk v' {S with R := Function.update S.R src (fibers.flatMap pairStream++tail)}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := copyR_exec (body := body) prefixCount prefixClock tmp
    ‹prefixCount ≠ prefixClock› ‹prefixCount ≠ tmp› ‹prefixClock ≠ tmp› (fun _ => tick) v S htmp
  let M : Stacks T A := {S with R := (Function.update S.R prefixClock
    (((S.R prefixCount).map (fun _ => tick)).reverse++S.R prefixClock))}
  have hoff (i : Fin T) (hi : i ≠ prefixClock) : M.R i = S.R i := by simp [M,hi]
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := mergeFibers_exec (body := body)
    prefixClock count clock volume planeVolume src archive zeroBank oneBank tmp (by regs_nodup)
    fibers B R hlen tail v₁ M (by simp [M,hprefixClock,hprefix])
    (by rw [hoff count ‹prefixClock ≠ count›.symm]; exact hcount)
    (by rw [hoff volume ‹prefixClock ≠ volume›.symm]; exact hvolume)
    (by rw [hoff planeVolume ‹prefixClock ≠ planeVolume›.symm]; exact hfiber)
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

end IntegerMultBounds.MathlibTM2.Routing.InverseFiberScan
