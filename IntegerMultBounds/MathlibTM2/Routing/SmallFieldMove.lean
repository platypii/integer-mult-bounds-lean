module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedLoop
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSlice
public import IntegerMultBounds.MathlibTM2.StackResources

/-! The complete one-bit field move [B] × [2] × [R] → [2] × [B] × [R].
Two private archives retain block order; no payload-dependent address arithmetic
or large-field exposure is used. The proof is structural in arbitrary blocks.
This is the small complete-field move of the pinned bulk tape-transfer note. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.SmallFieldMove
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

/-- Successive zero/one blocks of the binary field. -/
def pairStream {α : Type} (rows : List (List α × List α)) : List α :=
  rows.flatMap fun r => r.1++r.2

theorem pairStream_length {α : Type} (rows : List (List α × List α)) :
    (pairStream rows).length = (rows.flatMap Prod.fst).length+(rows.flatMap Prod.snd).length := by
  induction rows with
  | nil => rfl
  | cons r rows ih =>
    simp only [pairStream,List.flatMap_cons,List.length_append] at *
    omega

def splitPair (volume src zeroBank oneBank tmp : Fin T) : Pr P T Q A U :=
  .seq (transfer volume src zeroBank tmp) (transfer volume src oneBank tmp)

theorem splitPair_exec (volume src zeroBank oneBank tmp : Fin T)
    (hreg : [volume,src,zeroBank,oneBank,tmp].Nodup)
    (xs ys tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = xs++ys++tail)
    (hxs : (S.R volume).length = xs.length) (hys : xs.length = ys.length)
    (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (splitPair volume src zeroBank oneBank tmp) (mk v S)
        ((4*xs.length+4)+(4*ys.length+4))
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R src tail)
          zeroBank (xs.reverse++S.R zeroBank)) oneBank (ys.reverse++S.R oneBank))}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := transfer_exec (body := body) (count := volume) (src := src)
    (dst := zeroBank) (tmp := tmp) (by regs_nodup) v S xs (ys++tail)
    (by simpa only [List.append_assoc] using hsrc) hxs htmp
  let M : Stacks T A := {S with R := (Function.update (Function.update S.R src (ys++tail))
    zeroBank (xs.reverse++S.R zeroBank))}
  obtain ⟨v₂,hu₂,he₂⟩ := transfer_exec (body := body) (count := volume) (src := src)
    (dst := oneBank) (tmp := tmp) (by regs_nodup) v₁ M ys tail
    (by simp [M,‹src ≠ zeroBank›])
    (by simp [M,‹volume ≠ src›,‹volume ≠ zeroBank›,hxs,hys])
    (by simp [M,‹src ≠ tmp›.symm,‹zeroBank ≠ tmp›.symm,htmp])
  refine ⟨v₂,hu₂.trans hu₁,(Exec.seq he₁ he₂).cast rfl ?_⟩
  apply congrArg (mk v₂)
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases hs : i = src <;> by_cases hz : i = zeroBank <;> by_cases ho : i = oneBank <;>
    simp_all [M,Function.update_apply]

def splitBlockPairs (clock volume src zeroBank oneBank tmp : Fin T) : Pr P T Q A U :=
  .seq (countedLoop clock (splitPair volume src zeroBank oneBank tmp))
    (.seq (moveR oneBank src id) (moveR zeroBank src id))

/-- The loop consumes only its owned prefix. Archives and scan scratch return
empty, and the entire source suffix survives after the field permutation. -/
theorem splitBlockPairs_exec (clock volume src zeroBank oneBank tmp : Fin T)
    (hreg : [clock,volume,src,zeroBank,oneBank,tmp].Nodup)
    (rows : List (List (Fin (A+4)) × List (Fin (A+4)))) (R : ℕ)
    (hlen : ∀ r ∈ rows, r.1.length = R ∧ r.2.length = R)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hclock : (S.R clock).length = rows.length) (hvolume : (S.R volume).length = R)
    (hsrc : S.R src = pairStream rows++tail)
    (hzero : S.R zeroBank = []) (hone : S.R oneBank = []) (htmp : S.R tmp = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ rows.length*(12*R+11)+6 ∧
      Exec body (splitBlockPairs clock volume src zeroBank oneBank tmp) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R src
          (rows.flatMap Prod.fst++rows.flatMap Prod.snd++tail)) clock [])}) := by
  have hr := hreg
  regs_ne hr
  let Inv := fun j (F : Stacks T A) => ∃ done todo : List (List (Fin (A+4)) × List (Fin (A+4))),
    rows = done++todo ∧ done.length = j ∧ F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
    (∀ i, i ≠ src → i ≠ zeroBank → i ≠ oneBank → i ≠ clock → F.R i = S.R i) ∧
    F.R src = pairStream todo++tail ∧ F.R zeroBank = (done.flatMap Prod.fst).reverse ∧
    F.R oneBank = (done.flatMap Prod.snd).reverse
  obtain ⟨v₁,F,n,hu₁,hn,he,hc,hI⟩ := countedLoop_exec (body := body) clock
    (splitPair volume src zeroBank oneBank tmp) rows.length (8*R+8) Inv
    (by
      intro j F xs hI
      obtain ⟨done,todo,hd,hj,hi,ho,hl,hframe,hs,hz,hone'⟩ := hI
      refine ⟨done,todo,hd,hj,hi,ho,hl,?_,?_,?_,?_⟩
      · intro i his hiz hio hic
        simpa only [Function.update_of_ne hic] using hframe i his hiz hio hic
      · simpa only [Function.update_of_ne ‹clock ≠ src›.symm] using hs
      · simpa only [Function.update_of_ne ‹clock ≠ zeroBank›.symm] using hz
      · simpa only [Function.update_of_ne ‹clock ≠ oneBank›.symm] using hone')
    (by
      intro j hj vi F hI
      obtain ⟨done,todo,hd,hj',hi,ho,hl,hframe,hs,hz,hone'⟩ := hI
      cases todo with
      | nil => simp only [List.append_nil] at hd; subst rows; omega
      | cons r todo =>
        have hm : r ∈ rows := by rw [hd]; simp
        have hkeep (i : Fin T) (hi : i ∈ [volume,tmp]) : F.R i = S.R i := by
          apply hframe
          all_goals
            simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
            rcases hi with rfl | rfl
            all_goals first | assumption | (apply Ne.symm; assumption)
        obtain ⟨v',hu,hex⟩ := splitPair_exec (body := body) volume src zeroBank oneBank tmp
          (by regs_nodup) r.1 r.2 (pairStream todo++tail) vi F
          (by simpa only [pairStream,List.flatMap_cons,List.append_assoc] using hs)
          (by rw [hkeep _ (by simp),hvolume,(hlen r hm).1])
          ((hlen r hm).1.trans (hlen r hm).2.symm)
          (by rw [hkeep _ (by simp)]; exact htmp)
        let F' : Stacks T A := {F with R := (Function.update (Function.update (Function.update F.R src
          (pairStream todo++tail)) zeroBank (r.1.reverse++F.R zeroBank)) oneBank (r.2.reverse++F.R oneBank))}
        refine ⟨v',F',_,hu,?_,hex,?_,done++[r],todo,?_,?_,hi,ho,hl,?_,?_,?_,?_⟩
        · rw [(hlen r hm).1,(hlen r hm).2]; omega
        · simp [F',‹clock ≠ src›,‹clock ≠ zeroBank›,‹clock ≠ oneBank›]
        · simpa only [List.append_assoc,List.singleton_append] using hd
        · simp [hj']
        · intro i his hiz hio hic
          simpa only [F',Function.update_of_ne his,Function.update_of_ne hiz,Function.update_of_ne hio] using
            hframe i his hiz hio hic
        · simp [F',‹src ≠ zeroBank›,‹src ≠ oneBank›]
        · simp [F',‹zeroBank ≠ oneBank›,hz,List.flatMap_append,List.reverse_append]
        · simp [F',hone',List.flatMap_append,List.reverse_append])
    v S hclock ⟨[],rows,rfl,rfl,rfl,rfl,rfl,(by intros; rfl),hsrc,by simpa using hzero,by simpa using hone⟩
  obtain ⟨done,todo,hd,hj,hi,ho,hl,hframe,hs,hz,hone'⟩ := hI
  have ht : todo = [] := by
    have hh := congrArg List.length hd
    simp only [List.length_append] at hh
    exact List.eq_nil_of_length_eq_zero (by omega)
  subst todo
  simp only [List.append_nil] at hd
  subst done
  simp only [pairStream,List.flatMap_nil,List.nil_append] at hs
  obtain ⟨v₂,hu₂,he₂⟩ := moveR_exec body oneBank src ‹src ≠ oneBank›.symm id v₁ F
  let M : Stacks T A := {F with R := movedR F.R oneBank src id (F.R oneBank)}
  obtain ⟨v₃,hu₃,he₃⟩ := moveR_exec body zeroBank src ‹src ≠ zeroBank›.symm id v₂ M
  have hzlen : (rows.flatMap Prod.fst).length = rows.length*R := by
    rw [List.length_flatMap,List.map_eq_replicate_iff.mpr (by intro r hr; exact (hlen r hr).1),
      List.sum_replicate,smul_eq_mul]
  have holen : (rows.flatMap Prod.snd).length = rows.length*R := by
    rw [List.length_flatMap,List.map_eq_replicate_iff.mpr (by intro r hr; exact (hlen r hr).2),
      List.sum_replicate,smul_eq_mul]
  refine ⟨v₃,n+((2*(F.R oneBank).length+2)+(2*(M.R zeroBank).length+2)),
    hu₃.trans (hu₂.trans hu₁),?_,(Exec.seq he (Exec.seq he₂ he₃)).cast rfl ?_⟩
  · simp only [hone',List.length_reverse,M,movedR,Function.update_of_ne ‹src ≠ zeroBank›.symm,
      Function.update_of_ne ‹zeroBank ≠ oneBank›,hz,hzlen,holen]
    nlinarith only [hn]
  · apply congrArg (mk v₃)
    refine Stacks.ext hi ho hl ?_
    funext i
    by_cases his : i = src
    · subst i; simp [M,movedR,hs,hz,hone',
        ‹zeroBank ≠ oneBank›,‹src ≠ zeroBank›.symm,‹clock ≠ src›.symm,List.append_assoc]
    by_cases hiz : i = zeroBank
    · subst i; simp [M,movedR,‹src ≠ zeroBank›.symm,hzero,‹clock ≠ zeroBank›.symm]
    by_cases hio : i = oneBank
    · subst i; simp [M,movedR,‹src ≠ oneBank›.symm,‹zeroBank ≠ oneBank›.symm,hone,‹clock ≠ oneBank›.symm]
    by_cases hic : i = clock
    · subst i; simp [M,movedR,‹clock ≠ src›,‹clock ≠ zeroBank›,‹clock ≠ oneBank›,hc]
    · simp [M,movedR,his,hiz,hio,hic,hframe i his hiz hio hic]

/-- Append the next pair in reverse to a private archive. -/
def joinPair (volume zeroBank oneBank dst tmp : Fin T) : Pr P T Q A U :=
  .seq (transfer volume zeroBank dst tmp) (transfer volume oneBank dst tmp)

theorem joinPair_exec (volume zeroBank oneBank dst tmp : Fin T)
    (hreg : [volume,zeroBank,oneBank,dst,tmp].Nodup)
    (xs ys zeroTail oneTail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hzero : S.R zeroBank = xs++zeroTail) (hone : S.R oneBank = ys++oneTail)
    (hxs : (S.R volume).length = xs.length) (hys : xs.length = ys.length)
    (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (joinPair volume zeroBank oneBank dst tmp) (mk v S)
        ((4*xs.length+4)+(4*ys.length+4))
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R
          zeroBank zeroTail) oneBank oneTail) dst ((xs++ys).reverse++S.R dst))}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := transfer_exec (body := body) (count := volume) (src := zeroBank)
    (dst := dst) (tmp := tmp) (by regs_nodup) v S xs zeroTail hzero hxs htmp
  let M : Stacks T A := {S with R := (Function.update (Function.update S.R zeroBank zeroTail)
    dst (xs.reverse++S.R dst))}
  obtain ⟨v₂,hu₂,he₂⟩ := transfer_exec (body := body) (count := volume) (src := oneBank)
    (dst := dst) (tmp := tmp) (by regs_nodup) v₁ M ys oneTail
    (by simpa [M,‹zeroBank ≠ oneBank›.symm,‹oneBank ≠ dst›] using hone)
    (by simp [M,‹volume ≠ zeroBank›,‹volume ≠ dst›,hxs,hys])
    (by simp [M,‹zeroBank ≠ tmp›.symm,‹dst ≠ tmp›.symm,htmp])
  refine ⟨v₂,hu₂.trans hu₁,(Exec.seq he₁ he₂).cast rfl ?_⟩
  apply congrArg (mk v₂)
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases hz : i = zeroBank <;> by_cases ho : i = oneBank <;> by_cases hd : i = dst <;>
    simp_all [M,List.reverse_append,List.append_assoc]

/-- Interleave two complete block planes into a reverse archive. The caller
can concatenate that archive back onto its tensor after splitting the planes. -/
def joinBlockPairs (clock volume zeroBank oneBank dst tmp : Fin T) : Pr P T Q A U :=
  countedLoop clock (joinPair volume zeroBank oneBank dst tmp)

theorem joinBlockPairs_exec (clock volume zeroBank oneBank dst tmp : Fin T)
    (hreg : [clock,volume,zeroBank,oneBank,dst,tmp].Nodup)
    (rows : List (List (Fin (A+4)) × List (Fin (A+4)))) (R : ℕ)
    (hlen : ∀ r ∈ rows, r.1.length = R ∧ r.2.length = R)
    (zeroTail oneTail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hclock : (S.R clock).length = rows.length) (hvolume : (S.R volume).length = R)
    (hzero : S.R zeroBank = rows.flatMap Prod.fst++zeroTail)
    (hone : S.R oneBank = rows.flatMap Prod.snd++oneTail) (htmp : S.R tmp = []) :
    ∃ v' F n, v'.user = v.user ∧ n ≤ rows.length*(8*R+11)+2 ∧
      Exec body (joinBlockPairs clock volume zeroBank oneBank dst tmp) (mk v S) n (mk v' F) ∧
      F.R zeroBank = zeroTail ∧ F.R oneBank = oneTail ∧
      F.R dst = (pairStream rows).reverse++S.R dst ∧ F.R clock = [] ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      ∀ i, i ≠ zeroBank → i ≠ oneBank → i ≠ dst → i ≠ clock → F.R i = S.R i := by
  have hr := hreg
  regs_ne hr
  let Inv := fun j (F : Stacks T A) => ∃ done todo : List (List (Fin (A+4)) × List (Fin (A+4))),
    rows = done++todo ∧ done.length = j ∧ F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
    (∀ i, i ≠ zeroBank → i ≠ oneBank → i ≠ dst → i ≠ clock → F.R i = S.R i) ∧
    F.R zeroBank = todo.flatMap Prod.fst++zeroTail ∧
    F.R oneBank = todo.flatMap Prod.snd++oneTail ∧
    F.R dst = (pairStream done).reverse++S.R dst
  obtain ⟨v₁,F,n,hu₁,hn,he,hc,hI⟩ := countedLoop_exec (body := body) clock
    (joinPair volume zeroBank oneBank dst tmp) rows.length (8*R+8) Inv
    (by
      intro j F xs hI
      obtain ⟨done,todo,hd,hj,hi,ho,hl,hframe,hz,hone',hdst⟩ := hI
      refine ⟨done,todo,hd,hj,hi,ho,hl,?_,?_,?_,?_⟩
      · intro i hiz hio hid hic
        simpa only [Function.update_of_ne hic] using hframe i hiz hio hid hic
      · simpa only [Function.update_of_ne ‹clock ≠ zeroBank›.symm] using hz
      · simpa only [Function.update_of_ne ‹clock ≠ oneBank›.symm] using hone'
      · simpa only [Function.update_of_ne ‹clock ≠ dst›.symm] using hdst)
    (by
      intro j hj vi F hI
      obtain ⟨done,todo,hd,hj',hi,ho,hl,hframe,hz,hone',hdst⟩ := hI
      cases todo with
      | nil => simp only [List.append_nil] at hd; subst rows; omega
      | cons r todo =>
        have hm : r ∈ rows := by rw [hd]; simp
        have hkeep (i : Fin T) (hi : i ∈ [volume,tmp]) : F.R i = S.R i := by
          apply hframe
          all_goals
            simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
            rcases hi with rfl | rfl
            all_goals first | assumption | (apply Ne.symm; assumption)
        obtain ⟨v',hu,hex⟩ := joinPair_exec (body := body) volume zeroBank oneBank dst tmp
          (by regs_nodup) r.1 r.2 (todo.flatMap Prod.fst++zeroTail)
          (todo.flatMap Prod.snd++oneTail) vi F
          (by simpa only [List.flatMap_cons,List.append_assoc] using hz)
          (by simpa only [List.flatMap_cons,List.append_assoc] using hone')
          (by rw [hkeep _ (by simp),hvolume,(hlen r hm).1])
          ((hlen r hm).1.trans (hlen r hm).2.symm)
          (by rw [hkeep _ (by simp)]; exact htmp)
        let F' : Stacks T A := {F with R := (Function.update (Function.update (Function.update F.R
          zeroBank (todo.flatMap Prod.fst++zeroTail)) oneBank (todo.flatMap Prod.snd++oneTail))
          dst ((r.1++r.2).reverse++F.R dst))}
        refine ⟨v',F',_,hu,?_,hex,?_,done++[r],todo,?_,?_,hi,ho,hl,?_,?_,?_,?_⟩
        · rw [(hlen r hm).1,(hlen r hm).2]; omega
        · simp [F',‹clock ≠ zeroBank›,‹clock ≠ oneBank›,‹clock ≠ dst›]
        · simpa only [List.append_assoc,List.singleton_append] using hd
        · simp [hj']
        · intro i hiz hio hid hic
          simpa only [F',Function.update_of_ne hiz,Function.update_of_ne hio,Function.update_of_ne hid] using
            hframe i hiz hio hid hic
        · simp [F',‹zeroBank ≠ oneBank›,‹zeroBank ≠ dst›]
        · simp [F',‹oneBank ≠ dst›]
        · simp [F',hdst,pairStream,List.flatMap_append,List.reverse_append,List.append_assoc])
    v S hclock ⟨[],rows,rfl,rfl,rfl,rfl,rfl,(by intros; rfl),hzero,hone,by simp [pairStream]⟩
  obtain ⟨done,todo,hd,hj,hi,ho,hl,hframe,hz,hone',hdst⟩ := hI
  have ht : todo = [] := by
    have hh := congrArg List.length hd
    simp only [List.length_append] at hh
    exact List.eq_nil_of_length_eq_zero (by omega)
  subst todo
  simp only [List.append_nil] at hd
  subst done
  exact ⟨v₁,F,n,hu₁,hn,he,by simpa using hz,by simpa using hone',hdst,hc,hi,ho,hl,hframe⟩

/-- Undo the complete binary-field move, using ordinary retained block and
plane-volume headers. No scan touches the tensor suffix. -/
def mergeBlockPairs (count clock volume planeVolume src zeroBank archive tmp : Fin T) : Pr P T Q A U :=
  .seq (transfer planeVolume src archive tmp)
    (.seq (moveR archive zeroBank id)
      (.seq (copyR count clock tmp (fun _ => tick))
        (.seq (joinBlockPairs clock volume zeroBank src archive tmp) (moveR archive src id))))

theorem mergeBlockPairs_exec (count clock volume planeVolume src zeroBank archive tmp : Fin T)
    (hreg : [count,clock,volume,planeVolume,src,zeroBank,archive,tmp].Nodup)
    (rows : List (List (Fin (A+4)) × List (Fin (A+4)))) (R : ℕ)
    (hlen : ∀ r ∈ rows, r.1.length = R ∧ r.2.length = R)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hcount : (S.R count).length = rows.length) (hvolume : (S.R volume).length = R)
    (hplane : (S.R planeVolume).length = rows.length*R)
    (hsrc : S.R src = rows.flatMap Prod.fst++rows.flatMap Prod.snd++tail)
    (hclock : S.R clock = []) (hzero : S.R zeroBank = [])
    (harchive : S.R archive = []) (htmp : S.R tmp = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ rows.length*(18*R+15)+14 ∧
      Exec body (mergeBlockPairs count clock volume planeVolume src zeroBank archive tmp) (mk v S) n
        (mk v' {S with R := Function.update S.R src (pairStream rows++tail)}) := by
  have hr := hreg
  regs_ne hr
  have hzlen : (rows.flatMap Prod.fst).length = rows.length*R := by
    rw [List.length_flatMap,List.map_eq_replicate_iff.mpr (by intro r hr; exact (hlen r hr).1),
      List.sum_replicate,smul_eq_mul]
  have holen : (rows.flatMap Prod.snd).length = rows.length*R := by
    rw [List.length_flatMap,List.map_eq_replicate_iff.mpr (by intro r hr; exact (hlen r hr).2),
      List.sum_replicate,smul_eq_mul]
  obtain ⟨v₁,hu₁,he₁⟩ := transfer_exec (body := body) (count := planeVolume) (src := src)
    (dst := archive) (tmp := tmp) (by regs_nodup) v S (rows.flatMap Prod.fst)
    (rows.flatMap Prod.snd++tail) (by simpa only [List.append_assoc] using hsrc)
    (hplane.trans hzlen.symm) htmp
  let S₁ : Stacks T A := {S with R := (Function.update (Function.update S.R src
    (rows.flatMap Prod.snd++tail)) archive (rows.flatMap Prod.fst).reverse)}
  have he₁' : Exec body (transfer planeVolume src archive tmp) (mk v S)
      (4*(rows.flatMap Prod.fst).length+4) (mk v₁ S₁) := by
    simpa only [harchive,List.append_nil] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := moveR_exec body archive zeroBank ‹zeroBank ≠ archive›.symm id v₁ S₁
  let S₂ : Stacks T A := {S₁ with R := movedR S₁.R archive zeroBank id (S₁.R archive)}
  have hkeep (i : Fin T) (his : i ≠ src) (hiz : i ≠ zeroBank) (hia : i ≠ archive) :
      S₂.R i = S.R i := by simp [S₂,S₁,movedR,his,hiz,hia]
  obtain ⟨v₃,hu₃,he₃⟩ := copyR_exec (body := body) count clock tmp
    ‹count ≠ clock› ‹count ≠ tmp› ‹clock ≠ tmp› (fun _ => tick) v₂ S₂
    (by rw [hkeep tmp ‹src ≠ tmp›.symm ‹zeroBank ≠ tmp›.symm ‹archive ≠ tmp›.symm]; exact htmp)
  let S₃ : Stacks T A := {S₂ with R := (Function.update S₂.R clock
    (((S₂.R count).map (fun _ => tick)).reverse++S₂.R clock))}
  have hkeep₃ (i : Fin T) (his : i ≠ src) (hiz : i ≠ zeroBank)
      (hia : i ≠ archive) (hic : i ≠ clock) : S₃.R i = S.R i := by
    simp only [S₃,Function.update_of_ne hic]; exact hkeep i his hiz hia
  obtain ⟨v₄,F,n₄,hu₄,hn₄,he₄,hz,hs,ha,hc,hi,ho,hl,hframe⟩ := joinBlockPairs_exec
    (body := body) clock volume zeroBank src archive tmp (by regs_nodup) rows R hlen [] tail v₃ S₃
    (by simp [S₃,hkeep count ‹count ≠ src› ‹count ≠ zeroBank› ‹count ≠ archive›,
      hkeep clock ‹clock ≠ src› ‹clock ≠ zeroBank› ‹clock ≠ archive›,hclock,hcount])
    (by rw [hkeep₃ volume ‹volume ≠ src› ‹volume ≠ zeroBank› ‹volume ≠ archive› ‹clock ≠ volume›.symm]; exact hvolume)
    (by simp [S₃,S₂,S₁,movedR,‹clock ≠ zeroBank›.symm,‹zeroBank ≠ archive›,
      ‹src ≠ zeroBank›.symm,hzero])
    (by simp [S₃,S₂,S₁,movedR,‹clock ≠ src›.symm,‹src ≠ zeroBank›,‹src ≠ archive›])
    (by rw [hkeep₃ tmp ‹src ≠ tmp›.symm ‹zeroBank ≠ tmp›.symm ‹archive ≠ tmp›.symm ‹clock ≠ tmp›.symm]; exact htmp)
  have ha₃ : S₃.R archive = [] := by
    simp [S₃,S₂,movedR,‹clock ≠ archive›.symm,‹zeroBank ≠ archive›.symm]
  simp only [ha₃,List.append_nil] at ha
  obtain ⟨v₅,hu₅,he₅⟩ := moveR_exec body archive src ‹src ≠ archive›.symm id v₄ F
  refine ⟨v₅,_,hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))),?_,
    (Exec.seq he₁' (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ he₅)))).cast rfl ?_⟩
  · simp only [S₁,Function.update_self,List.length_reverse,ha,
      hkeep count ‹count ≠ src› ‹count ≠ zeroBank› ‹count ≠ archive›,hcount,
      pairStream_length,hzlen,holen]
    nlinarith only [hn₄]
  · apply congrArg (mk v₅)
    refine Stacks.ext hi ho hl ?_
    funext i
    by_cases his : i = src
    · subst i; simp [movedR,ha,hs]
    by_cases hia : i = archive
    · subst i; simp [movedR,‹src ≠ archive›.symm,harchive]
    by_cases hiz : i = zeroBank
    · subst i; simp [movedR,‹src ≠ zeroBank›.symm,‹zeroBank ≠ archive›,hz,hzero]
    by_cases hic : i = clock
    · subst i; simp [movedR,‹clock ≠ src›,‹clock ≠ archive›,hc,hclock]
    · simp only [movedR,Function.update_of_ne his,Function.update_of_ne hia]
      exact (hframe i hiz his hia hic).trans (hkeep₃ i his hiz hia hic)

/-- Produce the plane-volume header from the retained dimensions, execute the
inverse field move, and retire the derived header. -/
def generatedMergeBlockPairs (count clock volume planeVolume src zeroBank archive saved tmp : Fin T) :
    Pr P T Q A U :=
  .seq (unaryProduct count volume planeVolume saved tmp)
    (.seq (mergeBlockPairs count clock volume planeVolume src zeroBank archive tmp) (uclear planeVolume))

theorem generatedMergeBlockPairs_exec (count clock volume planeVolume src zeroBank archive saved tmp : Fin T)
    (hreg : [count,clock,volume,planeVolume,src,zeroBank,archive,saved,tmp].Nodup)
    (rows : List (List (Fin (A+4)) × List (Fin (A+4)))) (R : ℕ)
    (hlen : ∀ r ∈ rows, r.1.length = R ∧ r.2.length = R)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hcount : (S.R count).length = rows.length) (hvolume : (S.R volume).length = R)
    (hsrc : S.R src = rows.flatMap Prod.fst++rows.flatMap Prod.snd++tail)
    (hclock : S.R clock = []) (hplane : S.R planeVolume = []) (hzero : S.R zeroBank = [])
    (harchive : S.R archive = []) (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ rows.length*(24*R+24)+20 ∧
      Exec body (generatedMergeBlockPairs count clock volume planeVolume src zeroBank archive saved tmp)
        (mk v S) n (mk v' {S with R := Function.update S.R src (pairStream rows++tail)}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := unaryProduct_exec (body := body)
    (show [count,volume,planeVolume,saved,tmp].Nodup by regs_nodup) v S hsaved htmp
  let S₁ : Stacks T A := {S with R := (Function.update S.R planeVolume
    (List.replicate (rows.length*R) tick))}
  have he₁' : Exec body (unaryProduct count volume planeVolume saved tmp)
      (mk v S) n₁ (mk v₁ S₁) := by
    simpa only [hcount,hvolume,hplane,List.append_nil] using he₁
  have hoff (i : Fin T) (hi : i ≠ planeVolume) : S₁.R i = S.R i := by simp [S₁,hi]
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := mergeBlockPairs_exec (body := body)
    count clock volume planeVolume src zeroBank archive tmp (by regs_nodup) rows R hlen tail v₁ S₁
    (by rw [hoff count ‹count ≠ planeVolume›]; exact hcount)
    (by rw [hoff volume ‹volume ≠ planeVolume›]; exact hvolume)
    (by simp [S₁])
    (by rw [hoff src ‹planeVolume ≠ src›.symm]; exact hsrc)
    (by rw [hoff clock ‹clock ≠ planeVolume›]; exact hclock)
    (by rw [hoff zeroBank ‹planeVolume ≠ zeroBank›.symm]; exact hzero)
    (by rw [hoff archive ‹planeVolume ≠ archive›.symm]; exact harchive)
    (by rw [hoff tmp ‹planeVolume ≠ tmp›.symm]; exact htmp)
  let S₂ : Stacks T A := {S₁ with R := Function.update S₁.R src (pairStream rows++tail)}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) planeVolume v₂ S₂
  refine ⟨v₃,n₁+(n₂+(2*(S₂.R planeVolume).length+2)),hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁' (Exec.seq he₂ he₃)).cast rfl ?_⟩
  · simp only [S₂,Function.update_of_ne ‹planeVolume ≠ src›,S₁,
      Function.update_self,List.length_replicate]
    rw [hcount,hvolume] at hn₁
    nlinarith only [hn₁,hn₂]
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases his : i = src
    · subst i; simp [S₂,S₁,‹planeVolume ≠ src›.symm]
    by_cases hip : i = planeVolume
    · subst i; simp [‹planeVolume ≠ src›,hplane]
    · simp [S₂,S₁,his,hip]

/-- Retain the block count so successive binary passes share their controls. -/
def retainedSplitBlockPairs (count clock volume src zeroBank oneBank tmp : Fin T) : Pr P T Q A U :=
  .seq (copyR count clock tmp (fun _ => tick)) (splitBlockPairs clock volume src zeroBank oneBank tmp)

theorem retainedSplitBlockPairs_exec (count clock volume src zeroBank oneBank tmp : Fin T)
    (hreg : [count,clock,volume,src,zeroBank,oneBank,tmp].Nodup)
    (rows : List (List (Fin (A+4)) × List (Fin (A+4)))) (R : ℕ)
    (hlen : ∀ r ∈ rows, r.1.length = R ∧ r.2.length = R)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hcount : (S.R count).length = rows.length) (hvolume : (S.R volume).length = R)
    (hsrc : S.R src = pairStream rows++tail)
    (hclock : S.R clock = []) (hzero : S.R zeroBank = [])
    (hone : S.R oneBank = []) (htmp : S.R tmp = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ rows.length*(12*R+15)+10 ∧
      Exec body (retainedSplitBlockPairs count clock volume src zeroBank oneBank tmp) (mk v S) n
        (mk v' {S with R := (Function.update S.R src
          (rows.flatMap Prod.fst++rows.flatMap Prod.snd++tail))}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := copyR_exec (body := body) count clock tmp
    ‹count ≠ clock› ‹count ≠ tmp› ‹clock ≠ tmp› (fun _ => tick) v S htmp
  let M : Stacks T A := {S with R := (Function.update S.R clock
    (((S.R count).map (fun _ => tick)).reverse++S.R clock))}
  have hoff (i : Fin T) (hi : i ≠ clock) : M.R i = S.R i := by simp [M,hi]
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := splitBlockPairs_exec (body := body)
    clock volume src zeroBank oneBank tmp (by regs_nodup) rows R hlen tail v₁ M
    (by simp [M,hclock,hcount])
    (by rw [hoff volume ‹clock ≠ volume›.symm]; exact hvolume)
    (by rw [hoff src ‹clock ≠ src›.symm]; exact hsrc)
    (by rw [hoff zeroBank ‹clock ≠ zeroBank›.symm]; exact hzero)
    (by rw [hoff oneBank ‹clock ≠ oneBank›.symm]; exact hone)
    (by rw [hoff tmp ‹clock ≠ tmp›.symm]; exact htmp)
  refine ⟨v₂,(4*(S.R count).length+4)+n₂,hu₂.trans hu₁,?_,(Exec.seq he₁ he₂).cast rfl ?_⟩
  · rw [hcount]; nlinarith only [hn₂]
  · apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hic : i = clock
    · subst i; simp [M,‹clock ≠ src›,hclock]
    · simp [M,Function.update_apply,hic]

/-- Each native action adds at most two symbols, independently of block data. -/
theorem splitBlockPairs_pushBound (clock volume src zeroBank oneBank tmp : Fin T) :
    mnNativePushBound 2 (splitBlockPairs (P := P) (Q := Q) (A := A) (U := U)
      clock volume src zeroBank oneBank tmp) := by
  simp [splitBlockPairs,splitPair,countedLoop,countedLoopBody,
    transfer,moveR,scanR,keepIn,transferAct,drainR,popDo,whileR,moveStep,peekR,
    mnNativePushBound,mnActPush]

theorem retainedSplitBlockPairs_pushBound (count clock volume src zeroBank oneBank tmp : Fin T) :
    mnNativePushBound 2 (retainedSplitBlockPairs (P := P) (Q := Q) (A := A) (U := U)
      count clock volume src zeroBank oneBank tmp) := by
  simp only [retainedSplitBlockPairs,mnNativePushBound]
  constructor
  · simp [copyR,copyStep,moveR,whileR,moveStep,peekR,mnNativePushBound,mnActPush]
  · exact splitBlockPairs_pushBound clock volume src zeroBank oneBank tmp

/-- Inverse movement has the same constant native push bound as forward movement. -/
theorem generatedMergeBlockPairs_pushBound
    (count clock volume planeVolume src zeroBank archive saved tmp : Fin T) :
    mnNativePushBound 2 (generatedMergeBlockPairs (P := P) (Q := Q) (A := A) (U := U)
      count clock volume planeVolume src zeroBank archive saved tmp) := by
  simp [generatedMergeBlockPairs,mergeBlockPairs,joinBlockPairs,joinPair,
    unaryProduct,scanP,popPush,ucopy,umulSym,uclear,pushN,copyR,copyStep,
    countedLoop,countedLoopBody,transfer,moveR,scanR,keepIn,transferAct,
    drainR,popDo,whileR,moveStep,peekR,mnNativePushBound,mnActPush]

theorem retainedSplitBlockPairs_within_stock
    {count clock volume src zeroBank oneBank tmp : Fin T} {v v' : HS T Q A U}
    {S F : Stacks T A} {n B R : ℕ}
    (hex : Exec body (retainedSplitBlockPairs count clock volume src zeroBank oneBank tmp)
      (mk v S) n (mk v' F))
    (hn : n ≤ B*(12*R+15)+10) (depth : ℕ) :
    ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+2*(B*(12*R+15)+10))
      depth (retainedSplitBlockPairs count clock volume src zeroBank oneBank tmp)
      (mk v S) n (mk v' F) := by
  exact mn_native_exec_within hex 2 (retainedSplitBlockPairs_pushBound _ _ _ _ _ _ _) depth _ (by omega)

theorem generatedMergeBlockPairs_within_stock
    {count clock volume planeVolume src zeroBank archive saved tmp : Fin T} {v v' : HS T Q A U}
    {S F : Stacks T A} {n B R : ℕ}
    (hex : Exec body (generatedMergeBlockPairs count clock volume planeVolume src zeroBank archive saved tmp)
      (mk v S) n (mk v' F))
    (hn : n ≤ B*(24*R+24)+20) (depth : ℕ) :
    ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+2*(B*(24*R+24)+20))
      depth (generatedMergeBlockPairs count clock volume planeVolume src zeroBank archive saved tmp)
      (mk v S) n (mk v' F) := by
  exact mn_native_exec_within hex 2 (generatedMergeBlockPairs_pushBound _ _ _ _ _ _ _ _ _)
    depth _ (by omega)

end IntegerMultBounds.MathlibTM2.Routing.SmallFieldMove
