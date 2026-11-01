module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationField
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingSourceIntervalMaskHost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedInterval
public import IntegerMultBounds.MathlibTM2.StackResources

/-! The existing word selector also assembles a packed halo. Its traffic is
proportional to the stored interval, without an ambient-period expansion. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def packedPublicationFlags (s t band a b origin N : ℕ) : List Bool :=
  (List.range N).map (fun j => haloInteriorAt s t band a b (origin+j))

theorem publicationWords_packedInterval {s t band a b origin N w : ℕ} [NeZero s]
    (hst : s < t) (hb : b ≤ s) (hfit : origin+N ≤ s) (D Y : ZMod s → GaussianInt) :
    publicationWords (packedPublicationFlags s t band a b origin N)
      ((packedInterval origin N D).map (csyms A w)) ((packedInterval origin N Y).map (csyms A w)) =
      (packedInterval origin N (publicationField t band a b D Y)).map (csyms A w) := by
  let flags := packedPublicationFlags s t band a b origin N
  let xs := (packedInterval origin N D).map (csyms A w)
  let ys := (packedInterval origin N Y).map (csyms A w)
  have hx : xs.length = flags.length := by simp [xs,flags,packedPublicationFlags,packedInterval_length _ hfit]
  have hy : ys.length = flags.length := by simp [ys,flags,packedPublicationFlags,packedInterval_length _ hfit]
  apply List.ext_getElem
  · rw [publicationWords_length flags xs ys hx hy]
    simp [flags,packedPublicationFlags,packedInterval_length _ hfit]
  · intro j hj hk
    have hjN : j < N := by
      simpa only [List.length_map,packedInterval_length _ hfit] using hk
    rw [publicationWords_getElem flags xs ys hx hy j (by simpa [flags,packedPublicationFlags] using hjN)]
    have hflag := haloInteriorAt_spec hst band a b (origin+j) hb (by omega)
    simp only [flags,packedPublicationFlags,xs,ys,List.getElem_map,List.getElem_range,
      packedInterval_get _ hfit hjN]
    by_cases hi : ((origin+j : ℕ) : ZMod s) ∈ haloInterior s t band a b
    · have hi' := hi
      simp only [Nat.cast_add] at hi'
      simp [hflag.mpr hi,publicationField,hi']
    · have hf : haloInteriorAt s t band a b (origin+j) = false :=
        Bool.eq_false_iff.mpr (fun hh => hi (hflag.mp hh))
      have hi' := hi
      simp only [Nat.cast_add] at hi'
      simp [hf,publicationField,hi']

def packedPublicationMerge (count width mask x y reversed dst trash tmp : Fin T) : Pr P T Q A U :=
  .seq (publicationSelectLoop count width mask x y reversed trash tmp) (moveR reversed dst id)

def packedPublicationMergeCost (N w : ℕ) := N*(12*w+15)+4

theorem packedPublicationMerge_native (count width mask x y reversed dst trash tmp : Fin T) :
    mnNativePushBound 2 (packedPublicationMerge (P := P) (Q := Q) (A := A) (U := U)
      count width mask x y reversed dst trash tmp) := by
  simp [packedPublicationMerge,publicationSelectLoop,countedLoop,countedLoopBody,
    publicationSelectWord,publicationChoose,discardPrefix,transfer,transferAct,moveR,moveStep,
    scanR,drainR,popDo,keepIn,whileR,peekR,uclear,mnNativePushBound,mnActPush]

theorem packedPublicationMerge_exec (count width mask x y reversed dst trash tmp : Fin T)
    (hreg : [count,width,mask,x,y,reversed,dst,trash,tmp].Nodup)
    {s t band a b origin N w : ℕ} [NeZero s] (hA : 4 ≤ A)
    (hst : s < t) (hb : b ≤ s) (hfit : origin+N ≤ s) (D Y : ZMod s → GaussianInt)
    (tailX tailY : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hcount : (S.R count).length = N) (hwidth : (S.R width).length = w)
    (hmask : S.R mask = couplingSourceIntervalMaskSymbols false A s t band a b origin N)
    (hX : S.R x = cstream A w (packedInterval origin N D)++tailX)
    (hY : S.R y = cstream A w (packedInterval origin N Y)++tailY)
    (hreversed : S.R reversed = []) (htrash : S.R trash = []) (htmp : S.R tmp = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ packedPublicationMergeCost N w ∧
      Exec body (packedPublicationMerge count width mask x y reversed dst trash tmp) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update
          (Function.update S.R mask []) x tailX) y tailY) dst
            (cstream A w (packedInterval origin N (publicationField t band a b D Y))++S.R dst)) count [])}) := by
  have hr := hreg
  regs_ne hr
  let flags := packedPublicationFlags s t band a b origin N
  let xs := (packedInterval origin N D).map (csyms A w)
  let ys := (packedInterval origin N Y).map (csyms A w)
  let words := cstream A w (packedInterval origin N (publicationField t band a b D Y))
  have hwords : (publicationWords flags xs ys).flatten = words := by
    rw [publicationWords_packedInterval hst hb hfit]
    rfl
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := publicationSelectLoop_exec (body := body)
    (count := count) (width := width) (mask := mask) (x := x) (y := y) (dst := reversed)
    (trash := trash) (tmp := tmp) (by regs_nodup) hA flags xs ys w
    (by simp [xs,flags,packedPublicationFlags,packedInterval_length _ hfit])
    (by simp [ys,flags,packedPublicationFlags,packedInterval_length _ hfit])
    (by intro z hz; obtain ⟨z,_,rfl⟩ := List.mem_map.mp hz; simp)
    (by intro z hz; obtain ⟨z,_,rfl⟩ := List.mem_map.mp hz; simp) tailX tailY v S
    (by simpa [flags,packedPublicationFlags] using hcount) hwidth
    (by simpa [couplingSourceIntervalMaskSymbols,flags,packedPublicationFlags,haloMaskAt,List.map_map,Function.comp_def] using hmask)
    hX hY htrash htmp
  let M : Stacks T A := {S with R := (Function.update (Function.update (Function.update (Function.update
    (Function.update S.R mask []) x tailX) y tailY) reversed words.reverse) count [])}
  have he₁' : Exec body (publicationSelectLoop count width mask x y reversed trash tmp) (mk v S) n₁ (mk v₁ M) := by
    simpa only [hwords,hreversed,List.append_nil] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := moveR_exec body reversed dst ‹reversed ≠ dst› id v₁ M
  have hlen : words.length = N*w := by simp [words,length_cstream,packedInterval_length _ hfit]
  refine ⟨v₂,n₁+(2*(N*w)+2),hu₂.trans hu₁,?_,(Exec.seq he₁' he₂).cast ?_ ?_⟩
  · simp only [flags,packedPublicationFlags,List.length_map,List.length_range] at hn₁
    unfold packedPublicationMergeCost
    nlinarith only [hn₁]
  · simp [M,Function.update_apply,‹count ≠ reversed›.symm,hlen]
  · apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hdst : k = dst
    · subst k
      simp [M,movedR,Function.update_apply,‹count ≠ reversed›.symm,‹count ≠ dst›.symm,
        ‹mask ≠ dst›.symm,‹x ≠ dst›.symm,‹y ≠ dst›.symm,‹reversed ≠ dst›.symm,words]
    by_cases hrev : k = reversed
    · subst k
      simp [M,movedR,Function.update_apply,hreversed,‹count ≠ reversed›.symm,
        ‹mask ≠ reversed›.symm,‹x ≠ reversed›.symm,‹y ≠ reversed›.symm,‹reversed ≠ dst›]
    · simp [M,movedR,Function.update_apply,hrev,hdst]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
