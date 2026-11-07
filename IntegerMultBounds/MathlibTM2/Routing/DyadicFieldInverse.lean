module

public import IntegerMultBounds.MathlibTM2.Routing.DyadicFieldInverseStep
public import IntegerMultBounds.MathlibTM2.Routing.DyadicFieldRefinement

/-! Undo the complete dyadic field move with a fixed runtime bit-count loop.
The structural refinement path supplies each preceding binary frontier. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.DyadicFieldInverse
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz DyadicFieldLayout DyadicFieldMove
  DyadicFieldInverseStep DyadicFieldRefinement FieldBoundaryStock
variable {T Q A : ℕ} {P U β : Type} {body : P → Pr P T Q A U}

def inverseFieldMove
    (bits prefixCount prefixClock count clock volume planeVolume src archive zeroBank oneBank tmp : Fin T) :
    Pr P T Q A U :=
  countedLoop bits (inverseFieldStep prefixCount prefixClock count clock volume planeVolume src archive zeroBank oneBank tmp)

theorem inverseFieldMove_exec
    (bits prefixCount prefixClock count clock volume planeVolume src archive zeroBank oneBank tmp : Fin T)
    (hreg : [bits,prefixCount,prefixClock,count,clock,volume,planeVolume,src,archive,zeroBank,oneBank,tmp].Nodup)
    (encode : β → List (Fin (A+4))) (W B N : ℕ) (hW : 0 < W) (hB : 0 < B)
    (hlen : ∀ x, (encode x).length = W)
    (fibers : List (List (Field β N))) (hrows : ∀ rows ∈ fibers, rows.length = B)
    (hpositive : 0 < fibers.length)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hbits : (S.R bits).length = N) (hprefix : (S.R prefixCount).length = fibers.length*2^N)
    (hcount : (S.R count).length = B) (hvolume : (S.R volume).length = W)
    (hplane : (S.R planeVolume).length = B*W)
    (hsrc : S.R src = (finish fibers).flatMap (fun rows => rows.flatMap encode)++tail)
    (hprefixClock : S.R prefixClock = []) (hclock : S.R clock = [])
    (harchive : S.R archive = []) (hzero : S.R zeroBank = [])
    (hone : S.R oneBank = []) (htmp : S.R tmp = []) :
    ∃ v' F n, v'.user = v.user ∧ n ≤ N*(64*(stream encode fibers).length+3)+2 ∧
      Exec body (inverseFieldMove bits prefixCount prefixClock count clock volume planeVolume
        src archive zeroBank oneBank tmp) (mk v S) n (mk v' F) ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+200*(stream encode fibers).length)
        depth (inverseFieldMove bits prefixCount prefixClock count clock volume planeVolume
          src archive zeroBank oneBank tmp) (mk v S) n (mk v' F)) ∧
      F.R src = stream encode fibers++tail ∧ (F.R prefixCount).length = fibers.length ∧
      (F.R volume).length = 2^N*W ∧ (F.R planeVolume).length = B*(2^N*W) ∧ F.R bits = [] ∧
      Frame bits prefixCount volume planeVolume src S F := by
  have hr := hreg
  regs_ne hr
  let V := (stream encode fibers).length
  let Inv := fun j (F : Stacks T A) => ∃ fs : List (List (Field β j)),
    Refines fibers fs ∧ F.R src = stream encode fs++tail ∧
    (F.R prefixCount).length = fs.length ∧ (F.R volume).length = 2^j*W ∧
    (F.R planeVolume).length = B*(2^j*W) ∧ Frame bits prefixCount volume planeVolume src S F
  have hNV : N ≤ V := by
    dsimp only [V]
    rw [stream_length encode W B hlen fibers hrows]
    exact bits_le_volume N fibers.length B W hpositive hB hW
  have hinputlen : ((finish fibers).flatMap (fun rows => rows.flatMap encode)).length = V := by
    have hh := (Refines.complete fibers).volume encode W B hlen hrows
    simpa only [stream,word,V] using hh
  have hstock : ∀ j (vi : HS T Q A U) F, Inv j F → (F.R bits).length ≤ N →
      mnSize (mk vi F) ≤ mnSize (mk v S)+4*V := by
    intro j vi F hI hb
    obtain ⟨fs,hreach,hs,hp,hv,hf,hi,ho,hl,hframe⟩ := hI
    have hrowsF := hreach.row_length B hrows
    have hpos := hreach.positive hpositive
    have hV : (stream encode fs).length = V := hreach.volume encode W B hlen hrows
    have hdims := dimensions_le_volume hpos hB (Nat.mul_pos (Nat.two_pow_pos j) hW)
    have hd : fs.length*(B*(2^j*W)) = V :=
      (stream_length encode W B hlen fs hrowsF).symm.trans hV
    rw [hd] at hdims
    apply fieldBoundary_stock v vi S F bits prefixCount volume planeVolume src V hi ho hl hframe
    · rw [hs,hsrc,List.length_append,List.length_append,hV,hinputlen]
    · exact hb.trans hNV
    · rw [hp]; exact hdims.1
    · rw [hv]; exact hdims.2.1
    · rw [hf]; exact hdims.2.2
  obtain ⟨v₁,F,n,hu,hn,he,hc,hI⟩ := countedLoop_exec_bounded_stock (body := body) bits
    (inverseFieldStep prefixCount prefixClock count clock volume planeVolume src archive zeroBank oneBank tmp)
    N (64*V) (mnSize (mk v S)+4*V) (192*V) Inv
    (by
      intro j F xs hI
      obtain ⟨fs,hreach,hs,hp,hv,hf,hi,ho,hl,hframe⟩ := hI
      refine ⟨fs,hreach,?_,?_,?_,?_,hi,ho,hl,?_⟩
      · simpa only [Function.update_of_ne ‹bits ≠ src›.symm] using hs
      · simpa only [Function.update_of_ne ‹bits ≠ prefixCount›.symm] using hp
      · simpa only [Function.update_of_ne ‹bits ≠ volume›.symm] using hv
      · simpa only [Function.update_of_ne ‹bits ≠ planeVolume›.symm] using hf
      · intro i hm
        have hib : i ≠ bits := by intro h; subst i; simp at hm
        simpa only [Function.update_of_ne hib] using hframe i hm)
    hstock
    (by
      intro j hj vi F hI hremaining
      have hb := hstock j vi F hI (by omega)
      obtain ⟨fs,hreach,hs,hp,hv,hf,hi,ho,hl,hframe⟩ := hI
      cases hreach with
      | refl => omega
      | @step _ _ parents hparent =>
        have hrowsP := hparent.row_length B hrows
        have hpos := hparent.positive hpositive
        have hV := hparent.volume encode W B hlen hrows
        have hkeep (i : Fin T) (hm : i ∈ [prefixClock,count,clock,archive,zeroBank,oneBank,tmp]) :
            F.R i = S.R i := by
          apply hframe
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
          rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
          all_goals simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
          all_goals repeat' apply And.intro
          all_goals first | assumption | (apply Ne.symm; assumption)
        obtain ⟨vf,m,hu',hm,hex⟩ := inverseFieldStep_exec (body := body)
          prefixCount prefixClock count clock volume planeVolume src archive zeroBank oneBank tmp
          (by regs_nodup) encode W B j hlen parents hrowsP tail vi F
          (by simpa only [refineFibers_length] using hp)
          (by rw [hkeep _ (by simp)]; exact hcount) hv hf hs
          (by rw [hkeep _ (by simp)]; exact hprefixClock)
          (by rw [hkeep _ (by simp)]; exact hclock)
          (by rw [hkeep _ (by simp)]; exact harchive)
          (by rw [hkeep _ (by simp)]; exact hzero)
          (by rw [hkeep _ (by simp)]; exact hone)
          (by rw [hkeep _ (by simp)]; exact htmp)
        let F' : Stacks T A := {F with R := (Function.update (Function.update (Function.update (Function.update F.R
          prefixCount (List.replicate parents.length tick)) src (stream encode parents++tail))
          volume (F.R volume++F.R volume)) planeVolume (F.R planeVolume++F.R planeVolume))}
        have hcost := inverseFieldStep_cost_le_volume hpos hB (Nat.mul_pos (Nat.two_pow_pos j) hW) hm
        have hVj : V = 2*(parents.length*(B*(2^j*W))) := by
          change (stream encode fibers).length = _
          rw [←hV,stream_length encode W B hlen parents hrowsP,Nat.pow_succ]; ring
        refine ⟨vf,F',m,hu',?_,?_,?_,parents,hparent,?_,?_,?_,?_,hi,ho,hl,?_⟩
        · rw [hVj]; exact hcost
        · intro depth
          have hmV : m ≤ 64*V := by rw [hVj]; exact hcost
          exact mn_native_exec_within hex 3 (inverseFieldStep_pushBound _ _ _ _ _ _ _ _ _ _ _)
            depth _ (by omega)
        · simp [F',‹bits ≠ prefixCount›,‹bits ≠ src›,‹bits ≠ volume›,‹bits ≠ planeVolume›]
        · simp [F',‹volume ≠ src›.symm,‹planeVolume ≠ src›.symm]
        · simp [F',‹prefixCount ≠ src›,‹prefixCount ≠ volume›,‹prefixCount ≠ planeVolume›]
        · simp [F',‹volume ≠ planeVolume›,hv,Nat.pow_succ]; ring
        · simp [F',hf,Nat.pow_succ]; ring
        · intro i hm
          have hbits := hm
          simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hbits
          obtain ⟨hib,hip,hiv,hif,his⟩ := hbits
          simpa only [F',Function.update_of_ne hip,Function.update_of_ne hif,
            Function.update_of_ne his,Function.update_of_ne hiv] using hframe i hm)
    v S hbits ⟨finish fibers,Refines.complete fibers,(by simpa only [stream,word] using hsrc),
      (by simpa only [finish_length] using hprefix),(by simpa using hvolume),(by simpa using hplane),
      rfl,rfl,rfl,(by intros; rfl)⟩
  obtain ⟨fs,hreach,hs,hp,hv,hf,hframe⟩ := hI
  have hfs : fibers = fs := hreach.eq_of_same
  subst fs
  refine ⟨v₁,F,n,hu,hn,(he 0).toExec,?_,hs,hp,hv,hf,hc,hframe⟩
  intro depth
  exact (he depth).mono (by
    intro d z hz
    change mnSize z+d ≤ mnSize (mk v S)+4*V+depth+192*V at hz
    change mnSize z+d ≤ mnSize (mk v S)+depth+200*V
    omega)

theorem inverseFieldMove_pushBound
    (bits prefixCount prefixClock count clock volume planeVolume src archive zeroBank oneBank tmp : Fin T) :
    mnNativePushBound 3 (inverseFieldMove (P := P) (Q := Q) (A := A) (U := U)
      bits prefixCount prefixClock count clock volume planeVolume src archive zeroBank oneBank tmp) := by
  have hp := inverseFieldStep_pushBound (P := P) (Q := Q) (A := A) (U := U)
    prefixCount prefixClock count clock volume planeVolume src archive zeroBank oneBank tmp
  simpa [inverseFieldMove,countedLoop,countedLoopBody,peekR,mnNativePushBound,mnActPush] using hp

end IntegerMultBounds.MathlibTM2.Routing.DyadicFieldInverse
