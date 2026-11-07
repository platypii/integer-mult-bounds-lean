module

public import IntegerMultBounds.MathlibTM2.Routing.DyadicFieldStep
public import IntegerMultBounds.MathlibTM2.Routing.FieldBoundaryStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedLoopBoundedStock

/-! Move an entire short dyadic field across complete spectator rows with one
runtime counted loop. Binary significance and spectator order are structural. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.DyadicFieldMove
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz DyadicFieldLayout DyadicFieldStep FieldBoundaryStock
variable {T Q A : ℕ} {P U β : Type} {body : P → Pr P T Q A U}

/-- Rows transposed into binary column order, most significant digit first. -/
def columns : {k : ℕ} → List (Field β k) → List (List β)
  | 0, rows => [rows]
  | _+1, rows => columns (rows.map Prod.fst)++columns (rows.map Prod.snd)

def finish {k : ℕ} (fibers : List (List (Field β k))) : List (List β) :=
  fibers.flatMap columns

theorem finish_refine {k : ℕ} (fibers : List (List (Field β (k+1)))) :
    finish (refineFibers fibers) = finish fibers := by
  induction fibers with
  | nil => rfl
  | cons rows fibers ih =>
    simpa [finish,refineFibers,columns,List.flatMap_append,List.append_assoc] using
      congrArg (fun xs => columns (rows.map Prod.fst)++columns (rows.map Prod.snd)++xs) ih

theorem finish_zero (fibers : List (List (Field β 0))) : finish fibers = fibers := by
  simp [finish,columns]

theorem columns_length {k : ℕ} (rows : List (Field β k)) : (columns rows).length = 2^k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [columns,List.length_append,ih,Nat.pow_succ]; omega

theorem finish_length {k : ℕ} (fibers : List (List (Field β k))) :
    (finish fibers).length = fibers.length*2^k := by
  rw [finish,List.length_flatMap,List.map_eq_replicate_iff.mpr ?_,List.sum_replicate,smul_eq_mul]
  intro rows _
  exact columns_length rows

def fieldMove
    (bits prefixCount prefixClock count clock volume fiberVolume src archive zeroBank oneBank tmp : Fin T) :
    Pr P T Q A U :=
  countedLoop bits (fieldStep prefixCount prefixClock count clock volume fiberVolume src archive zeroBank oneBank tmp)

/-- A frame for the owned movement headers and source. All other tapes survive
exactly, including the archive and scratch reused between binary levels. -/
def Frame (bits prefixCount volume fiberVolume src : Fin T) (S F : Stacks T A) : Prop :=
  F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
    ∀ i, i ∉ [bits,prefixCount,volume,fiberVolume,src] → F.R i = S.R i

theorem fieldMove_exec
    (bits prefixCount prefixClock count clock volume fiberVolume src archive zeroBank oneBank tmp : Fin T)
    (hreg : [bits,prefixCount,prefixClock,count,clock,volume,fiberVolume,src,archive,zeroBank,oneBank,tmp].Nodup)
    (encode : β → List (Fin (A+4))) (W B N : ℕ) (hW : 0 < W) (hB : 0 < B)
    (hlen : ∀ x, (encode x).length = W)
    (fibers : List (List (Field β N))) (hrows : ∀ rows ∈ fibers, rows.length = B)
    (hpositive : 0 < fibers.length)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hbits : (S.R bits).length = N) (hprefix : (S.R prefixCount).length = fibers.length)
    (hcount : (S.R count).length = B) (hvolume : (S.R volume).length = 2^N*W)
    (hfiber : (S.R fiberVolume).length = B*(2^N*W))
    (hsrc : S.R src = stream encode fibers++tail)
    (hprefixClock : S.R prefixClock = []) (hclock : S.R clock = [])
    (harchive : S.R archive = []) (hzero : S.R zeroBank = [])
    (hone : S.R oneBank = []) (htmp : S.R tmp = []) :
    ∃ v' F n, v'.user = v.user ∧ n ≤ N*(60*(stream encode fibers).length+3)+2 ∧
      Exec body (fieldMove bits prefixCount prefixClock count clock volume fiberVolume
        src archive zeroBank oneBank tmp) (mk v S) n (mk v' F) ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+200*(stream encode fibers).length)
        depth (fieldMove bits prefixCount prefixClock count clock volume fiberVolume
          src archive zeroBank oneBank tmp) (mk v S) n (mk v' F)) ∧
      F.R src = (finish fibers).flatMap (fun rows => rows.flatMap encode)++tail ∧
      (F.R prefixCount).length = fibers.length*2^N ∧
      (F.R volume).length = W ∧ (F.R fiberVolume).length = B*W ∧ F.R bits = [] ∧
      Frame bits prefixCount volume fiberVolume src S F := by
  have hr := hreg
  regs_ne hr
  let V := (stream encode fibers).length
  let target := finish fibers
  let Inv := fun j (F : Stacks T A) => ∃ (k : ℕ) (fs : List (List (Field β k))),
    j+k = N ∧ (∀ rows ∈ fs, rows.length = B) ∧ 0 < fs.length ∧
    (stream encode fs).length = V ∧ finish fs = target ∧
    F.R src = stream encode fs++tail ∧ (F.R prefixCount).length = fs.length ∧
    (F.R volume).length = 2^k*W ∧ (F.R fiberVolume).length = B*(2^k*W) ∧
    Frame bits prefixCount volume fiberVolume src S F
  have hNV : N ≤ V := by
    dsimp only [V]
    rw [stream_length encode W B hlen fibers hrows]
    exact bits_le_volume N fibers.length B W hpositive hB hW
  have hstock : ∀ j (vi : HS T Q A U) F, Inv j F → (F.R bits).length ≤ N →
      mnSize (mk vi F) ≤ mnSize (mk v S)+4*V := by
    intro j vi F hI hb
    obtain ⟨k,fs,hj,hrowsF,hpos,hV,ht,hs,hp,hv,hf,hi,ho,hl,hframe⟩ := hI
    have hdims := dimensions_le_volume hpos hB (Nat.mul_pos (Nat.two_pow_pos k) hW)
    have hd : fs.length*(B*(2^k*W)) = V :=
      (stream_length encode W B hlen fs hrowsF).symm.trans hV
    rw [hd] at hdims
    apply fieldBoundary_stock v vi S F bits prefixCount volume fiberVolume src V hi ho hl hframe
    · rw [hs,hsrc,List.length_append,List.length_append,hV]
    · exact hb.trans hNV
    · rw [hp]; exact hdims.1
    · rw [hv]; exact hdims.2.1
    · rw [hf]; exact hdims.2.2
  obtain ⟨v₁,F,n,hu,hn,he,hc,hI⟩ := countedLoop_exec_bounded_stock (body := body) bits
    (fieldStep prefixCount prefixClock count clock volume fiberVolume src archive zeroBank oneBank tmp)
    N (60*V) (mnSize (mk v S)+4*V) (180*V) Inv
    (by
      intro j F xs hI
      obtain ⟨k,fs,hj,hrows,hpos,hV,ht,hs,hp,hv,hf,hi,ho,hl,hframe⟩ := hI
      refine ⟨k,fs,hj,hrows,hpos,hV,ht,?_,?_,?_,?_,hi,ho,hl,?_⟩
      · simpa only [Function.update_of_ne ‹bits ≠ src›.symm] using hs
      · simpa only [Function.update_of_ne ‹bits ≠ prefixCount›.symm] using hp
      · simpa only [Function.update_of_ne ‹bits ≠ volume›.symm] using hv
      · simpa only [Function.update_of_ne ‹bits ≠ fiberVolume›.symm] using hf
      · intro i hm
        have hib : i ≠ bits := by intro h; subst i; simp at hm
        simpa only [Function.update_of_ne hib] using hframe i hm)
    hstock
    (by
      intro j hj vi F hI hremaining
      have hb := hstock j vi F hI (by omega)
      obtain ⟨k,fs,hj',hrows,hpos,hV,ht,hs,hp,hv,hf,hi,ho,hl,hframe⟩ := hI
      cases k with
      | zero => omega
      | succ k =>
        have hkeep (i : Fin T) (hm : i ∈ [prefixClock,count,clock,archive,zeroBank,oneBank,tmp]) :
            F.R i = S.R i := by
          apply hframe
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
          rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
          all_goals simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
          all_goals repeat' apply And.intro
          all_goals first | assumption | (apply Ne.symm; assumption)
        obtain ⟨vf,m,hu',hm,hex⟩ := fieldStep_exec (body := body)
          prefixCount prefixClock count clock volume fiberVolume src archive zeroBank oneBank tmp
          (by regs_nodup) encode W B k hlen fs hrows tail vi F hp
          (by rw [hkeep _ (by simp)]; exact hcount)
          (by rw [Nat.pow_succ] at hv; nlinarith only [hv])
          (by rw [Nat.pow_succ] at hf; nlinarith only [hf]) hs
          (by rw [hkeep _ (by simp)]; exact hprefixClock)
          (by rw [hkeep _ (by simp)]; exact hclock)
          (by rw [hkeep _ (by simp)]; exact harchive)
          (by rw [hkeep _ (by simp)]; exact hzero)
          (by rw [hkeep _ (by simp)]; exact hone)
          (by rw [hkeep _ (by simp)]; exact htmp)
        let F' : Stacks T A := {F with R := (Function.update (Function.update (Function.update (Function.update F.R
          volume (List.replicate (2^k*W) tick)) src (stream encode (refineFibers fs)++tail))
          fiberVolume (List.replicate (B*(2^k*W)) tick)) prefixCount (F.R prefixCount++F.R prefixCount))}
        have hcost := fieldStep_cost_le_volume hpos hB (Nat.mul_pos (Nat.two_pow_pos k) hW) hm
        have hVk : V = 2*(fs.length*(B*(2^k*W))) := by
          rw [←hV,stream_length encode W B hlen fs hrows,Nat.pow_succ]; ring
        refine ⟨vf,F',m,hu',?_,?_,?_,k,refineFibers fs,?_,
          refineFibers_row_length fs B hrows,?_,?_,(finish_refine fs).trans ht,?_,?_,?_,?_,hi,ho,hl,?_⟩
        · rw [hVk]; exact hcost
        · intro depth
          have hmV : m ≤ 60*V := by rw [hVk]; exact hcost
          exact mn_native_exec_within hex 3 (fieldStep_pushBound _ _ _ _ _ _ _ _ _ _ _)
            depth _ (by omega)
        · simp [F',‹bits ≠ volume›,‹bits ≠ src›,‹bits ≠ fiberVolume›,‹bits ≠ prefixCount›]
        · omega
        · rw [refineFibers_length]; omega
        · exact (stream_refine_length encode W B hlen fs hrows).trans hV
        · simp [F',‹prefixCount ≠ src›.symm,‹fiberVolume ≠ src›.symm]
        · simp [F',refineFibers_length,hp]; omega
        · simp [F',‹prefixCount ≠ volume›.symm,‹volume ≠ fiberVolume›,‹volume ≠ src›]
        · simp [F',‹prefixCount ≠ fiberVolume›.symm]
        · intro i hm
          have hbits := hm
          simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hbits
          obtain ⟨hib,hip,hiv,hif,his⟩ := hbits
          simpa only [F',Function.update_of_ne hip,Function.update_of_ne hif,
            Function.update_of_ne his,Function.update_of_ne hiv] using hframe i hm)
    v S hbits ⟨N,fibers,by omega,hrows,hpositive,rfl,rfl,hsrc,hprefix,hvolume,hfiber,
      rfl,rfl,rfl,(by intros; rfl)⟩
  obtain ⟨k,fs,hk,hrows',hpos,hV,ht,hs,hp,hv,hf,hframe⟩ := hI
  have hk0 : k = 0 := by omega
  subst k
  have hfs : fs = target := (finish_zero fs).symm.trans ht
  subst fs
  refine ⟨v₁,F,n,hu,hn,(he 0).toExec,?_,?_,?_,?_,?_,hc,hframe⟩
  · intro depth
    exact (he depth).mono (by
      intro d z hz
      change mnSize z+d ≤ mnSize (mk v S)+4*V+depth+180*V at hz
      change mnSize z+d ≤ mnSize (mk v S)+depth+200*V
      omega)
  · simpa only [stream,word] using hs
  · simpa only [target,finish_length] using hp
  · simpa only [Nat.pow_zero,Nat.one_mul] using hv
  · simpa only [Nat.pow_zero,Nat.one_mul] using hf

theorem fieldMove_pushBound
    (bits prefixCount prefixClock count clock volume fiberVolume src archive zeroBank oneBank tmp : Fin T) :
    mnNativePushBound 3 (fieldMove (P := P) (Q := Q) (A := A) (U := U)
      bits prefixCount prefixClock count clock volume fiberVolume src archive zeroBank oneBank tmp) := by
  have hp := fieldStep_pushBound (P := P) (Q := Q) (A := A) (U := U)
    prefixCount prefixClock count clock volume fiberVolume src archive zeroBank oneBank tmp
  simpa [fieldMove,countedLoop,countedLoopBody,peekR,mnNativePushBound,mnActPush] using hp

end IntegerMultBounds.MathlibTM2.Routing.DyadicFieldMove
