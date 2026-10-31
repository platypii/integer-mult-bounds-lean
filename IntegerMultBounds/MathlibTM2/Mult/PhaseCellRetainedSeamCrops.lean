module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedSeamArchive

/-! A structural seam schedule reuses one full-line result. Each crop restores
all controls, so later readiness follows from the first state's headers. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry ScalarPlacement PhaseCellInterface
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

def retainedSeamCrops
    (clock clockSave sourceSave src dst savedSkip saved tmp rows width retireCount trash retireTmp : Fin T)
    (skip count : ℕ → Fin T) : List ℕ → Pr P T Q A U
  | [] => .act .done
  | k::ks => .seq
      (retainedSeamArchive clock clockSave sourceSave (skip k) (count k) src dst savedSkip saved tmp rows width retireCount trash retireTmp)
      (retainedSeamCrops clock clockSave sourceSave src dst savedSkip saved tmp rows width retireCount trash retireTmp skip count ks)

def SeamCropRows (p coreWidth : ℕ) (r : FamilyDispatchInput s A)
    (J : FamilyDispatchInput s A → (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (k : ℕ) (rs : List (List GaussianInt)) : Prop :=
  (∀ row ∈ rs, row.length = coreLength s coreWidth k) ∧
  List.Forall₂ (fun input row =>
    let out := packedIntervalRead p (2*p+13) (coreStart coreWidth k) (cstream A (2*p+13) row)
    (∀ i ∈ ownedCore s coreWidth k, ‖out i‖ ≤ 1) ∧
    ErrorOn (ownedCore s coreWidth k) out
      ((((2 : ℂ)^inverseNormalizationShift p)⁻¹ • J r) ((1/2 : ℂ) • fun i => value p (input i)))
      (3/(2 : ℝ)^p)) r.inputs.reverse rs

theorem retainedSeamCrops_exec
    (clock clockSave sourceSave src dst savedSkip saved tmp rows width retireCount trash retireTmp : Fin T)
    (skip count : ℕ → Fin T) (ks : List ℕ)
    (hreg : ∀ k ∈ ks, [clock,clockSave,sourceSave,skip k,count k,src,dst,savedSkip,saved,tmp,rows,width,retireCount,trash,retireTmp].Nodup)
    (p coreWidth : ℕ) (r : FamilyDispatchInput s A)
    (J : FamilyDispatchInput s A → (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)) (output : List (Fin (A+4)))
    (hproduced : ExactCoreProduced p s (fun _ => 0) J r output)
    (hstart : ∀ k ∈ ks, coreStart coreWidth k ≤ s)
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = output) (hclock : (S.R clock).length = r.inputs.length)
    (hskip : ∀ k ∈ ks, (S.R (skip k)).length = coreStart coreWidth k*(2*p+13))
    (hcount : ∀ k ∈ ks, (S.R (count k)).length = coreLength s coreWidth k*(2*p+13))
    (hrows : (S.R rows).length = s) (hwidth : (S.R width).length = 2*p+13)
    (hclean : ∀ i ∈ [clockSave,sourceSave,savedSkip,saved,tmp,retireCount,trash,retireTmp], S.R i = []) :
    ∃ rss : List (List (List GaussianInt)), ∃ v' F n, v'.user = v.user ∧
      n ≤ ks.length*(80*(r.inputs.length*s*(2*p+13))+14)+1 ∧
      Exec body (retainedSeamCrops clock clockSave sourceSave src dst savedSkip saved tmp rows width retireCount trash retireTmp skip count ks)
        (mk v S) n (mk v' F) ∧
      F.R dst = (rss.reverse.map (fun rs => cstream A (2*p+13) rs.flatten)).flatten++S.R dst ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      (∀ i, i ≠ dst → F.R i = S.R i) ∧ List.Forall₂ (SeamCropRows p coreWidth r J) ks rss := by
  induction ks generalizing v S with
  | nil => exact ⟨[],v,S,1,rfl,by simp,Exec.act _ _,by simp,rfl,rfl,rfl,fun _ _ => rfl,.nil⟩
  | cons k ks ih =>
    have hr := hreg k (by simp)
    have hr' := hr
    regs_ne hr'
    obtain ⟨rs,v₁,M,n₁,hu₁,hn₁,he₁,hd₁,hi₁,ho₁,hl₁,hframe₁,hlen,hgood⟩ := retainedSeamArchive_exec (body := body)
      clock clockSave sourceSave (skip k) (count k) src dst savedSkip saved tmp rows width retireCount trash retireTmp hr
      v S p coreWidth k r J output hproduced (hstart k (by simp)) hsrc hclock
      (hskip k (by simp)) (hcount k (by simp)) hrows hwidth hclean
    have hn₁' : n₁ ≤ 80*(r.inputs.length*s*(2*p+13))+14 := by
      rw [ExactCoreProduced.full_output_length hproduced] at hn₁
      exact hn₁.trans (retainedSeamArchiveCost_linear _ _ _ _ _ (Nat.pos_of_ne_zero (NeZero.ne s))
        (by omega) (hstart k (by simp)) (by unfold coreLength; exact (Nat.min_le_right _ _).trans (Nat.sub_le _ _)))
    have hcleanM : ∀ i ∈ [clockSave,sourceSave,savedSkip,saved,tmp,retireCount,trash,retireTmp], M.R i = [] := by
      intro i hi
      have hoff : i ≠ dst := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals first | assumption | (apply Ne.symm; assumption)
      rw [hframe₁ i hoff]; exact hclean i hi
    obtain ⟨rss,v₂,F,n₂,hu₂,hn₂,he₂,hd₂,hi₂,ho₂,hl₂,hframe₂,hgood₂⟩ := ih
      (fun j hj => hreg j (by simp [hj])) (fun j hj => hstart j (by simp [hj])) v₁ M
      (by rw [hframe₁ src ‹src ≠ dst›]; exact hsrc)
      (by rw [hframe₁ clock ‹clock ≠ dst›]; exact hclock)
      (by
        intro j hj
        have hrj := hreg j (by simp [hj])
        regs_ne hrj
        rw [hframe₁ (skip j) ‹skip j ≠ dst›]; exact hskip j (by simp [hj]))
      (by
        intro j hj
        have hrj := hreg j (by simp [hj])
        regs_ne hrj
        rw [hframe₁ (count j) ‹count j ≠ dst›]; exact hcount j (by simp [hj]))
      (by rw [hframe₁ rows ‹dst ≠ rows›.symm]; exact hrows)
      (by rw [hframe₁ width ‹dst ≠ width›.symm]; exact hwidth) hcleanM
    refine ⟨rs::rss,v₂,F,n₁+n₂,hu₂.trans hu₁,?_,Exec.seq he₁ he₂,?_,hi₂.trans hi₁,ho₂.trans ho₁,hl₂.trans hl₁,?_,.cons ⟨hlen,hgood⟩ hgood₂⟩
    · simp only [List.length_cons]; nlinarith only [hn₁',hn₂]
    · rw [hd₂,hd₁]
      simp only [List.reverse_cons,List.map_append,List.map_cons,List.map_nil,List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil,List.append_assoc]
    · intro i hi; exact (hframe₂ i hi).trans (hframe₁ i hi)

theorem retainedSeamCrops_native
    (clock clockSave sourceSave src dst savedSkip saved tmp rows width retireCount trash retireTmp : Fin T)
    (skip count : ℕ → Fin T) (ks : List ℕ) :
    mnNativePushBound 2 (retainedSeamCrops (P := P) (Q := Q) (A := A) (U := U)
      clock clockSave sourceSave src dst savedSkip saved tmp rows width retireCount trash retireTmp skip count ks) := by
  induction ks with
  | nil => simp [retainedSeamCrops,mnNativePushBound,mnActPush]
  | cons k ks ih => exact ⟨retainedSeamArchive_native _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,ih⟩

theorem retainedSeamCrops_within
    {clock clockSave sourceSave src dst savedSkip saved tmp rows width retireCount trash retireTmp : Fin T}
    {skip count : ℕ → Fin T} {ks : List ℕ}
    {v v' : HS T Q A U} {S F : Stacks T A} {n bound : ℕ}
    (he : Exec body (retainedSeamCrops clock clockSave sourceSave src dst savedSkip saved tmp rows width retireCount trash retireTmp skip count ks)
      (mk v S) n (mk v' F)) (hn : n ≤ bound) (depth : ℕ) :
    ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+2*bound) depth
      (retainedSeamCrops clock clockSave sourceSave src dst savedSkip saved tmp rows width retireCount trash retireTmp skip count ks)
      (mk v S) n (mk v' F) := by
  exact mn_native_exec_within he 2 (retainedSeamCrops_native _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) depth _ (by omega)

/-- Only the first and last two cores can require the full-period fallback.
For any such list, all repeated scans and backups remain linear in volume. -/
theorem retainedSeamCrops_three_cost (ks : List ℕ) (hcount : ks.length ≤ 3) (volume : ℕ) :
    ks.length*(80*volume+14)+1 ≤ 240*volume+43 := by
  have h := Nat.mul_le_mul_right (80*volume+14) hcount
  nlinarith only [h]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
