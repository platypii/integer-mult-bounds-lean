module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCommonClassGeometry
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCopyWordHeaders
public import IntegerMultBounds.MathlibTM2.StackStockComposition
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterchangeHeaderStock

/-! Borrow the shared seed table to generate two class words, export them,
then restore the seed. Only the two owned binary words survive setup. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CommonClassGeometry
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv ScalarPlacement.ComputedClassBanks
variable {T Q A : ℕ} {P U : Type}

def restoreCode : TblCode 13 := tblBlock 13 [.zero 10] (.zero 11)

def masterCopies (rg : TblR 13 → Fin T) (core halo : Fin T) : List (Fin T × Fin T) :=
  [(rg (.v 10),core),(rg (.v 11),halo)]

def masterProgram (rg : TblR 13 → Fin T) (clipped : Bool) (core halo : Fin T) : Pr P T Q A U :=
  .seq (tblCompile rg (code clipped))
    (.seq (copyWordHeaders (rg (.z 0)) (rg (.z 1)) (masterCopies rg core halo)) (tblCompile rg restoreCode))

def masterTimeCost (D : ℕ) := 5*tblC D 0+12*D+13

def masterStock (D : ℕ) := 3*(3*tblC D 0)+(2*(12*D+13)+3*(2*tblC D 0))

def masterLoaded (core halo : Fin T) (D : ℕ) (clipped : Bool) (s width radius : ℕ) (S : Stacks T A) :=
  {S with R := (Function.update (Function.update S.R core (binSyms D (coreRows clipped s width)))
    halo (binSyms D (haloRows clipped s width radius)))}

/-- The generated words complete the existing twelve-master input ABI. -/
theorem masterLoaded_words (masters : Fin 12 → Fin T) (hinj : Function.Injective masters)
    (D : ℕ) (clipped : Bool) (p u l target s t B W N radius width : ℕ) (S : Stacks T A)
    (hprefix : ∀ j, j ≠ 10 → j ≠ 11 → S.R (masters j) =
      binSyms D (seedValues p u l target s t B W N radius width (Fin.castAdd 1 j))) :
    ∀ j, (masterLoaded (masters 10) (masters 11) D clipped s width radius S).R (masters j) =
      binSyms D (commonInputValues p u l target s t B W N radius (haloRows clipped s width radius) j) := by
  intro j
  by_cases h10 : j = 10
  · subst j
    simp [masterLoaded,hinj.eq_iff,commonInputValues,Matrix.vecAppend_eq_ite,haloRows]
  by_cases h11 : j = 11
  · subst j
    simp [masterLoaded,commonInputValues,Matrix.vecAppend_eq_ite]
  simp only [masterLoaded,Function.update_of_ne (hinj.ne h10),Function.update_of_ne (hinj.ne h11)]
  rw [hprefix j h10 h11,seed_prefix clipped p u l target s t B W N radius width j h10 h11]

private theorem restore_do (D s width radius : ℕ) (clipped : Bool) (st : TblSt 13 A)
    (h10 : st.val 10 = 0) (h11 : st.val 11 = 0) :
    TblDo A D 0 restoreCode (loaded clipped s width radius st) (fun st' => st' = st) 2 := by
  rcases st with ⟨values,acc⟩
  change values 10 = 0 at h10
  change values 11 = 0 at h11
  apply TblDo.block
  · simp [tblFitsList,TblIns.fits]
  · change (⟨_,acc⟩ : TblSt 13 A) = ⟨values,acc⟩
    congr 1
    funext i
    by_cases hi10 : i = 10
    · subst i; simp [TblIns.exact,loaded,h10]
    by_cases hi11 : i = 11
    · subst i; simp [TblIns.exact,loaded,h11]
    · simp [TblIns.exact,loaded,hi10,hi11]

theorem master_exec_within (body : P → Pr P T Q A U) (rg : TblR 13 → Fin T) (hinj : Function.Injective rg)
    (core halo : Fin T) (hne : core ≠ halo)
    (hcoreOff : ∀ r, rg r ≠ core) (hhaloOff : ∀ r, rg r ≠ halo)
    (clipped : Bool) (D s width radius : ℕ) (st : TblSt 13 A)
    (hs : st.val 4 = s) (hw : st.val 12 = width) (hr : st.val 9 = radius)
    (h10 : st.val 10 = 0) (h11 : st.val 11 = 0)
    (hwidth : 0 < width) (hfit : width+2*radius < 2^D) (hvalues : ∀ j, st.val j < 2^D)
    (wl : List (Fin (A+4))) (hwl : wl.length = D)
    (v : HS T Q A U) (S : Stacks T A) (hholds : tblHolds rg S (tblRho D wl [] st))
    (hcoreBlank : S.R core = []) (hhaloBlank : S.R halo = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ masterTimeCost D ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+masterStock D) depth
        (masterProgram rg clipped core halo) (mk v S) n
        (mk v' (masterLoaded core halo D clipped s width radius S)) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,hM,he₁⟩ := exec_within body rg hinj clipped D s width radius st hs hw hr
    hwidth hfit hvalues wl hwl v S hholds depth
  let M : Stacks T A := {S with R := (Function.update (Function.update S.R (rg (.v 10))
    (binSyms D (coreRows clipped s width))) (rg (.v 11)) (binSyms D (haloRows clipped s width radius)))}
  have hm10 : M.R (rg (.v 10)) = binSyms D (coreRows clipped s width) := hM (.v 10)
  have hm11 : M.R (rg (.v 11)) = binSyms D (haloRows clipped s width radius) := hM (.v 11)
  have hmcore : M.R core = [] := by simp [M,(hcoreOff (.v 10)).symm,(hcoreOff (.v 11)).symm,hcoreBlank]
  have hmhalo : M.R halo = [] := by simp [M,(hhaloOff (.v 10)).symm,(hhaloOff (.v 11)).symm,hhaloBlank]
  obtain ⟨v₂,hu₂,he₂⟩ := copyWordHeaders_exec (body := body) (rg (.z 0)) (rg (.z 1)) (masterCopies rg core halo)
    (by
      intro r hr
      simp only [masterCopies,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl <;> simp [List.nodup_cons,hinj.eq_iff,hcoreOff,hhaloOff,Ne.symm])
    (by
      intro r hr p hp
      simp only [masterCopies,List.mem_cons,List.not_mem_nil,or_false] at hr hp
      rcases hr with rfl | rfl <;> rcases hp with rfl | rfl
      all_goals apply Ne.symm; first | exact hcoreOff _ | exact hhaloOff _)
    M.R v₁ M (by intro r _; rfl) (hM (.z 0)) (hM (.z 1))
  let C : Stacks T A := {M with R := (Function.update (Function.update M.R core (binSyms D (coreRows clipped s width)))
    halo (binSyms D (haloRows clipped s width radius)))}
  have hcost : ((masterCopies rg core halo).map (fun r => 6*(M.R r.1).length+6)).sum+1 = 12*D+13 := by
    simp [masterCopies,hm10,hm11,length_binSyms] <;> omega
  rw [hcost] at he₂
  have hcopyEnd : {M with R := copyWordHeadersR M.R (masterCopies rg core halo) M.R} = C := by
    simp [C,masterCopies,copyWordHeadersR,hm10,hm11,hmcore,hmhalo,hne.symm]
  rw [hcopyEnd] at he₂
  have hC (r) : C.R (rg r) = tblRho D wl [] (loaded clipped s width radius st) r := by
    simpa only [C,Function.update_of_ne (hcoreOff r),Function.update_of_ne (hhaloOff r)] using hM r
  have hloadedFit (j) : (loaded clipped s width radius st).val j < 2^D := by
    have hc := coreRows_le clipped s width hwidth
    by_cases hj11 : j = 11
    · subst j; simp only [loaded,Function.update_self,haloRows]; omega
    by_cases hj10 : j = 10
    · subst j; simp [loaded]; omega
    · simpa only [loaded,Function.update_of_ne hj11,Function.update_of_ne hj10] using hvalues j
  obtain ⟨st',heq,hrun⟩ := (restore_do D s width radius clipped st h10 h11).host (body := body) (w := 0)
    hinj wl [] hwl rfl (by simp) hloadedFit
  subst st'
  obtain ⟨v₃,F,n₃,hu₃,hn₃,he₃,hF,hframe⟩ := hrun v₂ C hC
  have hend : F = masterLoaded core halo D clipped s width radius S := by
    refine Stacks.ext hframe.1 hframe.2.1 hframe.2.2.1 ?_
    funext k
    by_cases hk : ∃ r, rg r = k
    · obtain ⟨r,rfl⟩ := hk
      rw [hF r]
      simpa only [masterLoaded,Function.update_of_ne (hcoreOff r),Function.update_of_ne (hhaloOff r)] using (hholds r).symm
    · have hne10 : k ≠ rg (.v 10) := by intro heq; exact hk ⟨.v 10,heq.symm⟩
      have hne11 : k ≠ rg (.v 11) := by intro heq; exact hk ⟨.v 11,heq.symm⟩
      rw [hframe.2.2.2 k (by intro r heq; exact hk ⟨r,heq⟩)]
      simp [C,M,masterLoaded,Function.update_apply,hne10,hne11]
  rw [hend] at he₃
  have hw₂ := mn_native_exec_within he₂ 2 (copyWordHeaders_native _ _ _) depth
    (mnSize (mk v₁ M)+depth+2*(12*D+13)) (by omega)
  have hw₃ := mn_native_exec_within he₃ 3 (tblCompile_native _ _) depth
    (mnSize (mk v₂ C)+depth+3*(2*tblC D 0)) (Nat.add_le_add_left (Nat.mul_le_mul_left 3 hn₃) _)
  refine ⟨v₃,n₁+((12*D+13)+n₃),hu₃.trans (hu₂.trans hu₁),?_,?_⟩
  · unfold masterTimeCost
    omega
  · exact mn_seq_within_add he₁ (mn_seq_within_add hw₂ hw₃)

/-- Retire the two owned class words after publication, preserving the ambient result. -/
theorem master_retire_exec_within (body : P → Pr P T Q A U) (core halo output : Fin T)
    (hne : core ≠ halo) (houtCore : output ≠ core) (houtHalo : output ≠ halo)
    (D : ℕ) (clipped : Bool) (s width radius : ℕ) (ys : List (Fin (A+4)))
    (v : HS T Q A U) (S : Stacks T A) (hcore : S.R core = []) (hhalo : S.R halo = []) (depth : ℕ) :
    let M := masterLoaded core halo D clipped s width radius S
    let F := {M with R := Function.update M.R output ys}
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v F)+depth+0) depth
        (clearWords [core,halo]) (mk v F) (4*D+5)
        (mk v' {S with R := Function.update S.R output ys}) := by
  dsimp only
  let M := masterLoaded core halo D clipped s width radius S
  let F := {M with R := Function.update M.R output ys}
  obtain ⟨v',hu,hx⟩ := clearWords_exec (body := body) [core,halo] (by simp [hne]) v F
  have hcost : 2*(([core,halo].map (fun j => (F.R j).length)).sum)+2*[core,halo].length+1 = 4*D+5 := by
    simp [F,M,masterLoaded,houtCore.symm,houtHalo.symm,hne,length_binSyms] <;> omega
  rw [hcost] at hx
  have hend : {F with R := fun j => if j ∈ [core,halo] then [] else F.R j} =
      {S with R := Function.update S.R output ys} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext j
    by_cases hjCore : j = core
    · subst j; simp [houtCore.symm,hcore]
    by_cases hjHalo : j = halo
    · subst j; simp [houtHalo.symm,hhalo]
    · simp [F,M,masterLoaded,hjCore,hjHalo,Function.update_apply]
  rw [hend] at hx
  exact ⟨v',hu,mn_native_exec_within hx 0 (clearWords_native _) depth _
    (by simp only [Nat.zero_mul,Nat.add_zero]; exact le_rfl)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CommonClassGeometry
