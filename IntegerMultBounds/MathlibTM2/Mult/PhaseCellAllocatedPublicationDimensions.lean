module

public import IntegerMultBounds.MathlibTM2.Host.SharedRegisterPlacement
public import IntegerMultBounds.MathlibTM2.Host.EmbedStock
public import IntegerMultBounds.MathlibTM2.Host.EmbedUpdate
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDyadicGatherCapacity
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterchangeHeaderStock

/-! Reuse the checked gather-dimension producer after origin counting. Only
replica/count inputs and the three generated masters occupy caller ports. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {T Q K A : ℕ} {P U : Type}

def publicationCountIndex (j : Fin 5) : Fin tapeCount := headerReg (![83,80,84,85,81] j)

def publicationCountRole (i : Fin tapeCount) : Option (Fin 5) :=
  if i = headerReg 83 then some 0 else if i = headerReg 80 then some 1 else
  if i = headerReg 84 then some 2 else if i = headerReg 85 then some 3 else
  if i = headerReg 81 then some 4 else none

theorem publicationCountRole_index (j : Fin 5) : publicationCountRole (publicationCountIndex j) = some j := by
  fin_cases j <;> simp [publicationCountRole,publicationCountIndex,headerReg_injective.eq_iff]

theorem publicationCountRole_recovers (i : Fin tapeCount) (j : Fin 5)
    (hi : publicationCountRole i = some j) : i = publicationCountIndex j := by
  unfold publicationCountRole at hi
  split_ifs at hi <;> simp_all only [Option.some.injEq,reduceCtorEq] <;> subst_vars <;> simp [publicationCountIndex]

def publicationCountPlacement (src : Fin 5 → Fin T) : Fin tapeCount → Fin (T+tapeCount) :=
  sharedRegisterPlacement (Fin.natAdd T) (Fin.castAdd tapeCount ∘ src) publicationCountRole

private theorem private_ne_prefix (i : Fin tapeCount) (k : Fin T) :
    Fin.natAdd T i ≠ Fin.castAdd tapeCount k := by
  intro he
  have hv := congrArg (fun j : Fin (T+tapeCount) => j.val) he
  simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
  have hk := k.isLt
  omega

theorem publicationCountPlacement_shared (src : Fin 5 → Fin T) (j : Fin 5) :
    publicationCountPlacement src (publicationCountIndex j) = Fin.castAdd tapeCount (src j) := by
  simp only [publicationCountPlacement,sharedRegisterPlacement,publicationCountRole_index,Function.comp_apply]

theorem publicationCountPlacement_private (src : Fin 5 → Fin T) (i : Fin tapeCount)
    (hi : publicationCountRole i = none) : publicationCountPlacement src i = Fin.natAdd T i := by
  simp only [publicationCountPlacement,sharedRegisterPlacement,hi]

theorem publicationCountPlacement_injective (src : Fin 5 → Fin T) (hinj : Function.Injective src) :
    Function.Injective (publicationCountPlacement src) := by
  apply sharedRegisterPlacement_injective _ (Fin.natAdd_injective _ _) _ ((Fin.castAdd_injective _ _).comp hinj)
  · intro i j; exact private_ne_prefix i (src j)
  · intro i k j hi hk
    exact (publicationCountRole_recovers i j hi).trans (publicationCountRole_recovers k j hk).symm

def publicationDimensionsProgram (src : Fin 5 → Fin T) : Pr P (T+tapeCount) Q (prime+K) U :=
  embProg (publicationCountPlacement src) Empty.elim (gatherDimensionsProgram (P := Empty))

def publicationDimensionsTimeCost (b N : ℕ) :=
  ((19*2^b+10)+(19*N+9))+(4*2^(Nat.clog 2 N)+9*Nat.clog 2 N+5)

def publicationDimensionsLoaded (src : Fin 5 → Fin T) (b N : ℕ)
    (S : Stacks (T+tapeCount) A) :=
  {S with R := (Function.update (Function.update (Function.update S.R
    (Fin.castAdd tapeCount (src 2)) (List.replicate b tick))
    (Fin.castAdd tapeCount (src 3)) (List.replicate (Nat.clog 2 N) tick))
    (Fin.castAdd tapeCount (src 4)) (List.replicate (2^(Nat.clog 2 N)) tick))}

theorem publicationDimensionsLoaded_off (src : Fin 5 → Fin T) (b N : ℕ)
    (S : Stacks (T+tapeCount) A) (k : Fin (T+tapeCount))
    (h2 : k ≠ Fin.castAdd tapeCount (src 2)) (h3 : k ≠ Fin.castAdd tapeCount (src 3))
    (h4 : k ≠ Fin.castAdd tapeCount (src 4)) :
    (publicationDimensionsLoaded src b N S).R k = S.R k := by
  simp only [publicationDimensionsLoaded,Function.update_of_ne h2,Function.update_of_ne h3,Function.update_of_ne h4]

theorem publicationDimensionsLoaded_update_off (src : Fin 5 → Fin T) (b N : ℕ)
    (S : Stacks (T+tapeCount) A) (k : Fin T) (xs : List (Fin (A+4)))
    (h2 : src 2 ≠ k) (h3 : src 3 ≠ k) (h4 : src 4 ≠ k) :
    publicationDimensionsLoaded src b N {S with R := Function.update S.R (Fin.castAdd tapeCount k) xs} =
      {publicationDimensionsLoaded src b N S with R := (Function.update
        (publicationDimensionsLoaded src b N S).R (Fin.castAdd tapeCount k) xs)} := by
  refine Stacks.ext rfl rfl rfl ?_
  simp only [publicationDimensionsLoaded]
  rw [Function.update_comm ((Fin.castAdd_injective _ _).ne h2).symm,
    Function.update_comm ((Fin.castAdd_injective _ _).ne h3).symm,
    Function.update_comm ((Fin.castAdd_injective _ _).ne h4).symm]

theorem publicationDimensions_exec_within (body : P → Pr P (T+tapeCount) Q (prime+K) U)
    (src : Fin 5 → Fin T) (hinj : Function.Injective src) (b N depth : ℕ)
    (v : HS (T+tapeCount) Q (prime+K) U) (S : Stacks (T+tapeCount) (prime+K))
    (hreplicas : (S.R (Fin.castAdd tapeCount (src 0))).length = 2^b)
    (hrows : (S.R (Fin.castAdd tapeCount (src 1))).length = N)
    (houtputs : ∀ j ∈ [(2 : Fin 5),3,4], S.R (Fin.castAdd tapeCount (src j)) = [])
    (hprivate : ∀ i, S.R (Fin.natAdd T i) = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ publicationDimensionsTimeCost b N ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+2*publicationDimensionsTimeCost b N) depth
        (publicationDimensionsProgram src) (mk v S) n (mk v' (publicationDimensionsLoaded src b N S)) := by
  let e := publicationCountPlacement src
  have he : Function.Injective e := publicationCountPlacement_injective src hinj
  have hread (j : Fin 5) : e (publicationCountIndex j) = Fin.castAdd tapeCount (src j) :=
    publicationCountPlacement_shared src j
  have hfresh (i : Fin 117) (hi : publicationCountRole (headerReg i) = none) :
      (embStk e S).R (headerReg i) = [] := by
    change S.R (e (headerReg i)) = []
    rw [show e (headerReg i) = Fin.natAdd T (headerReg i) from publicationCountPlacement_private src _ hi,hprivate]
  obtain ⟨w,n,hu,hn,hx⟩ := gatherDimensions_exec_within (body := fun f : Empty => nomatch f)
    b N depth (embDn e v) (embStk e S)
    (by
      change (S.R (e (publicationCountIndex 0))).length = _
      rw [hread]; exact hreplicas)
    (by
      change (S.R (e (publicationCountIndex 1))).length = _
      rw [hread]; exact hrows)
    (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · change S.R (e (publicationCountIndex 4)) = []; rw [hread]; exact houtputs 4 (by simp)
      · change S.R (e (publicationCountIndex 2)) = []; rw [hread]; exact houtputs 2 (by simp)
      · change S.R (e (publicationCountIndex 3)) = []; rw [hread]; exact houtputs 3 (by simp)
      all_goals apply hfresh; simp [publicationCountRole,headerReg_injective.eq_iff])
  obtain ⟨v',_,hu',hexe⟩ := exec_emb_ovr_within_stock (e := e) he (body' := body) (ι := Empty.elim)
    (fun f => nomatch f) hx v rfl S rfl
  rw [embOvr_updateR_updateR_updateR he] at hexe
  have h84 : e (headerReg 84) = Fin.castAdd tapeCount (src 2) := hread 2
  have h85 : e (headerReg 85) = Fin.castAdd tapeCount (src 3) := hread 3
  have h81 : e capacityRows = Fin.castAdd tapeCount (src 4) := hread 4
  rw [h84,h85,h81] at hexe
  refine ⟨v',n,?_,?_,?_⟩
  · have huser : w.user = v.user := by simpa only [embDn_user] using hu
    exact hu'.trans huser
  · simpa only [publicationDimensionsTimeCost] using hn
  · simpa only [publicationDimensionsTimeCost,publicationDimensionsProgram,publicationDimensionsLoaded,
    Nat.mul_add,e] using hexe
theorem publicationDimensions_after_update_exec_within (body : P → Pr P (T+tapeCount) Q (prime+K) U)
    (src : Fin 5 → Fin T) (hinj : Function.Injective src) (b N depth : ℕ)
    (k : Fin T) (xs : List (Fin (prime+K+4))) (hoff : ∀ j, src j ≠ k)
    (v : HS (T+tapeCount) Q (prime+K) U) (S : Stacks (T+tapeCount) (prime+K))
    (hreplicas : (S.R (Fin.castAdd tapeCount (src 0))).length = 2^b)
    (hrows : (S.R (Fin.castAdd tapeCount (src 1))).length = N)
    (houtputs : ∀ j ∈ [(2 : Fin 5),3,4], S.R (Fin.castAdd tapeCount (src j)) = [])
    (hprivate : ∀ i, S.R (Fin.natAdd T i) = []) :
    let F : Stacks (T+tapeCount) (prime+K) := {S with R := Function.update S.R (Fin.castAdd tapeCount k) xs}
    let D := publicationDimensionsLoaded src b N S
    ∃ v' n, v'.user = v.user ∧ n ≤ publicationDimensionsTimeCost b N ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v F)+depth+2*publicationDimensionsTimeCost b N) depth
        (publicationDimensionsProgram src) (mk v F) n
        (mk v' {D with R := Function.update D.R (Fin.castAdd tapeCount k) xs}) := by
  dsimp only
  let F : Stacks (T+tapeCount) (prime+K) := {S with R := Function.update S.R (Fin.castAdd tapeCount k) xs}
  have hread (j : Fin 5) : F.R (Fin.castAdd tapeCount (src j)) = S.R (Fin.castAdd tapeCount (src j)) := by
    simp only [F,Function.update_of_ne ((Fin.castAdd_injective _ _).ne (hoff j))]
  obtain ⟨v',n,hu,hn,hx⟩ := publicationDimensions_exec_within body src hinj b N depth v F
    (by rw [hread]; exact hreplicas) (by rw [hread]; exact hrows)
    (by intro j hj; rw [hread]; exact houtputs j hj)
    (by intro i; simpa only [F,Function.update_of_ne (private_ne_prefix i k)] using hprivate i)
  rw [publicationDimensionsLoaded_update_off src b N S k xs (hoff 2) (hoff 3) (hoff 4)] at hx
  exact ⟨v',n,hu,hn,hx⟩

theorem retirePublicationDimensions_exec_within (body : P → Pr P (T+tapeCount) Q (prime+K) U)
    (src : Fin 5 → Fin T) (hinj : Function.Injective src) (b N : ℕ) (output : Fin T)
    (hoff : ∀ j ∈ [(2 : Fin 5),3,4], src j ≠ output)
    (ys : List (Fin (prime+K+4))) (v : HS (T+tapeCount) Q (prime+K) U) (S : Stacks (T+tapeCount) (prime+K))
    (hblank : ∀ j ∈ [(2 : Fin 5),3,4], S.R (Fin.castAdd tapeCount (src j)) = []) (depth : ℕ) :
    let D := publicationDimensionsLoaded src b N S
    let F : Stacks (T+tapeCount) (prime+K) := {D with R := Function.update D.R (Fin.castAdd tapeCount output) ys}
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v F)+depth+0) depth
        (clearWords [Fin.castAdd tapeCount (src 2),Fin.castAdd tapeCount (src 3),Fin.castAdd tapeCount (src 4)])
        (mk v F) (2*(b+Nat.clog 2 N+2^(Nat.clog 2 N))+7)
        (mk v' {S with R := Function.update S.R (Fin.castAdd tapeCount output) ys}) := by
  dsimp only
  let D := publicationDimensionsLoaded src b N S
  let F : Stacks (T+tapeCount) (prime+K) := {D with R := Function.update D.R (Fin.castAdd tapeCount output) ys}
  let ports := [Fin.castAdd tapeCount (src 2),Fin.castAdd tapeCount (src 3),Fin.castAdd tapeCount (src 4)]
  have hcast : Function.Injective (fun j => Fin.castAdd tapeCount (src j)) := (Fin.castAdd_injective _ _).comp hinj
  have hne (j : Fin 5) (hj : j ∈ [(2 : Fin 5),3,4]) : Fin.castAdd tapeCount (src j) ≠ Fin.castAdd tapeCount output :=
    (Fin.castAdd_injective _ _).ne (hoff j hj)
  obtain ⟨v',hu,hx⟩ := clearWords_exec (body := body) ports (by simp [ports,List.nodup_cons,hcast.eq_iff]) v F
  have hcost : 2*(ports.map (fun j => (F.R j).length)).sum+2*ports.length+1 =
      2*(b+Nat.clog 2 N+2^(Nat.clog 2 N))+7 := by
    simp [ports,F,D,publicationDimensionsLoaded,hne 2 (by simp),hne 3 (by simp),hne 4 (by simp),hcast.eq_iff]
    omega
  rw [hcost] at hx
  have hend : {F with R := fun j => if j ∈ ports then [] else F.R j} =
      {S with R := Function.update S.R (Fin.castAdd tapeCount output) ys} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext j
    by_cases hj : j ∈ ports
    · simp only [ports,List.mem_cons,List.not_mem_nil,or_false] at hj
      rcases hj with rfl | rfl | rfl
      · simp [ports,hne 2 (by simp),hblank 2 (by simp)]
      · simp [ports,hne 3 (by simp),hblank 3 (by simp)]
      · simp [ports,hne 4 (by simp),hblank 4 (by simp)]
    · have hrest := hj
      simp only [ports,List.mem_cons,List.not_mem_nil,or_false,not_or] at hrest
      simp [hj,F,D,publicationDimensionsLoaded,Function.update_apply,hrest.1,hrest.2.1,hrest.2.2]
  rw [hend] at hx
  exact ⟨v',hu,mn_native_exec_within hx 0 (clearWords_native _) depth _ (by simp only [F,D,Nat.zero_mul,Nat.add_zero]; exact le_rfl)⟩


end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
