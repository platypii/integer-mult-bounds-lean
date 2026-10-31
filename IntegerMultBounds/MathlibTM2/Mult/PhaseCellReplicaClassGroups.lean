module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedReplicaPublication
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCorePublicationGroups
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaPublicationAccuracy

/-! A class-major publication schedule matches the actual transpose archives.
Each class publishes all replicas before the next class, borrowing the same
replica clock and deriving all subsequent readiness from the restored frame. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A s width B : ℕ} {P U : Type} {src dst : Fin T}

def replicaClassGroupsProgram (plans : CorePublicationClass s width → PreparedPublicationPlan T src dst)
    (clock lineRows : Fin T) : List (CorePublicationClass s width) → Pr P T Q A U
  | [] => .act .done
  | g::gs => .seq ((plans g).replicaProgram clock lineRows) (replicaClassGroupsProgram plans clock lineRows gs)

def replicaClassGroupsCost (B w : ℕ) (missing : CorePublicationClass s width → ℕ)
    (gs : List (CorePublicationClass s width)) :=
  (gs.map (fun g => replicaPublicationCost B s (missing g) g.length w+37*s*w+6*B+31)).sum+1

theorem replicaClassGroups_exec (body : P → Pr P T Q A U)
    (plans : CorePublicationClass s width → PreparedPublicationPlan T src dst) (clock lineRows : Fin T)
    (gs : List (CorePublicationClass s width))
    (hreg : ∀ g ∈ gs, ((plans g).support++[src,dst,clock,lineRows]).Nodup)
    (w : ℕ) (hw : 0 < width) (hw1 : 1 ≤ w)
    (rows : CorePublicationClass s width → Fin B → ℕ → List GaussianInt)
    (padded : CorePublicationClass s width → Fin B → List (List GaussianInt))
    (missing : CorePublicationClass s width → ℕ) (borrowed : CorePublicationClass s width → List (Fin (A+4)))
    (hrows : ∀ g ∈ gs, ∀ j k, k ∈ g.indices → (rows g j k).length = g.length)
    (hpadded : ∀ g ∈ gs, ∀ j row, row ∈ padded g j → row.length = g.length)
    (hcount : ∀ g ∈ gs, ∀ j, missing g+g.indices.length = (padded g j).length)
    (hreal : ∀ g ∈ gs, ∀ j, (padded g j).flatten.drop (missing g*g.length) = (g.indices.map (rows g j)).flatten)
    (ambient : Fin B → List (Fin (A+4))) (hambient : ∀ j, (ambient j).length = s*w)
    (sourceTail outputTail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hready : ∀ g ∈ gs, (plans g).Ready (coreSubsetPublicationWindows s width g.length hw g.indices g.sublist)
      w (missing g) (borrowed g) S)
    (hclock : (S.R clock).length = B) (hline : (S.R lineRows).length = s)
    (hsrc : S.R src = gs.flatMap (fun g => (List.ofFn fun j => cstream A w (padded g j).flatten).flatten)++sourceTail)
    (hdst : S.R dst = (List.ofFn ambient).flatten++outputTail) :
    ∃ v' F n, v'.user = v.user ∧ n ≤ replicaClassGroupsCost B w missing gs ∧
      Exec body (replicaClassGroupsProgram plans clock lineRows gs) (mk v S) n (mk v' F) ∧
      F.R src = sourceTail ∧
      F.R dst = (List.ofFn fun j => corePublicationGroupsOutput w hw (fun g => rows g j) gs (ambient j)).flatten++outputTail ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      ∀ i, i ≠ src → i ≠ dst → F.R i = S.R i := by
  induction gs generalizing ambient v S with
  | nil =>
    refine ⟨v,S,1,rfl,by simp [replicaClassGroupsCost],Exec.act _ _,?_,?_,rfl,rfl,rfl,fun _ _ _ => rfl⟩
    · simpa using hsrc
    · simpa only [corePublicationGroupsOutput] using hdst
  | cons g gs ih =>
    let windows := coreSubsetPublicationWindows s width g.length hw g.indices g.sublist
    let replicas := List.ofFn (fun j : Fin B => ({paddedRows := padded g j,rows := g.indices.map (rows g j),ambient := ambient j} : PublicationReplica A))
    have hv : ∀ r ∈ replicas, r.Valid windows w (missing g) := by
      intro r hr
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hr
      refine ⟨?_,?_,hpadded g (by simp) j,?_,hreal g (by simp) j,hambient j⟩
      · simp [windows,coreSubsetPublicationWindows,PublicationWindows.restrict]
      · intro row hr
        obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hr
        exact hrows g (by simp) j k hk
      · simpa only [List.length_map] using hcount g (by simp) j
    let tail := gs.flatMap (fun g => (List.ofFn fun j => cstream A w (padded g j).flatten).flatten)++sourceTail
    have hsrc' : S.R src = replicas.flatMap (PublicationReplica.input w)++tail := by
      simpa only [replicas,PublicationReplica.input,List.flatMap,List.map_ofFn,Function.comp_def,
        List.flatMap_cons,List.map_cons,List.flatten_cons,List.append_assoc,tail] using hsrc
    have hdst' : S.R dst = replicas.flatMap PublicationReplica.ambient++outputTail := by
      simpa only [replicas,List.flatMap,List.map_ofFn,Function.comp_def] using hdst
    obtain ⟨v₁,M,n₁,hu₁,hn₁,he₁,hs,hd,hi,ho,hl,hframe⟩ := (plans g).replica_exec clock lineRows (hreg g (by simp))
      windows w (missing g) hw1 replicas hv tail outputTail (borrowed g) v S (hready g (by simp)) hsrc' hdst'
      (by simpa only [replicas,List.length_ofFn] using hclock) hline
    let ambient₁ := fun j => g.output w hw (rows g j) (ambient j)
    have hambient₁ : ∀ j, (ambient₁ j).length = s*w := by
      intro j; exact g.output_length w hw (rows g j) (hrows g (by simp) j) (ambient j) (hambient j)
    have hclockOff : clock ≠ src ∧ clock ≠ dst ∧ lineRows ≠ src ∧ lineRows ≠ dst := by
      have hr := hreg g (by simp)
      have hsuffix := (List.nodup_append.mp hr).2.1
      simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hsuffix
      exact ⟨Ne.symm hsuffix.1.2.1,Ne.symm hsuffix.2.1.1,Ne.symm hsuffix.1.2.2,Ne.symm hsuffix.2.1.2⟩
    obtain ⟨v₂,F,n₂,hu₂,hn₂,he₂,hs',hd',hi',ho',hl',hframe'⟩ := ih (fun g hg => hreg g (by simp [hg]))
      (fun g hg => hrows g (by simp [hg])) (fun g hg => hpadded g (by simp [hg]))
      (fun g hg => hcount g (by simp [hg])) (fun g hg => hreal g (by simp [hg])) ambient₁ hambient₁ v₁ M
      (by
        intro g' hg'
        apply (hready g' (by simp [hg'])).of_frame
        intro i hi
        exact hframe i ((plans g').support_off hi).1 ((plans g').support_off hi).2)
      (by rw [hframe _ hclockOff.1 hclockOff.2.1]; exact hclock)
      (by rw [hframe _ hclockOff.2.2.1 hclockOff.2.2.2]; exact hline)
      hs (by simpa only [replicas,PublicationReplica.output,PublicationReplica.words,List.flatMap,List.map_ofFn,
        Function.comp_def,ambient₁,CorePublicationClass.output,windows] using hd)
    refine ⟨v₂,F,n₁+n₂,hu₂.trans hu₁,?_,Exec.seq he₁ he₂,hs',?_,hi'.trans hi,ho'.trans ho,hl'.trans hl,?_⟩
    · simp only [replicas,List.length_ofFn] at hn₁
      simp only [replicaClassGroupsCost,List.map_cons,List.sum_cons] at hn₂ ⊢
      omega
    · simpa only [corePublicationGroupsOutput,ambient₁] using hd'
    · intro i his hid; exact (hframe' i his hid).trans (hframe i his hid)

theorem replicaClassGroups_native
    (plans : CorePublicationClass s width → PreparedPublicationPlan T src dst) (clock lineRows : Fin T)
    (gs : List (CorePublicationClass s width)) :
    mnNativePushBound 2 (replicaClassGroupsProgram (P := P) (Q := Q) (A := A) (U := U) plans clock lineRows gs) := by
  induction gs with
  | nil => simp [replicaClassGroupsProgram,mnNativePushBound,mnActPush]
  | cons g gs ih => exact ⟨(plans g).replica_native clock lineRows,ih⟩

theorem replicaClassGroups_within {body : P → Pr P T Q A U}
    {plans : CorePublicationClass s width → PreparedPublicationPlan T src dst} {clock lineRows : Fin T}
    {gs : List (CorePublicationClass s width)} {missing : CorePublicationClass s width → ℕ}
    {w n : ℕ} {v v' : HS T Q A U} {S F : Stacks T A}
    (he : Exec body (replicaClassGroupsProgram plans clock lineRows gs) (mk v S) n (mk v' F))
    (hn : n ≤ replicaClassGroupsCost B w missing gs) (depth : ℕ) :
    ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+2*replicaClassGroupsCost B w missing gs) depth
      (replicaClassGroupsProgram plans clock lineRows gs) (mk v S) n (mk v' F) := by
  exact mn_native_exec_within he 2 (replicaClassGroups_native plans clock lineRows gs) depth _ (by omega)

/-- The returned physical replica slices have the same global error as their
certified rows. The untouched output suffix does not enter any replica reader. -/
theorem replicaClassGroups_accuracy [NeZero s] (q w : ℕ) (hw : 0 < width)
    (gs : List (CorePublicationClass s width))
    (rows : CorePublicationClass s width → Fin B → ℕ → List GaussianInt)
    (hrows : ∀ g ∈ gs, ∀ j k, k ∈ g.indices → (rows g j k).length = g.length)
    (hcover : ∀ k ∈ IntegerMultBounds.NLogN.PhaseCellMatrix.coreIndices s width, ∃ g ∈ gs, k ∈ g.indices)
    (ambient : Fin B → List (Fin (A+4))) (hambient : ∀ j, (ambient j).length = s*w)
    (target : Fin B → ZMod s → ℂ) (error : ℝ)
    (hgood : ∀ g ∈ gs, ∀ j k, k ∈ g.indices → PhaseCellInterface.ErrorOn
      (IntegerMultBounds.NLogN.PhaseCellMatrix.ownedCore s width k)
      (packedIntervalRead q w (IntegerMultBounds.NLogN.PhaseCellMatrix.coreStart width k) (cstream A w (rows g j k))) (target j) error)
    (raw outputTail : List (Fin (A+4)))
    (hraw : raw = (List.ofFn fun j => corePublicationGroupsOutput w hw (fun g => rows g j) gs (ambient j)).flatten++outputTail) :
    ∀ j : Fin B, ∀ i, ‖pairedCellRead q w (raw.drop (j.val*(s*w))) i-target j i‖ ≤ error := by
  let output := fun j => corePublicationGroupsOutput w hw (fun g => rows g j) gs (ambient j)
  have hlength (j : Fin B) : (output j).length = s*w :=
    corePublicationGroupsOutput_length w hw (fun g => rows g j) gs (fun g hg => hrows g hg j) (ambient j) (hambient j)
  have hlines : ∀ line ∈ List.ofFn output, line.length = s*w := by
    intro line hl
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hl
    exact hlength j
  intro j i
  have he := corePublicationGroupsOutput_error q w hw (fun g => rows g j) gs (fun g hg => hrows g hg j)
    hcover (target j) error (fun g hg => hgood g hg j) (ambient j) (hambient j) i
  have hword := fixedLines_word (s*w) w (List.ofFn output) hlines outputTail j.val (i.val*w)
    (by simp only [List.length_ofFn]; exact j.isLt) (by
      have hm := Nat.mul_le_mul_right w (Nat.succ_le_of_lt i.val_lt)
      simpa only [Nat.succ_mul] using hm)
  rw [hraw]
  change ‖value q (decodeWord (((((List.ofFn output).flatten++outputTail).drop (j.val*(s*w))).drop (i.val*w)).take w))-target j i‖ ≤ error
  rw [hword]
  simpa only [List.getElem_ofFn,pairedCellRead,output] using he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
