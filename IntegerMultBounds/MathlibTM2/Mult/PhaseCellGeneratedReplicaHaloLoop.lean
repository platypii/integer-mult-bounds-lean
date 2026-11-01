module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaHaloProblem

/-! The concrete accuracy, encoded-row and machine-bank invariant for all keys. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

structure ReplicaHaloLoopState (H : ReplicaHaloProblem s) (plan : ReplicaInteriorPlacement T)
    (dst : Fin T) (buffers : ReplicaLoopBuffers A) (allKeys keys : List ℕ) (S : Stacks T A) : Prop where
  remaining : ∀ L ∈ keys, L ∈ allKeys
  headers : ReplicaLoopHeaders H plan.gather buffers S
  bank : embStk weightCacheCoreReg (embStk plan.solver S) =
    releasedCellBank [] buffers.rhsTail buffers.solverOutputTail S.inp S.out
  cache : S.R (plan.solver 117) = buffers.cacheTail
  solverFresh : ∀ k ∈ [(118 : Fin 121),119,120], S.R (plan.solver k) = []
  input : S.inp = buffers.input
  output : S.out = buffers.output
  gatherLeft : (embStk plan.gather S).L = buffers.savedGather.L
  gatherFrame : ∀ k : Fin 126, k ≠ 87 → k ≠ 119 → S.R (plan.gather k) = buffers.savedGather.R k
  packets : S.R (plan.gather 87) = keys.flatMap (binSyms H.metadataWidth)++buffers.keyTail
  count : S.R (plan.gather 119) = List.replicate keys.length (tick : Fin (A+4))
  rows : ∃ rows : List (List (Fin (A+4))), rows.length = H.Fs.length ∧
    (∀ row ∈ rows, row.length = H.span*H.wordWidth) ∧
    (∀ row ∈ rows, EncodedRange A H.wordWidth H.precision (interiorOutputExponent H.p H.l H.target H.rhsExp) row) ∧
    S.R dst = rows.flatten++buffers.accumulatorTail
  accuracy : ∀ L ∈ allKeys, L ∉ keys → H.ClassAccuracy L (S.R dst)

theorem ReplicaHaloLoopState.gather_restored (H : ReplicaHaloProblem s) (plan : ReplicaInteriorPlacement T)
    (dst : Fin T) (buffers : ReplicaLoopBuffers A) (allKeys : List ℕ) (F : Stacks T A)
    (h : ReplicaHaloLoopState H plan dst buffers allKeys [] F) :
    embStk plan.gather F = {buffers.savedGather with
      inp := buffers.input
      out := buffers.output
      R := (Function.update (Function.update buffers.savedGather.R 87 buffers.keyTail) 119 [])} := by
  refine Stacks.ext h.input h.output h.gatherLeft ?_
  funext k
  by_cases h87 : k = 87
  · subst k
    simpa [embStk] using h.packets
  by_cases h119 : k = 119
  · subst k
    simpa [embStk] using h.count
  simpa [embStk,h87,h119] using h.gatherFrame k h87 h119

namespace ReplicaHaloProblem

def keyCost (H : ReplicaHaloProblem s) (L : ℕ) :=
  processGeneratedHaloReplicaKeyCost H.p H.l H.Fs.length H.metadataWidth H.origin H.span L s H.t H.u H.target H.rhsExp

noncomputable def keyWorkspace (H : ReplicaHaloProblem s) (hQ : SS.states ≤ Q) (R K L : ℕ) :=
  processGeneratedHaloReplicaKeyWorkspace (A := A) (U := U) hQ R K H.p H.l H.Fs.length H.metadataWidth
    H.origin H.span L s H.t H.u H.target H.rhsExp

end ReplicaHaloProblem

theorem replicaHaloLoop_step (H : ReplicaHaloProblem s) (plan : ReplicaInteriorPlacement T) (dst : Fin T)
    (hgd : ∀ i, plan.gather i ≠ dst) (hsd : ∀ i, plan.solver i ≠ dst)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (buffers : ReplicaLoopBuffers A) (allKeys : List ℕ)
    (hbounds : ∀ L ∈ allKeys, 0 < L ∧ L ≤ s ∧ L+L ≤ 2^H.l+1 ∧ L < 2^H.metadataWidth ∧ H.offsets L ≠ [])
    (R K : ℕ)
    (hpushR : mnProgPush (rpProg (P := Empty) (Q := Q) (A := A) (U := U)
      Fixed.ringReg Fixed.hostReg Fixed.layout.ι_inj (by decide) hR) ≤ R)
    (hpushK : mnProgPush (cmulBlock cr (rmulOne (P := Empty) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr)) ≤ K)
    (L : ℕ) (keys : List ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hInv : ReplicaHaloLoopState H plan dst buffers allKeys (L::keys) S) (depth : ℕ) :
    ∃ v' F n, v'.user = v.user ∧ n ≤ H.keyCost L ∧ ReplicaHaloLoopState H plan dst buffers allKeys keys F ∧
      ExecWithin body (fun d z => mnSize z+d ≤
        mnSize (mk v {S with R := Function.update S.R (plan.gather 119) (List.replicate keys.length (tick : Fin (A+4)))})+
          depth+H.keyWorkspace (A := A) (U := U) hQ R K L) depth (processGeneratedHaloReplicaKey plan dst hR hQ)
        (mk v {S with R := Function.update S.R (plan.gather 119) (List.replicate keys.length (tick : Fin (A+4)))}) n (mk v' F) := by
  obtain ⟨hL,hLs,hpad,hkey,hne⟩ := hbounds L (hInv.remaining L (by simp))
  let W := H.windows L hL
  let S₀ : Stacks T A := {S with R := Function.update S.R (plan.gather 119) (List.replicate keys.length (tick : Fin (A+4)))}
  have hg₀ (k : Fin 126) (hk : k ≠ 119) : S₀.R (plan.gather k) = S.R (plan.gather k) := by
    simp [S₀,plan.gather_injective.eq_iff,hk]
  have headers₀ : ReplicaLoopHeaders H plan.gather buffers S₀ :=
    hInv.headers.of_frame (fun k _ hk => hg₀ k hk)
  have hs₀ : embStk plan.solver S₀ = embStk plan.solver S := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    simp [S₀,embStk,(plan.disjoint 119 k).symm]
  have hsR₀ (k : Fin 121) : S₀.R (plan.solver k) = S.R (plan.solver k) :=
    congrFun (congrArg Stacks.R hs₀) k
  have hd₀ : S₀.R dst = S.R dst := by simp [S₀,(hgd 119).symm]
  obtain ⟨rows,hrows,hlen,hrange,hdst⟩ := hInv.rows
  obtain ⟨hwV,hcoords,hunits⟩ := H.metadataWidth_fits
  have hgeom (j : Fin (H.offsets L).length) :=
    haloReplicaClassOrigin_geometry H.s_lt_t H.band H.origin H.span L j
  obtain ⟨v',F,n,replicas,ha,hnrep,hvalid,houtputRange,hu,hn,he,hgather,hd,htail,hi,ho,
      hbank,hcache,hfresh,herror,hpreserve⟩ :=
    processGeneratedHaloReplicaKey_exec_within (body := body) plan dst hgd hsd hR hQ hA
      H.p_pos H.s_lt_t H.band_fit H.u_pos H.alpha_sq H.theta_pos H.gap H.budget hL hLs hpad
      H.metadataWidth H.origin H.span W rfl H.Fs rows hne H.span_fit hwV hcoords hunits
      v S₀ buffers.solverOutputTail buffers.rhsTail buffers.packedRhsTail buffers.accumulatorTail
      (keys.flatMap (binSyms H.metadataWidth)++buffers.keyTail) R K hpushR hpushK depth
      H.rhs_bound (haloInterior s H.t H.band H.origin (H.origin+H.span)) H.x H.solves
      (fun j hj k hk => (hgeom ⟨j,hj⟩).2.2.1 k hk)
      (fun j hj k hk => (hgeom ⟨j,hj⟩).2.2.2.1 k hk)
      (fun j hj k hk => (hgeom ⟨j,hj⟩).2.2.2.2 k hk)
      (by rw [hs₀]; exact hInv.bank) headers₀.masters rfl headers₀.origin headers₀.endpoint
      (by intro k hk; rw [hsR₀]; exact hInv.solverFresh k hk) headers₀.width hkey
      (by rw [hg₀ 87 (by decide),hInv.packets]; simp [List.flatMap_cons,List.append_assoc])
      headers₀.volume headers₀.source headers₀.blank headers₀.fresh hrows hlen hrange (hd₀.trans hdst)
  have hg (k : Fin 126) (h87 : k ≠ 87) (h119 : k ≠ 119) : F.R (plan.gather k) = S.R (plan.gather k) := by
    have hh := congrFun (congrArg Stacks.R hgather) k
    simpa [embStk,S₀,plan.gather_injective.eq_iff,h87,h119] using hh
  refine ⟨v',F,n,hu,hn,?_,he⟩
  refine ⟨fun J hJ => hInv.remaining J (by simp [hJ]),hInv.headers.of_frame hg,?_,?_,hfresh,
    hi.trans hInv.input,ho.trans hInv.output,?_,?_,?_,?_,?_,?_⟩
  · rw [hi,ho]; exact hbank
  · exact hcache.trans ((hsR₀ 117).trans hInv.cache)
  · have hh := congrArg (fun B : Stacks 126 A => B.L) hgather
    change (embStk plan.gather F).L = (embStk plan.gather S).L at hh
    exact hh.trans hInv.gatherLeft
  · intro k h87 h119
    exact (hg k h87 h119).trans (hInv.gatherFrame k h87 h119)
  · have hh := congrFun (congrArg Stacks.R hgather) 87
    simpa [embStk] using hh
  · have hh := congrFun (congrArg Stacks.R hgather) 119
    simpa [embStk,S₀,plan.gather_injective.eq_iff] using hh
  · obtain ⟨hnRows,hrowLength,hrowRange,hflat⟩ := publicationReplicas_output_rows W H.wordWidth replicas hvalid houtputRange
    refine ⟨replicas.map (PublicationReplica.output W H.wordWidth),hnRows.trans hnrep,hrowLength,hrowRange,?_⟩
    rw [hflat]
    exact hd
  · intro J hJ hnot
    by_cases hJL : J = L
    · subst J
      exact herror
    · apply H.classAccuracy_preserved J L hJL (S₀.R dst) (F.R dst) hpreserve
      rw [hd₀]
      apply hInv.accuracy J hJ
      intro hmem
      rcases List.mem_cons.mp hmem with heq | hmem
      · exact hJL heq
      · exact hnot hmem

theorem replicaHaloLoop_exec_within (H : ReplicaHaloProblem s) (plan : ReplicaInteriorPlacement T) (dst : Fin T)
    (hgd : ∀ i, plan.gather i ≠ dst) (hsd : ∀ i, plan.solver i ≠ dst)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (buffers : ReplicaLoopBuffers A) (allKeys : List ℕ)
    (hbounds : ∀ L ∈ allKeys, 0 < L ∧ L ≤ s ∧ L+L ≤ 2^H.l+1 ∧ L < 2^H.metadataWidth ∧ H.offsets L ≠ [])
    (R K : ℕ)
    (hpushR : mnProgPush (rpProg (P := Empty) (Q := Q) (A := A) (U := U)
      Fixed.ringReg Fixed.hostReg Fixed.layout.ι_inj (by decide) hR) ≤ R)
    (hpushK : mnProgPush (cmulBlock cr (rmulOne (P := Empty) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr)) ≤ K)
    (keys : List ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hInv : ReplicaHaloLoopState H plan dst buffers allKeys keys S)
    (hflag : v.flag = keys.head?.isSome) (depth : ℕ) :
    ∃ v' F n, v'.user = v.user ∧ n ≤ (keys.map (fun L => H.keyCost L+3)).sum+1 ∧
      ReplicaHaloLoopState H plan dst buffers allKeys [] F ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        (keys.map (H.keyWorkspace (A := A) (U := U) hQ R K)).sum) depth
        (generatedHaloReplicaKeyLoop plan dst hR hQ) (mk v S) n (mk v' F) := by
  apply generatedHaloReplicaKeyLoop_of_invariant plan dst hR hQ
    (ReplicaHaloLoopState H plan dst buffers allKeys) H.keyCost (H.keyWorkspace (A := A) (U := U) hQ R K)
    depth (fun keys S h => h.count)
  · intro L keys v S h
    exact replicaHaloLoop_step H plan dst hgd hsd hR hQ hA buffers allKeys hbounds R K hpushR hpushK L keys v S h depth
  · exact hInv
  · exact hflag

noncomputable def runReplicaHaloLoop (plan : ReplicaInteriorPlacement T) (dst : Fin T)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  .seq (.act (peekR (plan.gather 119))) (generatedHaloReplicaKeyLoop plan dst hR hQ)

theorem runReplicaHaloLoop_exec_within (H : ReplicaHaloProblem s) (plan : ReplicaInteriorPlacement T) (dst : Fin T)
    (hgd : ∀ i, plan.gather i ≠ dst) (hsd : ∀ i, plan.solver i ≠ dst)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (buffers : ReplicaLoopBuffers A) (allKeys : List ℕ)
    (hbounds : ∀ L ∈ allKeys, 0 < L ∧ L ≤ s ∧ L+L ≤ 2^H.l+1 ∧ L < 2^H.metadataWidth ∧ H.offsets L ≠ [])
    (R K : ℕ)
    (hpushR : mnProgPush (rpProg (P := Empty) (Q := Q) (A := A) (U := U)
      Fixed.ringReg Fixed.hostReg Fixed.layout.ι_inj (by decide) hR) ≤ R)
    (hpushK : mnProgPush (cmulBlock cr (rmulOne (P := Empty) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr)) ≤ K)
    (keys : List ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hInv : ReplicaHaloLoopState H plan dst buffers allKeys keys S)
    (depth : ℕ) :
    ∃ v' F n, v'.user = v.user ∧ n ≤ (keys.map (fun L => H.keyCost L+3)).sum+2 ∧
      ReplicaHaloLoopState H plan dst buffers allKeys [] F ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        (keys.map (H.keyWorkspace (A := A) (U := U) hQ R K)).sum) depth
        (runReplicaHaloLoop plan dst hR hQ) (mk v S) n (mk v' F) := by
  let v₀ := {v with flag := (List.replicate keys.length (tick : Fin (A+4))).head?.isSome}
  have he₀ := Exec.act (body := body) (peekR (plan.gather 119)) (mk v S)
  rw [peekR_run,hInv.count] at he₀
  have he₀' : ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+0) depth
      (.act (peekR (plan.gather 119))) (mk v S) 1 (mk v₀ S) :=
    mn_native_exec_within he₀ 0 (by simp [peekR,mnNativePushBound,mnActPush]) depth _ (by omega)
  obtain ⟨v',F,n,hu,hn,hInvF,he⟩ := replicaHaloLoop_exec_within H plan dst hgd hsd hR hQ hA
    buffers allKeys hbounds R K hpushR hpushK keys v₀ S hInv
    (by change (List.replicate keys.length (tick : Fin (A+4))).head?.isSome = keys.head?.isSome; cases keys <;> simp) depth
  refine ⟨v',F,1+n,hu,by omega,hInvF,?_⟩
  refine .seq (he₀'.mono ?_) (he.mono ?_)
  · intro d z hz
    omega
  · intro d z hz
    change mnSize z+d ≤ mnSize (mk v S)+depth+
      (keys.map (H.keyWorkspace (A := A) (U := U) hQ R K)).sum at hz
    exact hz

namespace ReplicaHaloProblem

theorem classAccuracy_of_empty (H : ReplicaHaloProblem s) (L : ℕ) (output : List (Fin (A+4)))
    (hempty : H.offsets L = []) : H.ClassAccuracy L output := by
  intro r j
  have hj := j.isLt
  simp only [hempty,List.length_nil] at hj
  omega

theorem classAccuracy_haloInterior (H : ReplicaHaloProblem s) (output : List (Fin (A+4)))
    (haccuracy : ∀ L ∈ haloLengthKeys s H.t H.band H.origin (H.origin+H.span), H.ClassAccuracy L output) :
    ∀ r : Fin H.Fs.length, PhaseCellInterface.ErrorOn (haloInterior s H.t H.band H.origin (H.origin+H.span))
      (fun k => (packedIntervalRead H.precision H.wordWidth H.origin
        (output.drop (r.val*H.span*H.wordWidth)) k).re) (H.x r) (1/(2 : ℝ)^H.target) := by
  intro r k hk
  obtain ⟨L,hL,j,i,he⟩ := packedHaloGroups_cover H.s_lt_t H.band H.origin (H.origin+H.span) k hk
  have horigin : H.originAt L j = packedCellOrigin H.origin (H.offsets L) j := by
    simp only [originAt,haloReplicaClassOrigin,offsets,packedCellOrigin,
      List.getD_eq_getElem _ _ j.isLt,List.getElem?_eq_getElem j.isLt,Option.getD_some]
  apply haccuracy L hL r j k
  apply Finset.mem_image.mpr
  refine ⟨i.val,Finset.mem_range.mpr i.isLt,?_⟩
  rw [horigin]
  exact he

theorem nonempty_classAccuracy_haloInterior (H : ReplicaHaloProblem s) (output : List (Fin (A+4)))
    (haccuracy : ∀ L ∈ haloLengthKeys s H.t H.band H.origin (H.origin+H.span),
      H.offsets L ≠ [] → H.ClassAccuracy L output) :
    ∀ r : Fin H.Fs.length, PhaseCellInterface.ErrorOn (haloInterior s H.t H.band H.origin (H.origin+H.span))
      (fun k => (packedIntervalRead H.precision H.wordWidth H.origin
        (output.drop (r.val*H.span*H.wordWidth)) k).re) (H.x r) (1/(2 : ℝ)^H.target) := by
  apply H.classAccuracy_haloInterior output
  intro L hL
  by_cases hempty : H.offsets L = []
  · exact H.classAccuracy_of_empty L output hempty
  · exact haccuracy L hL hempty

end ReplicaHaloProblem

theorem ReplicaHaloLoopState.haloInterior_accuracy (H : ReplicaHaloProblem s) (plan : ReplicaInteriorPlacement T)
    (dst : Fin T) (buffers : ReplicaLoopBuffers A) (F : Stacks T A)
    (h : ReplicaHaloLoopState H plan dst buffers (haloLengthKeys s H.t H.band H.origin (H.origin+H.span)) [] F) :
    ∀ r : Fin H.Fs.length, PhaseCellInterface.ErrorOn (haloInterior s H.t H.band H.origin (H.origin+H.span))
      (fun k => (packedIntervalRead H.precision H.wordWidth H.origin
        ((F.R dst).drop (r.val*H.span*H.wordWidth)) k).re) (H.x r) (1/(2 : ℝ)^H.target) :=
  H.classAccuracy_haloInterior (F.R dst) (fun L hL => h.accuracy L hL (by simp))

theorem ReplicaHaloLoopState.haloInterior_accuracy_of_cover (H : ReplicaHaloProblem s)
    (plan : ReplicaInteriorPlacement T) (dst : Fin T) (buffers : ReplicaLoopBuffers A)
    (allKeys : List ℕ) (F : Stacks T A) (h : ReplicaHaloLoopState H plan dst buffers allKeys [] F)
    (hcover : ∀ L ∈ haloLengthKeys s H.t H.band H.origin (H.origin+H.span), H.offsets L ≠ [] → L ∈ allKeys) :
    ∀ r : Fin H.Fs.length, PhaseCellInterface.ErrorOn (haloInterior s H.t H.band H.origin (H.origin+H.span))
      (fun k => (packedIntervalRead H.precision H.wordWidth H.origin
        ((F.R dst).drop (r.val*H.span*H.wordWidth)) k).re) (H.x r) (1/(2 : ℝ)^H.target) :=
  H.nonempty_classAccuracy_haloInterior (F.R dst) (fun L hL hne => h.accuracy L (hcover L hL hne) (by simp))

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
