module

public import IntegerMultBounds.MathlibTM2.M6.BitOrdinaryIdleRead

/-! Execute the scheduled weighted child with only the caller payload shared. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Matrix
open Shared50ModularControl (prime)
open IntegerMultBounds.Networks.Certificates.PR589.Nine
open Cover LabelTraversal FlatCoordinateLayout Stack Host Fallback RecursiveInterchangeLayout

/-- The complete procedure body for one ordinary child occurrence. -/
noncomputable def hostedWeightedOrdinaryProgram [M8.Machine.Net] {P U : Type} {n T : ℕ}
    (full : Fin 58 ↪ Fin n) (rootCut : Fin n) (host : Fin 64 ↪ Fin T)
    (aux : Fin ((rowSwapBlock.tapes+35)+1) ↪ Fin T) (separate : ∀ i j, aux i ≠ host j)
    (r g : ℕ) (f : P) : Pr P (n+T) columnCapacity prime U :=
  let physical := Record.payloadBank (full 24) (host 24)
  let apart := fun i j => physical.injective.ne (separate i j)
  let program := weightedOrdinaryProgram (host.trans physical) (aux.trans physical) apart r g f
  let src := fun i => (full (ordinaryHeaderSlots i)).castAdd T
  let port := host.trans (Fin.natAddEmb n)
  let slots := ordinaryHeaderSlots.trans (Fin.castLEEmb (by decide : 58 ≤ 64))
  let load := Record.copyLeafHeaders src (slots.trans port) (port 0) (port 1) (List.finRange 7)
  let cut := correctionColumnPlacement (host.trans physical) (aux.trans physical) apart (Fin.last _)
  let init := load.seq (bcopy (rootCut.castAdd T) cut (port 0) (port 1))
  (init.seq program).seq (clearWorkTapes ((List.finRange (n+T)).filter fun j => n ≤ j.val))

local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

/-- Run the scheduled weighted child from the record headers and return the complete caller frame. -/
theorem hostedOrdinaryChildDispatch_exec [M8.Machine.Net] {P U : Type} {n T : ℕ}
    (full : Fin 58 ↪ Fin n) (rootCut : Fin n) (host : Fin 64 ↪ Fin T)
    (aux : Fin ((rowSwapBlock.tapes+35)+1) ↪ Fin T) (separate : ∀ i j, aux i ≠ host j)
    (body : P → Pr P (n+T) columnCapacity prime U) :
    let physical := Record.payloadBank (full 24) (host 24)
    let caller := host.trans physical
    let work := aux.trans physical
    let apart := fun i j => physical.injective.ne (separate i j)
    let placement := correctionColumnPlacement caller work apart
    let ports := columnPorts.trans placement
    let cut := placement (Fin.last _)
    ∃ C : ℕ, ∀ (node : Descriptor) (i : Fin nodeChildren5.length) w (aligned : node.width = 64*(w+1)),
      let r := nodeChildren5[i.val]
      let g := 64-r
      let parent := role node 142080
      let W := CopyChildLayout.spectators parent
      0 < W →
      let d := (r+g)+(r+g)
      let M := prime^(w+1)
      let is := ordinaryChildPackSchedule r g
      let routeTime := (is.map (fun i => completeSwapTime (P := Empty) (U := U) Empty.elim d i (i+1) w W M.size W.size)).sum+1
      let bank := ((Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)).trans ports
      let clean := fun (S : Stacks (n+T) prime) => ∀ k : Fin (rowSwapBlock.tapes+35), 35 ≤ k.val → S.L (ports k) = [] ∧ S.R (ports k) = []
      ∀ (v : HS (n+T) columnCapacity prime U) (S : Stacks (n+T) prime)
        (before : Fin (M^d*W) → ZMod 2)
        (f : P) (budget cutoff L : ℕ),
      let desc := ordinaryChildDescriptor r g w W
      let child := scheduledChild prime node i
      let same : rankDescriptor prime (r*(w+1)) (g*(w+1)) parent = child := by
        simp only [child,scheduledChild,aligned,Nat.mul_div_cancel_left _ (by decide : 0 < 64)]
        rfl
      let layout := (ordinaryScheduledLayout parent r g w).trans (finCongr (congrArg (volume prime) same))
      let onTape := fun (word : Fin (volume prime child) → ZMod 2) (D : Stacks (n+T) prime) =>
        ∀ z, readAt blank (D.L (bank 24)) (D.R (bank 24)) z =
          M8.Machine.ArbitraryWidthHighExchangeShared.sourceWord (v := desc) (word ∘ layout) z
      ∀ pivot : Fin r → (ZMod M)ˣ,
      let setupTime := 6*(2*M.size+W.size+1+w+2*(r*M.size)+L)+49
      let privateTapes := (List.finRange (n+T)).filter fun j => n ≤ j.val
      S.R ((full 55).castAdd T) = (List.ofFn fun k => binSyms M.size (pivot k : ZMod M).val).flatten →
      S.R ((full 56).castAdd T) = (List.ofFn fun k => binSyms M.size (pivot k).inv.val).flatten →
      cutoff < 2^L → desc.width.size ≤ L →
      S.R (rootCut.castAdd T) = binSyms L cutoff →
      (cutoff < desc.width → child.width < node.width → ∀ word u D, onTape word D → clean D → D.R cut = binSyms L cutoff → ∃ y G t, y.user = u.user ∧ t ≤ budget ∧
        Exec body (body f) (mk u D) t (mk y G) ∧
        onTape (Shared50RecursiveNodeRows.transpose (one_dvd child.rows) word) G ∧
        (∀ j, j ≠ bank 24 → G.L j = D.L j ∧ G.R j = D.R j)) →
      S.R ((full 2).castAdd T) = binSyms M.size M → S.R ((full 53).castAdd T) = binSyms W.size W →
      S.R ((full 28).castAdd T) = binSyms 1 1 → S.R ((full 44).castAdd T) = binSyms M.size (1 : ZMod M).val →
      (S.R ((full 45).castAdd T)).length = w →
      (∀ j : Fin (n+T), n ≤ j.val → S.L j = [] ∧ S.R j = []) →
      (∀ z, readAt blank (S.L ((full 24).castAdd T)) (S.R ((full 24).castAdd T)) (z-0) =
        RadixToBinary.binaryEncoding.encode (putWord (fun _ => blank) 0 (List.ofFn (SparseRoleCircuit.encode ∘ before)) z)) →
      let localTime := setupTime+(if cutoff < desc.width then 2*(1+routeTime) else C*(desc.width*(M^d*W))) +
        ordinaryCorrectionTime U w W M.size W.size
      let hosted := hostedWeightedOrdinaryProgram (U := U) full rootCut host aux separate r g f
      ∃ z F steps after, z.user = v.user ∧ Exec body hosted (mk v S) steps (mk z F) ∧
        (∀ c, Fast.Main.mnProgPush hosted ≤ c → (∀ f, Fast.Main.mnProgPush (body f) ≤ c) →
          steps ≤ (if cutoff < desc.width then budget+2 else 0) + (4*w+23*desc.width+22*L+51) +
            localTime + (privateTapes.length*(6*(c*localTime)+4)+1)) ∧
        (∀ (hg tg : Fin g → ZMod M) (x : IntegerMultBounds.Swap.Shear.State (Fin r) (ZMod M)) (j : Fin W),
          let address := fun y => let t := childFields hg tg y
                                  FlatCoordinateLayout.index (Fin.append t.1 t.2) j
          after (address (Weighted.child r (fun k => (pivot k : ZMod M)) (fun k => (pivot k).inv) x)) = before (address x)) ∧
        (∀ z, RadixToBinary.binaryEncoding.encode (putWord (fun _ => blank) 0 (List.ofFn (SparseRoleCircuit.encode ∘ after)) z) =
          readAt blank (F.L ((full 24).castAdd T)) (F.R ((full 24).castAdd T)) (z-0)) ∧
        ∀ j, j ≠ (full 24).castAdd T → F.L j = S.L j ∧ F.R j = S.R j := by
  intro physical caller work apart placement ports cut
  obtain ⟨C,dispatch⟩ := weightedOrdinaryChildDispatch_exec caller work apart body
  refine ⟨C,?_⟩
  intro node i w aligned r g parent W hW d M is routeTime bank clean v S before f budget cutoff L
    desc child eqn layout onTape pivot setupTime privateTapes
    pos inv cutFits widthFits cutWord recurse modulus width one padded clock free source localTime hosted
  let program := weightedOrdinaryProgram (U := U) caller work apart r g f
  let src := fun i => (full (ordinaryHeaderSlots i)).castAdd T
  let slots := ordinaryHeaderSlots.trans (Fin.castLEEmb (by decide : 58 ≤ 64))
  obtain ⟨u,D,user,setup,left,right,header,cutoffLoaded,empty,finish⟩ := privateOrdinaryReturn_exec full rootCut host aux separate body program v S free
  have priv (j : Fin T) (ne : j ≠ host 24) : physical j = j.natAdd n := Record.payloadBank_private _ _ _ ne
  have blankAt (j : Fin T) (notPayload : j ≠ host 24) (notCut : j ≠ aux (Fin.last _))
      (off : ∀ i, host (slots i) ≠ j) : D.L (physical j) = [] ∧ D.R (physical j) = [] := by
    rw [priv j notPayload,left]
    exact ⟨(free _ (Nat.le_add_right ..)).1,empty j notCut off⟩
  have hostBlank (j : Fin 64) (ne : j ≠ 24) (off : ∀ i, slots i ≠ j) :=
    blankAt (host j) (host.injective.ne ne) (separate _ _).symm (fun i => host.injective.ne (off i))
  have workBlank (k : Fin ((rowSwapBlock.tapes+35)+1)) (ne : k ≠ Fin.last _) :=
    blankAt (aux k) (separate _ _) (aux.injective.ne ne) (fun i => (separate _ _).symm)
  have fresh : ∀ j ∈ ([58,59,61,62,63] : List (Fin 64)), D.R (caller j) = [] := by
    intro j hj
    have ok : ∀ j ∈ ([58,59,61,62,63] : List (Fin 64)), j ≠ 24 ∧ ∀ i, slots i ≠ j := by decide
    exact (hostBlank j (ok j hj).1 (ok j hj).2).2
  have scratch : ∀ k ∈ shearWork, D.L (work (columnBank k)) = [] ∧ D.R (work (columnBank k)) = [] :=
    fun k _ => workBlank _ (Fin.castSucc_ne_last _)
  have cleanD : clean D := by
    intro k hk
    have off : ¬ ∃ j, columnBank (correctionColumnSlots j) = columnPorts k := by
      rintro ⟨j,h⟩
      have val := congrArg Fin.val h
      change (correctionColumnSlots j).val = k.val at val
      omega
    have eq : ports k = work (columnPorts k) := by
      change sharedRegisterPlacement work (correctionCallerSlots.trans caller) correctionRole (columnPorts k) = _
      unfold sharedRegisterPlacement
      rw [show correctionRole (columnPorts k) = none from dite_eq_right off]
    rw [eq]
    exact workBlank _ (Fin.castSucc_ne_last _)
  have payload : caller 24 = (full 24).castAdd T := Record.payloadBank_shared ..
  have dest := hostBlank 25 (by decide) (by decide)
  obtain ⟨z,F,t,after,same,paid,run,action,readback,_,_,_,frame,growth⟩ :=
    dispatch node i w aligned hW u D (fun _ => blank) 0 before f budget cutoff L pivot
      (fun _ _ _ => rfl) ((header 5).trans pos) ((header 6).trans inv) fresh cutFits widthFits
      (cutoffLoaded.trans cutWord) (by
        intro active smaller word a A onWord cleanA savedA precision
        obtain ⟨y,G,m,huser,time,childRun,result,frame⟩ := recurse active smaller word a A onWord cleanA precision
        refine ⟨y,G,m,huser,time,childRun,result,fun j ne => frame _ (bank.injective.ne ne),?_,?_⟩
        · intro k hk
          have ne : ports k ≠ bank 24 := by
            intro eq
            have sameIndex : k = (⟨24,by omega⟩ : Fin (rowSwapBlock.tapes+35)) := ports.injective eq
            have val := congrArg Fin.val sameIndex
            change k.val = 24 at val
            omega
          obtain ⟨l,r⟩ := frame _ ne
          exact ⟨l.trans (cleanA k hk).1,r.trans (cleanA k hk).2⟩
        · intro j hj
          have ne : j ≠ bank 24 := (hj ⟨24,by omega⟩).symm
          exact ⟨(frame j ne).1.trans (savedA j hj).1,(frame j ne).2.trans (savedA j hj).2⟩)
      ((header 0).trans modulus) ((header 1).trans width) ((header 2).trans one) ((header 3).trans padded)
      ((congrArg List.length (header 4)).trans clock) scratch
      (by rwa [payload,left,right]) (by intro k; rw [show D.L (caller 25) = [] from dest.1,show D.R (caller 25) = [] from dest.2]; simp [readAt]; rfl) cleanD
  obtain ⟨y,G,lastUser,done,payloadLeft,payloadRight,kept⟩ := finish z F t run frame
  have setupCost := ordinaryHeaderCost (fun k => (S.R ((full k).castAdd T)).length) M.size W.size w r L
    (by simp [modulus,length_binSyms]) (by simp [width,length_binSyms]) (by simp [one,length_binSyms])
    (by simp [padded,length_binSyms]) clock
    (by simp [pos,List.length_flatten,List.map_ofFn,Function.comp_def,length_binSyms,List.ofFn_const])
    (by simp [inv,List.length_flatten,List.map_ofFn,Function.comp_def,length_binSyms,List.ofFn_const])
  have timeEq : ((List.finRange 7).map fun i => 6*(S.R (src i)).length+6).sum+1+(6*(S.R (rootCut.castAdd T)).length+6) = setupTime := by
    rw [cutWord,length_binSyms]
    exact setupCost
  rw [timeEq] at setup done
  refine ⟨y,G,_,after,lastUser.trans (same.trans user),done,?_,action,?_,kept⟩
  · intro c hp hb
    have beforeClear := (max_le_iff.mp hp).1
    have loaded := StackGrowthExcept.of_exec (caller 24) setup (max_le_iff.mp beforeClear).1 hb
    have localStock := loaded.trans (growth c (max_le_iff.mp beforeClear).2 hb)
    let route := if cutoff < desc.width then 2*(1+routeTime) else C*(desc.width*(M^d*W))
    let correction := ordinaryCorrectionTime U w W M.size W.size
    change StackGrowthExcept (caller 24) S F (c*setupTime+c*(route+correction)) at localStock
    have total : c*setupTime+c*(route+correction) = c*localTime := by
      simp only [localTime,route,correction,Nat.mul_add,Nat.add_assoc]
    rw [total] at localStock
    have each (j : Fin (n+T)) (hj : j ∈ privateTapes) :
        4*(F.L j).length+2*(F.R j).length+4 ≤ 6*(c*localTime)+4 := by
      have privateAt : n ≤ j.val := (List.mem_filter.mp hj).2 |> of_decide_eq_true
      have ne : j ≠ caller 24 := by
        rw [payload]
        intro eq
        subst j
        exact (full 24).isLt.not_ge privateAt
      obtain ⟨l,r⟩ := localStock j ne
      obtain ⟨l0,r0⟩ := free j privateAt
      rw [l0,List.length_nil,Nat.zero_add] at l
      rw [r0,List.length_nil,Nat.zero_add] at r
      omega
    have price := List.sum_le_sum (l := privateTapes) each
    simp only [List.map_const',List.sum_replicate,smul_eq_mul] at price
    change t ≤ 4*w+23*desc.width+22*L+51+(if cutoff < desc.width then budget+2+2*(1+routeTime) else C*(desc.width*(M^d*W)))+correction at paid
    have running : setupTime+t ≤ (if cutoff < desc.width then budget+2 else 0)+(4*w+23*desc.width+22*L+51)+localTime := by
      change _ ≤ _ + (setupTime+route+correction)
      dsimp only [route]
      split_ifs at paid ⊢ <;> omega
    exact Nat.add_le_add running (Nat.add_le_add_right price 1)
  · intro k
    rw [payloadLeft,payloadRight,← payload]
    exact readback k

end IntegerMultBounds.MathlibTM2.M6.BitNode
