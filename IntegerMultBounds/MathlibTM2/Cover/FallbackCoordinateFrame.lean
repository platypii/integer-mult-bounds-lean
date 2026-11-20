module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackLeafPairSwap
public import IntegerMultBounds.MathlibTM2.Cover.FallbackWeightedLeafBudget

/-! Execute a coordinate leaf between the descriptor change and its return. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open M8.RevMachine RecursiveInterchangeLayout

/-- The host word for one coordinate. Only the two archive offsets vary
across the schedule. The role, tape placement and state space stay fixed. -/
noncomputable def packedCoordinateProgram [M8.Machine.Net] {T work Q : ℕ} {F U : Type}
    (io : Fin T) (parentIndex pivotIndex : ℕ) :
    let common := CommonBank.count T
    let entry : Graph.Block common prime := Blocks.seqB LeafRoutines.offsets (Blocks.seqB Blocks.push LeafRoutines.view)
    let leave : Graph.Block common prime := Blocks.seqB Blocks.restore LeafRoutines.advance
    entry.tapes ≤ common+work → leave.tapes ≤ common+work → LeafCore.small ≤ work →
    entry.states ≤ Q → leave.states ≤ Q → (LeafCore.core io).states ≤ Q →
    Pr F ((common+55)+work) Q prime U := by
  intro common entry leave ef xf fits eqs xqs cap
  let place (g : Graph.Block common prime) (h : g.tapes ≤ common+work) (q : g.states ≤ Q) :
      Pr F ((common+55)+work) Q prime U :=
    statePlacedNormalized (framePorts 55 h) q (Nat.zero_lt_of_lt g.program.start.isLt)
      Empty.elim (foreign g.program)
  let leaf : Pr F ((common+55)+work) Q prime U := statePlacedNormalized (packedFramePorts (host := common+24) fits) cap
    (Nat.lt_of_lt_of_le (by decide : 0 < 217) (leafCoreCapacity io)) Empty.elim
    (packedLeafProgram (F := Empty) io parentIndex pivotIndex)
  exact ((place entry ef eqs).seq leaf).seq (place leave xf xqs)

section
local instance (w : ℕ) : NeZero (prime^(w+1)) :=
  ⟨pow_ne_zero _ Networks.Shared50ModularControl.prime_prime.ne_zero⟩

private theorem projectedUser {K T q Q A : ℕ} {U : Type} (ports : Fin T ↪ Fin K)
    (pos : 0 < q) (u : HS K Q A U) : (stateLiftDown pos (embDn ports u)).user = u.user := rfl

attribute [local irreducible] packedLeafPush packedLeafProgram Fast.Main.mnProgPush Fast.Main.mnPushC

/-- Execute the weighted middle of a coordinate call on the same host as
entry and restore. The output word identifies the role bank passed to restore. -/
theorem packedCoordinateMiddle_exec [M8.Machine.Net] {T m d work Q : ℕ} {F U : Type}
    (v : Descriptor) (positive : v.Positive) (w : ℕ) (width : v.width = w+1)
    (parent : Fin m → ZMod (prime^(w+1))) (j : Fin m) (parentInv : ZMod (prime^(w+1)))
    (reciprocal : parent j * parentInv = 1) (pivot : Fin d → ZMod (prime^(w+1)))
    (i : Fin d) (unit : IsUnit (pivot i)) (io : Fin T) (roles : Tapes T prime)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime)
    (ctr : Fin CommonBank.K → Option ℕ) (st : Tapes 2 prime)
    (fits : LeafCore.small ≤ work) (cap : (LeafCore.core io).states ≤ Q) :
    let common := CommonBank.count T
    let host := common+24
    let M := prime^(w+1)
    let N := ((v.beforeRows*v.rows*v.beforeH)*M*v.between)*(M*v.afterD)
    let ports := packedFramePorts (host := host) fits
    let pos := Nat.lt_of_lt_of_le (by decide : 0 < 217) (leafCoreCapacity io)
    let leaf := packedLeafProgram (F := Empty) (U := U) io j.val i.val
    let record := (Fin.natAddEmb common (m := 24)).trans ((Fin.castAddEmb 31).trans (Fin.castAddEmb work))
    let rep := fun roles' (D : Stacks ((host+31)+work) prime) =>
      RepT (CommonBank.bank roles' (Routines.hdr v) f p node scalar ctr st)
        (fun k => D.L (((k.castAdd 24).castAdd 31).castAdd work))
        (fun k => D.R (((k.castAdd 24).castAdd 31).castAdd work))
    let clean := fun (D : Stacks ((host+31)+work) prime) => ∀ (k : Fin work) x,
      readAt blank (D.L (k.natAdd (host+31))) (D.R (k.natAdd (host+31))) x = blank
    ∀ (word : Fin N → ZMod 2) (body : F → Pr F ((host+31)+work) Q prime U)
      (u : HS _ Q prime U) (before S : Stacks _ prime) (pivotTail parentTail : List (Fin (prime+4))),
      roles.head io = 0 → roles.tape io = leafBitTape (List.ofFn word) → rep roles S → clean S →
      (∀ k : Fin 55, S.L ((k.natAdd common).castAdd work) = before.L ((k.natAdd common).castAdd work) ∧
        S.R ((k.natAdd common).castAdd work) = before.R ((k.natAdd common).castAdd work)) →
      (∀ k : Fin 31, before.L ((k.natAdd host).castAdd work) = [] ∧ before.R ((k.natAdd host).castAdd work) = []) →
      before.R (record 18) = [] →
      PackedLeafInputs (goodChildPorts.trans record) M.size parent pivot before pivotTail parentTail →
      ∃ next : Fin N → ZMod 2, ∃ z D n, z.user = u.user ∧
        n ≤ 1+(weightedLeafCost (volume prime v) v.width (LeafCore.core io).tapes
          (packedLeafPush (F := Empty) (U := U) io Empty.elim)+
          ((1000*(prime+1)+8*(i.val+j.val))*(2*(prime.size+1)^2))*M) ∧
        Exec body (statePlacedNormalized ports cap pos Empty.elim leaf) (mk u S) n (mk z D) ∧
        rep (SharedPlacementAlphabet.setTape roles io (leafBitTape (List.ofFn next)) 0) D ∧ clean D ∧
        (∀ k : Fin 55, D.L ((k.natAdd common).castAdd work) = S.L ((k.natAdd common).castAdd work) ∧
          D.R ((k.natAdd common).castAdd work) = S.R ((k.natAdd common).castAdd work)) ∧
        ∀ a < v.beforeRows, ∀ row < v.rows, ∀ pre < v.beforeH, ∀ mid < v.between,
          ∀ post < v.afterD, ∀ h t : ZMod M,
          ext next (index prime v a row pre ((parent j*pivot i)*t).val mid ((parentInv*Ring.inverse (pivot i))*h).val post) =
            ext word (index prime v a row pre h.val mid t.val post) := by
  intro common host M N ports pos leaf record rep clean word body u before S pivotTail parentTail head input initial free keep arithmetic spare archives
  obtain ⟨empty,spare',archives',initial',privateBlank⟩ := packedFrame_inputs fits parent pivot
    (CommonBank.bank roles (Routines.hdr v) f p node scalar ctr st) pivotTail parentTail before S
    keep arithmetic spare archives initial free
  obtain ⟨y,E,t,user,bound,⟨run,_⟩,out,next,cells,addr⟩ := packedWeightedLeaf_exec v positive w width
    parent j parentInv reciprocal pivot i unit io roles f p node scalar ctr st word head input
    (F := Empty) Empty.elim (stateLiftDown pos (embDn ports u)) (embStk ports S) empty spare'
    pivotTail parentTail archives' initial' privateBlank
  obtain ⟨z,D,hz,placed,back,blank⟩ := packedFrame_exec fits cap pos leaf body u S y E run out.1.2 free
  have startEmpty (k : Fin 31) : S.L ((k.natAdd host).castAdd work) = [] ∧
      S.R ((k.natAdd host).castAdd work) = [] := by
    have same := keep (k.natAdd 24)
    have idx : ((k.natAdd 24).natAdd common : Fin (common+55)) = k.natAdd host := by
      apply Fin.ext
      simp [host,Nat.add_assoc]
    rw [idx] at same
    exact ⟨same.1.trans (arithmetic k).1,same.2.trans (arithmetic k).2⟩
  obtain ⟨changed,kept⟩ := packedFrame_return fits _ S D E back out.1.1 out.2.2.2.2 out.2.2.2.1 startEmpty
  refine ⟨next,z,D,1+t,?_,?_,?_,?_,?_,?_,?_⟩
  · exact hz.trans (user.trans (projectedUser ports pos u))
  · exact Nat.add_le_add_left bound 1
  · exact placed
  · simpa only [rep,cells] using changed
  · exact blank
  · exact kept
  · exact addr

end

/-- A leaf may change its role tapes subject to its payload specification.
Returning restores the parent descriptor and decrements the coordinate counter. -/
theorem coordinateCall_exec {T n work Q cost : ℕ} {F U : Type} (roles : Tapes T prime)
    (v : Descriptor) (positive : v.Positive) (b m : ℕ) (hb : 0 < b) (width : v.width = n*b)
    (i : Fin n) (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime)
    (st : Tapes 2 prime) (free : Family.NodeFree node) (effect : Tapes T prime → Prop) :
    let common := CommonBank.count T
    let entry : Graph.Block common prime := Blocks.seqB LeafRoutines.offsets (Blocks.seqB Blocks.push LeafRoutines.view)
    let leave : Graph.Block common prime := Blocks.seqB Blocks.restore LeafRoutines.advance
    let parent := fun roles' count => CommonBank.bank roles' (Routines.hdr v) f p node scalar (Family.leafC b m n count) st
    let c := Family.leafC b m n (i.val+1)
    let live := Function.update (Function.update (Function.update c 12 (some i.val)) 13 (some 1)) 14 (some (n-i.val-1))
    let view := {(RecursiveInterchangeLayout.child (prime^b) 1 1 v i i.rev) with width := b}
    let inside := fun roles' => CommonBank.bank roles' (Routines.hdr view) f p
      (RecursiveViewFrame.savedStack (Routines.hdr v) node) scalar live st
    ∀ (ef : entry.tapes ≤ common+work) (xf : leave.tapes ≤ common+work)
      (eqs : entry.states ≤ Q) (xqs : leave.states ≤ Q)
      (body : F → Pr F ((common+55)+work) Q prime U) (leaf : Pr F _ Q prime U)
      (u : HS _ Q prime U) (S : Stacks _ prime),
    let rep := fun bank (D : Stacks ((common+55)+work) prime) => RepT bank
      (fun i : Fin common => D.L ((i.castAdd 55).castAdd work))
      (fun i => D.R ((i.castAdd 55).castAdd work))
    let clean := fun (D : Stacks ((common+55)+work) prime) => ∀ (j : Fin work) x,
      readAt blank (D.L (j.natAdd (common+55))) (D.R (j.natAdd (common+55))) x = blank
    let keep := fun (D E : Stacks ((common+55)+work) prime) => ∀ j : Fin 55,
      D.L ((j.natAdd common).castAdd work) = E.L ((j.natAdd common).castAdd work) ∧
      D.R ((j.natAdd common).castAdd work) = E.R ((j.natAdd common).castAdd work)
    let place := fun (g : Graph.Block common prime) (fits : g.tapes ≤ common+work) (cap : g.states ≤ Q) =>
      statePlacedNormalized (framePorts 55 fits) cap (Nat.zero_lt_of_lt g.program.start.isLt)
        Empty.elim (foreign g.program)
    rep (parent roles (i.val+1)) S → clean S →
    (∀ z D, rep (inside roles) D → clean D → keep D S →
      ∃ roles' y E t, effect roles' ∧ y.user = z.user ∧ t ≤ cost ∧
        Exec body leaf (mk z D) t (mk y E) ∧ rep (inside roles') E ∧ clean E ∧ keep E D) →
    ∃ roles' z D t, effect roles' ∧ z.user = u.user ∧
      t ≤ (1+(1800*volume prime v*(entry.tapes+5)+6))+cost+(1+(200*volume prime v*(leave.tapes+5)+6)) ∧
      Exec body (((place entry ef eqs).seq leaf).seq (place leave xf xqs)) (mk u S) t (mk z D) ∧
      rep (parent roles' i.val) D ∧ clean D ∧ keep D S := by
  intro common entry leave parent c live view inside ef xf eqs xqs body leaf u S rep clean keep place ready blank middle
  have frame := coordinateFrame_runs roles v positive b m hb width i f p node scalar st free
  have en : common ≤ entry.tapes := Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
  have ex : common ≤ leave.tapes := Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
  obtain ⟨roles',z,D,t,user,bound,run,out,cleanD,keepD⟩ := framedLeaf_exec
    (record := 55) entry leave _ _ (fun r : Subtype effect => inside r.val)
    (fun r => parent r.val i.val) frame.1 (fun r => frame.2 r.val)
    en ex ef xf eqs xqs body leaf u S ready blank (by
      intro z D child freeD keepD
      obtain ⟨r,y,E,t,hr,h⟩ := middle z D child freeD keepD
      exact ⟨⟨r,hr⟩,y,E,t,h⟩)
  exact ⟨roles'.val,z,D,t,roles'.property,user,bound,run,out,cleanD,keepD⟩

section
local instance (w : ℕ) : NeZero (prime^(w+1)) :=
  ⟨pow_ne_zero _ Networks.Shared50ModularControl.prime_prime.ne_zero⟩

private theorem coordinateWord_cast {n m : ℕ} (h : n = m) (word : Fin m → ZMod 2) :
    List.ofFn (fun k : Fin n => word (k.cast h)) = List.ofFn word ∧
    ext (fun k : Fin n => word (k.cast h)) = ext word := by
  subst m
  exact ⟨rfl,rfl⟩

/-- The concrete weighted coordinate call returns the changed word at the
decremented parent counter, preserving the caller's records. -/
theorem packedCoordinate_exec [M8.Machine.Net] {T m d work Q : ℕ} {F U : Type}
    (v : Descriptor) (positive : v.Positive) (w : ℕ) (width : v.width = d*(w+1))
    (parent : Fin m → ZMod (prime^(w+1))) (j : Fin m) (parentInv : ZMod (prime^(w+1)))
    (reciprocal : parent j * parentInv = 1) (pivot : Fin d → ZMod (prime^(w+1)))
    (i : Fin d) (unit : IsUnit (pivot i)) (io : Fin T) (roles : Tapes T prime)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime)
    (arity : ℕ) (st : Tapes 2 prime) (freeNode : Family.NodeFree node)
    (fits : LeafCore.small ≤ work) (cap : (LeafCore.core io).states ≤ Q) :
    let common := CommonBank.count T
    let host := common+24
    let M := prime^(w+1)
    let view := {(RecursiveInterchangeLayout.child M 1 1 v i i.rev) with width := w+1}
    let N := volume prime v
    let entry : Graph.Block common prime := Blocks.seqB LeafRoutines.offsets (Blocks.seqB Blocks.push LeafRoutines.view)
    let leave : Graph.Block common prime := Blocks.seqB Blocks.restore LeafRoutines.advance
    let record := (Fin.natAddEmb common (m := 24)).trans ((Fin.castAddEmb 31).trans (Fin.castAddEmb work))
    let rep := fun count roles' (D : Stacks ((host+31)+work) prime) =>
      RepT (CommonBank.bank roles' (Routines.hdr v) f p node scalar (Family.leafC (w+1) arity d count) st)
        (fun k => D.L (((k.castAdd 24).castAdd 31).castAdd work))
        (fun k => D.R (((k.castAdd 24).castAdd 31).castAdd work))
    let clean := fun (D : Stacks ((host+31)+work) prime) => ∀ (k : Fin work) x,
      readAt blank (D.L (k.natAdd (host+31))) (D.R (k.natAdd (host+31))) x = blank
    ∀ (ef : entry.tapes ≤ common+work) (xf : leave.tapes ≤ common+work)
      (eqs : entry.states ≤ Q) (xqs : leave.states ≤ Q) (word : Fin N → ZMod 2) (body : F → Pr F ((host+31)+work) Q prime U)
      (u : HS _ Q prime U) (S : Stacks _ prime) (pivotTail parentTail : List (Fin (prime+4))),
      roles.head io = 0 → roles.tape io = leafBitTape (List.ofFn word) → rep (i.val+1) roles S → clean S →
      (∀ k : Fin 31, S.L ((k.natAdd host).castAdd work) = [] ∧ S.R ((k.natAdd host).castAdd work) = []) →
      S.R (record 18) = [] →
      PackedLeafInputs (goodChildPorts.trans record) M.size parent pivot S pivotTail parentTail →
      ∃ next : Fin N → ZMod 2, ∃ z D n, z.user = u.user ∧
        n ≤ (1+(1800*volume prime v*(entry.tapes+5)+6))+(1+(weightedLeafCost (volume prime view) view.width (LeafCore.core io).tapes
          (packedLeafPush (F := Empty) (U := U) io Empty.elim)+
          ((1000*(prime+1)+8*(i.val+j.val))*(2*(prime.size+1)^2))*M))+(1+(200*volume prime v*(leave.tapes+5)+6)) ∧
        Exec body (packedCoordinateProgram io j.val i.val ef xf fits eqs xqs cap) (mk u S) n (mk z D) ∧
        rep i.val (SharedPlacementAlphabet.setTape roles io (leafBitTape (List.ofFn next)) 0) D ∧ clean D ∧
        (∀ k : Fin 55, D.L ((k.natAdd common).castAdd work) = S.L ((k.natAdd common).castAdd work) ∧
          D.R ((k.natAdd common).castAdd work) = S.R ((k.natAdd common).castAdd work)) ∧
        ∀ a < view.beforeRows, ∀ row < view.rows, ∀ pre < view.beforeH, ∀ mid < view.between,
          ∀ post < view.afterD, ∀ h t : ZMod M,
          ext next (index prime view a row pre ((parent j*pivot i)*t).val mid ((parentInv*Ring.inverse (pivot i))*h).val post) =
            ext word (index prime view a row pre h.val mid t.val post) := by
  intro common host M view N entry leave record rep clean ef xf eqs xqs word body u S pivotTail parentTail head input initial blank arithmetic spare archives
  let address := fun (next : Fin N → ZMod 2) =>
        ∀ a < view.beforeRows, ∀ row < view.rows, ∀ pre < view.beforeH, ∀ mid < view.between,
          ∀ post < view.afterD, ∀ h t : ZMod M,
          ext next (index prime view a row pre ((parent j*pivot i)*t).val mid ((parentInv*Ring.inverse (pivot i))*h).val post) =
            ext word (index prime view a row pre h.val mid t.val post)
  let changed := fun (next : Fin N → ZMod 2) => SharedPlacementAlphabet.setTape roles io (leafBitTape (List.ofFn next)) 0
  let effect := fun r => ∃ next, r = changed next ∧ address next
  have viewPos : view.Positive := child_positive M 1 1 v i i.rev
    (pow_pos Networks.Shared50ModularControl.prime_prime.pos _) (by decide) (one_dvd _) positive
  have size : ((view.beforeRows*view.rows*view.beforeH)*M*view.between)*(M*view.afterD) = N := by
    let logical := {v with width := d}
    have same := child_volume_div M 1 1 logical i i.rev (by simp [logical]) (by decide) (one_dvd _)
    rw [Nat.div_one] at same
    calc
      _ = volume M (child M 1 1 logical i i.rev) := by simp [view,volume,child,logical,Nat.mul_assoc]
      _ = volume M logical := same
      _ = N := by simp [N,logical,volume,width,M,pow_mul,Nat.mul_comm d (w+1)]
  let localWord := fun k => word (Fin.cast size k)
  obtain ⟨sameCells,sameRead⟩ := coordinateWord_cast size word
  let localLeaf := packedLeafProgram (F := Empty) (U := U) io j.val i.val
  let middle := statePlacedNormalized (packedFramePorts (host := host) fits) cap
    (Nat.lt_of_lt_of_le (by decide : 0 < 217) (leafCoreCapacity io)) (Empty.elim : Empty → F) localLeaf
  obtain ⟨r,z,D,t,⟨next,rfl,addr⟩,user,bound,run,out,free,keep⟩ :=
    coordinateCall_exec roles v positive (w+1) arity (Nat.succ_pos _) width i f p node scalar st freeNode
      effect ef xf eqs xqs body middle u S initial blank (by
        intro y E inside cleanE kept
        obtain ⟨next,z,D,t,user,bound,run,out,free,keep,addr⟩ := packedCoordinateMiddle_exec
          view viewPos w rfl parent j parentInv reciprocal pivot i unit io roles f p _ scalar _ st fits cap
          localWord body y S E pivotTail parentTail head (by simpa only [localWord,sameCells] using input) inside cleanE kept arithmetic spare archives
        let result := fun k => next (Fin.cast size.symm k)
        obtain ⟨cells,read⟩ := coordinateWord_cast size.symm next
        refine ⟨changed result,z,D,t,⟨result,rfl,?_⟩,user,bound,run,?_,free,keep⟩
        · simpa only [address,result,read,localWord,sameRead] using addr
        · have bankEq : changed result = SharedPlacementAlphabet.setTape roles io (leafBitTape (List.ofFn next)) 0 :=
            congrArg (fun xs => SharedPlacementAlphabet.setTape roles io (leafBitTape xs) 0) cells
          rw [bankEq]
          exact out)
  exact ⟨next,z,D,t,user,bound,run,out,free,keep,addr⟩

/-- Execute every packed coordinate from the initial rank down to counter zero. -/
theorem packedCoordinates_exec [M8.Machine.Net] {T d work Q : ℕ} {F U : Type}
    (v : Descriptor) (positive : v.Positive) (w : ℕ) (width : v.width = d*(w+1))
    (parent parentInv : Fin d → ZMod (prime^(w+1)))
    (reciprocal : ∀ i, parent i * parentInv i = 1) (pivot : Fin d → ZMod (prime^(w+1)))
    (unit : ∀ i, IsUnit (pivot i)) (io : Fin T) (roles : Tapes T prime)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime)
    (arity : ℕ) (st : Tapes 2 prime) (freeNode : Family.NodeFree node)
    (fits : LeafCore.small ≤ work) (cap : (LeafCore.core io).states ≤ Q) :
    let common := CommonBank.count T
    let host := common+24
    let M := prime^(w+1)
    let view := fun i : Fin d => {(RecursiveInterchangeLayout.child M 1 1 v i i.rev) with width := w+1}
    let N := volume prime v
    let entry : Graph.Block common prime := Blocks.seqB LeafRoutines.offsets (Blocks.seqB Blocks.push LeafRoutines.view)
    let leave : Graph.Block common prime := Blocks.seqB Blocks.restore LeafRoutines.advance
    let record := (Fin.natAddEmb common (m := 24)).trans ((Fin.castAddEmb 31).trans (Fin.castAddEmb work))
    let rep := fun count roles' (D : Stacks ((host+31)+work) prime) =>
      RepT (CommonBank.bank roles' (Routines.hdr v) f p node scalar (Family.leafC (w+1) arity d count) st)
        (fun k => D.L (((k.castAdd 24).castAdd 31).castAdd work))
        (fun k => D.R (((k.castAdd 24).castAdd 31).castAdd work))
    let clean := fun (D : Stacks ((host+31)+work) prime) => ∀ (k : Fin work) x,
      readAt blank (D.L (k.natAdd (host+31))) (D.R (k.natAdd (host+31))) x = blank
    let payload := fun x : Fin N → ZMod 2 => SharedPlacementAlphabet.setTape roles io (leafBitTape (List.ofFn x)) 0
    let weight := fun i => parent i*pivot i
    let inv := fun i => parentInv i*Ring.inverse (pivot i)
    let logical := {v with width := d}
    let addr := fun a row pre mid post (x : IntegerMultBounds.Swap.Shear.State (Fin d) (ZMod M)) =>
      index M logical a row pre (FlatCoordinateLayout.rank x.1).val mid (FlatCoordinateLayout.rank x.2).val post
    ∀ (ef : entry.tapes ≤ common+work) (xf : leave.tapes ≤ common+work)
      (eqs : entry.states ≤ Q) (xqs : leave.states ≤ Q) (word : Fin N → ZMod 2) (body : F → Pr F ((host+31)+work) Q prime U)
      (u : HS _ Q prime U) (S : Stacks _ prime) (pivotTail parentTail : List (Fin (prime+4))),
      rep d (payload word) S → clean S →
      (∀ k : Fin 31, S.L ((k.natAdd host).castAdd work) = [] ∧ S.R ((k.natAdd host).castAdd work) = []) →
      S.R (record 18) = [] →
      PackedLeafInputs (goodChildPorts.trans record) M.size parent pivot S pivotTail parentTail →
      let call := fun i : Fin d => packedCoordinateProgram (F := F) (U := U) io i.val i.val ef xf fits eqs xqs cap
      ∃ next : Fin N → ZMod 2, ∃ z D t, z.user = u.user ∧ t ≤ packedCoordinatesTime d N w (LeafCore.core io).tapes
          (packedLeafPush (F := Empty) (U := U) io Empty.elim) entry.tapes leave.tapes ∧
        Exec body (Prog.seqList ((List.finRange d).reverse.map call)) (mk u S) t (mk z D) ∧
        rep 0 (payload next) D ∧ clean D ∧
        (∀ k : Fin 55, D.L ((k.natAdd common).castAdd work) = S.L ((k.natAdd common).castAdd work) ∧
          D.R ((k.natAdd common).castAdd work) = S.R ((k.natAdd common).castAdd work)) ∧
        ∀ a < v.beforeRows, ∀ row < v.rows, ∀ pre < v.beforeH, ∀ mid < v.between, ∀ post < v.afterD, ∀ x,
          ext next (addr a row pre mid post (Weighted.child d weight inv x)) = ext word (addr a row pre mid post x) := by
  intro common host M view N entry leave record rep clean payload weight inv logical addr ef xf eqs xqs word body u S pivotTail parentTail initial free arithmetic spare archives call
  let budget := fun i : Fin d => (1+(1800*N*(entry.tapes+5)+6))+(1+(weightedLeafCost (volume prime (view i)) (w+1)
      (LeafCore.core io).tapes (packedLeafPush (F := Empty) (U := U) io Empty.elim)+
      ((1000*(prime+1)+8*(i.val+i.val))*(2*(prime.size+1)^2))*M))+(1+(200*N*(leave.tapes+5)+6))
  let keep := fun (E : Stacks ((host+31)+work) prime) => ∀ k : Fin 55,
    E.L ((k.natAdd common).castAdd work) = S.L ((k.natAdd common).castAdd work) ∧
    E.R ((k.natAdd common).castAdd work) = S.R ((k.natAdd common).castAdd work)
  let ready := fun count E (read : ℕ → ZMod 2) => ∃ x : Fin N → ZMod 2,
    read = ext x ∧ rep count (payload x) E ∧ clean E ∧ keep E
  have units (i : Fin d) : weight i * inv i = 1 := by
    dsimp only [weight,inv]
    rw [mul_mul_mul_comm,reciprocal,Ring.mul_inverse_cancel _ (unit i),one_mul]
  have step := weightedCoordinates_exec logical rfl (q := prime) (w := w+1) rfl weight inv units body call budget ready
  obtain ⟨z,D,out,t,user,bound,run,⟨next,rfl,finalBank,blank,kept⟩,address⟩ := step (by
    intro i y E read current
    obtain ⟨x,rfl,bank,blank,kept⟩ := current
    have right (k : Fin 24) : E.R (record k) = S.R (record k) := (kept (k.castAdd 31)).2
    have empty (k : Fin 31) : E.L ((k.natAdd host).castAdd work) = [] ∧ E.R ((k.natAdd host).castAdd work) = [] := by
      have h := kept (k.natAdd 24)
      have eq : ((k.natAdd 24).natAdd common : Fin (common+55)) = k.natAdd host := by
        apply Fin.ext
        simp [host,Nat.add_assoc]
      rw [eq] at h
      exact ⟨h.1.trans (arithmetic k).1,h.2.trans (arithmetic k).2⟩
    have inputs : PackedLeafInputs (goodChildPorts.trans record) M.size parent pivot E pivotTail parentTail :=
      ⟨(right _).trans archives.weights,(right _).trans archives.pivots,(right _).trans archives.modulus,
       (right _).trans archives.one,(congrArg List.length (right _)).trans archives.clock,
       fun k h => (right _).trans (archives.scratch k h)⟩
    obtain ⟨next,z,D,t,hz,ht,run,result,cleanD,keepD,addrD⟩ :=
      packedCoordinate_exec v positive w width parent i (parentInv i) (reciprocal i) pivot i (unit i) io
        (payload x) f p node scalar arity st freeNode fits cap ef xf eqs xqs x body y E pivotTail parentTail
        (by simp [payload,SharedPlacementAlphabet.setTape]) (by simp [payload,SharedPlacementAlphabet.setTape])
        bank blank empty ((right _).trans spare) inputs
    refine ⟨z,D,ext next,t,hz,ht,run,⟨next,rfl,?_,cleanD,?_⟩,?_⟩
    · simpa only [payload,SharedPlacementAlphabet.setTape,Function.update_idem] using result
    · intro k
      exact ⟨(keepD k).1.trans (kept k).1,(keepD k).2.trans (kept k).2⟩
    · simpa only [logical,weight,inv,child,Nat.div_one] using addrD) u S (ext word)
      ⟨word,rfl,initial,free,fun _ => ⟨rfl,rfl⟩⟩
  have same : volume M logical = N := by
    simp [N,logical,volume,width,M,pow_mul,Nat.mul_comm d (w+1)]
  have charge := weightedCoordinates_cost logical (r := d) rfl positive w (LeafCore.core io).tapes
    (packedLeafPush (F := Empty) (U := U) io Empty.elim) entry.tapes leave.tapes
  dsimp only at charge
  rw [same] at charge
  exact ⟨next,z,D,t,user,bound.trans charge,run,finalBank,blank,kept,address⟩

end

end IntegerMultBounds.MathlibTM2.Cover.Fallback
