module

public import IntegerMultBounds.MathlibTM2.M6.BitOrdinaryDirectoryOutgoing

/-! Traverse the returned directory once. Only live ordinary rows need an outgoing transform. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover Cover.Fallback Stack Host LabelTraversal
open Shared50ModularControl (prime)
local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

theorem outgoingDirectoryScan_exec {P U : Type} {m K w W N Q : ℕ}
    (body : P → Pr P (66+K) Q prime U) (good : Pr P (66+K) Q prime U)
    (v : RecursiveInterchangeLayout.Descriptor) (proj : Matrix (Fin m) (Fin m) ℚ)
    (weights : Fin m → ZMod (prime^(w+1))) (prefixes : ℕ → List (Fin (prime+4)))
    (archiveTail ownerTail : List (Fin (prime+4))) (rs : List ℕ) (live bad : ℕ → Bool)
    (input : ℕ → Fin N → ZMod 2) (effect : ℕ → (Fin N → ZMod 2) → Prop) (price : ℕ → ℕ)
    (u : HS ((66+K)+5) Q prime U) (S : Stacks ((66+K)+5) prime) :
    let caller := Fin.castAddEmb (n := 66) K
    let bank := fun i : Fin (66+K) => i.castAdd 5
    let reg := fun j : Fin 5 => Fin.natAdd (66+K) j
    let ready := DirectoryReady v proj w W (prime^(w+1)).size W.size weights prefixes archiveTail (fun _ => [])
    let flags := fun (f : ℕ → Bool) (xs : List ℕ) => xs.map (fun j => bitSymbol (a := prime) (f j))
    let bits := fun word : Fin N → ZMod 2 => payloadWord (SparseRoleCircuit.encode ∘ word)
    let slots : Fin 7 ↪ Fin 58 := ⟨![45,46,2,47,48,44,49],by decide⟩
    let scan := ((goodRecordScanPorts.trans slots).trans (Fin.castAddEmb 8)).trans caller
    let skip : Pr P (66+K) Q prime U := readWithSuccessorClock (scan 1) (advanceDirectory m scan)
    let active := fun j => live j && !bad j
    let dispatch := ownerDispatch (caller 57) (caller 56) good skip skip
    let cursor := fun j => 1+(4*(prefixes j).length+4+(m*m*(4*(w+1)+4)+1)+1)
    let cost := fun j => (if active j then price j else cursor j)+(if live j then 4 else 3)
    let start := embStk bank S
    ready start rs → start.R (caller 57) = flags live rs → start.R (caller 56) = flags bad rs →
    S.R (reg 0) = rs.flatMap (bits ∘ input) ++ ownerTail → S.R (reg 1) = [] → (S.R (reg 2)).length = N →
    S.R (reg 3) = [] → S.R (reg 4) = [] → (∀ j, readAt blank (start.L (caller 24)) (start.R (caller 24)) j = blank) →
    (∀ j ∈ rs, ∀ xs (a : HS (66+K) Q prime U) (A : Stacks (66+K) prime), live j = true → bad j = false →
      ready A (j::xs) → RecordPayload (caller 24) (fun _ => blank) 0 (input j) A →
      ∃ z D t out, z.user = a.user ∧ t ≤ price j ∧ Exec body good (mk a A) t (mk z D) ∧
        ready D xs ∧ RecordPayload (caller 24) (fun _ => blank) 0 out D ∧ effect j out ∧
        D.R (caller 57) = A.R (caller 57) ∧ D.R (caller 56) = A.R (caller 56) ∧ D.R (caller 47) = A.R (caller 47)) →
    ∃ z F n rows, z.user = u.user ∧
      n ≤ (rs.map (fun j => 6*N+6+cost j+(4*N+4))).sum+2*rs.length+2+(2*(rs.length*N)+2) ∧
      Exec (fun f => embProg bank id (body f)) (packedOwner (caller 24) (caller 57) dispatch) (mk u S) n (mk z F) ∧
      List.Forall₂ (fun j tape => ∃ word, (if active j then effect j word else word = input j) ∧ tape = bits word) rs rows ∧
      F.L (reg 0) = S.L (reg 0) ∧ F.R (reg 0) = rows.flatten ++ ownerTail ∧ F.R (reg 1) = [] ∧
      (F.R (reg 2)).length = N ∧ F.R (reg 3) = [] ∧ F.R (reg 4) = [] ∧ ready (embStk bank F) [] ∧
      F.R (bank (caller 57)) = [] ∧ F.R (bank (caller 56)) = [] ∧ F.R (bank (caller 47)) = S.R (bank (caller 47)) := by
  intro caller bank reg ready flags bits slots scan skip active dispatch cursor cost start directory ls bs queue acc width saved tmp empty run
  let inv := fun (xs : List ℕ) (A : Stacks (66+K) prime) =>
    ready A xs ∧ A.R (caller 57) = flags live xs ∧ A.R (caller 56) = flags bad xs ∧ A.R (caller 47) = start.R (caller 47) ∧ xs ⊆ rs
  obtain ⟨z,F,n,rows,hu,time,step,_,ordered,left,right,clear,count,saveEnd,tmpEnd,done,lsEnd,bsEnd,widthEnd,_⟩ :=
    packedOwner_exec ownerTail body (caller 24) (caller 57) dispatch input
      (fun j word => if active j then effect j word else word = input j) cost inv rs u S (by
        intro xs A h
        rw [h.2.1]
        cases xs <;> rfl) ⟨⟨directory,ls,bs,rfl,List.Subset.refl _⟩,rfl,queue,acc,width,saved,tmp,empty⟩ (by
      intro j xs A a state loaded payload
      obtain ⟨dir,liveBits,badBits,widthBefore,subset⟩ := state
      let E := {loaded with R := Function.update (Function.update loaded.R (caller 57) (flags live xs)) (caller 56) (flags bad xs)}
      let b := {a with flag := bad j}
      have dirE : ready E (j::xs) := DirectoryReady.updateSelector 56 (by decide) (by decide) _
        (DirectoryReady.updateSelector 57 (by decide) (by decide) _ (directoryReady_updatePayload dir _))
      have on (i : Fin 66) (off : i ≠ 57 ∧ i ≠ 56) : E.R (caller i) = loaded.R (caller i) :=
        (Function.update_of_ne (caller.injective.ne off.2) ..).trans (Function.update_of_ne (caller.injective.ne off.1) ..)
      have inputE : RecordPayload (caller 24) (fun _ => blank) 0 (input j) E := by
        intro k
        change readAt blank (loaded.L _) (E.R (caller 24)) _ = _
        rw [on 24 (by decide)]
        exact payload k
      have masks : E.R (caller 57) = flags live xs ∧ E.R (caller 56) = flags bad xs := by
        simp [E]
      have keep (i : Fin 66) (hi : i ≠ 24) : loaded.R (caller i) = A.R (caller i) :=
        Function.update_of_ne (caller.injective.ne hi) ..
      have widthE : E.R (caller 47) = start.R (caller 47) :=
        (on 47 (by decide)).trans ((keep 47 (by decide)).trans widthBefore)
      have branch : ∃ z D n out, z.user = a.user ∧ n ≤ (if active j then price j else cursor j) ∧
          Exec body (if live j then (if bad j then skip else good) else skip) (mk b E) n (mk z D) ∧
          (if active j then effect j out else out = input j) ∧ RecordPayload (caller 24) (fun _ => blank) 0 out D ∧ inv xs D := by
        by_cases selected : active j = true
        · obtain ⟨l,h⟩ := Bool.and_eq_true_iff.mp selected
          have noBad : bad j = false := by simpa using h
          obtain ⟨z,D,n,out,user,paid,exec,next,read,ok,lm,bm,wm⟩ :=
            run j (subset List.mem_cons_self) xs b E l noBad dirE inputE
          simp only [selected,l,noBad,ite_true,Bool.false_eq_true,ite_false]
          exact ⟨z,D,n,out,user,paid,exec,ok,read,next,lm.trans masks.1,bm.trans masks.2,wm.trans widthE,fun _ h => subset (List.mem_cons_of_mem j h)⟩
        · have prog : (if live j then (if bad j then skip else good) else skip) = skip := by
            cases l : live j <;> cases h : bad j <;> simp_all only [active,Bool.and_true,Bool.not_true,
              Bool.not_false,Bool.and_false,Bool.false_eq_true,ite_false,ite_true,not_true_eq_false]
          obtain ⟨z,user,exec,next⟩ := DirectoryReady.advancePadding body b dirE rfl
          simp only [selected,prog]
          refine ⟨z,_,cursor j,input j,user,le_rfl,exec,rfl,?_,next,?_,?_,?_,fun _ h => subset (List.mem_cons_of_mem j h)⟩
          · intro k
            change readAt blank (E.L _) (Function.update E.R (caller 46) (xs.flatMap (LabelDirectory.entry prefixes m (w+1)) ++ archiveTail) (caller 24)) _ = _
            rw [Function.update_of_ne (caller.injective.ne (by decide : (24 : Fin 66) ≠ 46))]
            exact inputE k
          · exact (Function.update_of_ne (caller.injective.ne (by decide : (57 : Fin 66) ≠ 46)) (xs.flatMap (LabelDirectory.entry prefixes m (w+1)) ++ archiveTail) E.R).trans masks.1
          · exact (Function.update_of_ne (caller.injective.ne (by decide : (56 : Fin 66) ≠ 46)) (xs.flatMap (LabelDirectory.entry prefixes m (w+1)) ++ archiveTail) E.R).trans masks.2
          · exact (Function.update_of_ne (caller.injective.ne (by decide : (47 : Fin 66) ≠ 46)) (xs.flatMap (LabelDirectory.entry prefixes m (w+1)) ++ archiveTail) E.R).trans widthE
      obtain ⟨z,D,t,out,user,paid,exec,ok,read,next,liveNext,badNext,widthNext,rem⟩ := branch
      have step := ownerDispatch_exec body (caller 57) (caller 56) (caller.injective.ne (by decide))
        good skip skip (live j) (bad j) a loaded (flags live xs) (flags bad xs)
        ((keep 57 (by decide)).trans liveBits) ((keep 56 (by decide)).trans badBits) exec
      refine ⟨z,D,_,out,user,Nat.add_le_add_right paid _,step,ok,read,directoryReady_updatePayload next _,?_,?_,?_,rem⟩
      · exact (Function.update_of_ne (caller.injective.ne (by decide : (57 : Fin 66) ≠ 24)) ((D.R (caller 24)).drop N) D.R).trans liveNext
      · exact (Function.update_of_ne (caller.injective.ne (by decide : (56 : Fin 66) ≠ 24)) ((D.R (caller 24)).drop N) D.R).trans badNext
      · exact (Function.update_of_ne (caller.injective.ne (by decide : (47 : Fin 66) ≠ 24)) ((D.R (caller 24)).drop N) D.R).trans widthNext)
  exact ⟨z,F,n,rows,hu,time,step,ordered,left,right,clear,count,saveEnd,tmpEnd,done,lsEnd,bsEnd,widthEnd⟩

private theorem ofFn_cast_payload {V N : ℕ} (size : V = N) (word : Fin V → ZMod 2) :
    payloadWord (SparseRoleCircuit.encode ∘ (fun i => word (i.cast size.symm))) =
      payloadWord (SparseRoleCircuit.encode ∘ word) := by
  subst N
  rfl

open GoodForm FlatCoordinateLayout Matrix M8.Exchange M8.ReversedExchange IntegerMultBounds.Swap.Shear
open IntegerMultBounds.Swap.Modular GoodChildLayout

/-- Pack the outgoing scan into one tape word. Inactive rows inherit the action
already proved at recursive return, since the outgoing scan copies those rows. -/
theorem outgoingOwnerRows_pack {R N V total : ℕ} (width : V = N) (volume : R*N = total)
    (active : ℕ → Bool) (returned : ℕ → Fin V → ZMod 2)
    (ordinary bypass : ℕ → (Fin N → ZMod 2) → Prop)
    {rows : List (List (Fin (prime+4)))}
    (restored : ∀ j : Fin R, active j = false → ∃ word, bypass j word ∧
      returned j = fun i => word (i.cast width))
    (scanned : List.Forall₂ (fun j tape => ∃ word,
      (if active j then ordinary j word else word = fun i => returned j (i.cast width.symm)) ∧
      tape = payloadWord (SparseRoleCircuit.encode ∘ word)) (List.range R) rows) :
    ∃ output : Fin total → ZMod 2,
      (∀ j : Fin R, if active j then ordinary j (ownerRow volume output j)
        else bypass j (ownerRow volume output j)) ∧
      rows.flatten = payloadWord (SparseRoleCircuit.encode ∘ output) := by
  obtain ⟨output,action,packed⟩ := ownerRows_pack volume scanned
  refine ⟨output,fun j => ?_,packed⟩
  have row := action j
  cases h : active j with
  | true => simpa [h] using row
  | false =>
    obtain ⟨word,ok,read⟩ := restored j h
    have same : ownerRow volume output j = word := by simpa [h,read] using row
    simpa [h,same] using ok

/-- Execute the outgoing scan on the words returned by the batched transpose.
Each active row recovers its original word at the projector-transformed addresses. -/
theorem generatedOutgoingScan_exec [M8.Machine.Net] {P U : Type} {r g w W common work : ℕ}
    (v : RecursiveInterchangeLayout.Descriptor) :
    let m := r+g
    let hr := Nat.le_add_right r g
    let K := common+24+31+work
    let M := prime^(w+1)
    let N := M^(m+m)*W
    let V := RecursiveInterchangeLayout.volume prime (ordinaryChildDescriptor r g w W)
    ∀ (proj : Matrix (Fin m) (Fin m) ℚ) (_rank : proj.rank = r) (_dim : m = 64)
      (_idem : proj*proj = proj) (factor : IntegerMultBounds.Swap.LowerTriangular.Factorization Finset.univ Finset.univ proj)
      (_small : ∀ k ∈ factorizationDenominators factor, k < prime)
      (weights : Fin m → ZMod M) (_unit : ∀ i, IsUnit (weights i)) (_hW : 0 < W)
      (prefixes : ℕ → List (Fin (prime+4))) (archiveTail ownerTail : List (Fin (prime+4))) (R : ℕ)
      (pool : (RingFormula.conjugationDepth m+1)*13 ≤ work) (room : 58+(rowSwapBlock.tapes+35+1) ≤ K)
      (body : P → Pr P (66+K) columnCapacity prime U) (u : HS ((66+K)+5) columnCapacity prime U)
      (S : Stacks ((66+K)+5) prime) (original : ℕ → Fin N → ZMod 2) (returned : ℕ → Fin V → ZMod 2) (c : ℕ),
    let rs := List.range R
    let full := ordinaryCaller (by omega : 58 ≤ K)
    let machine := GoodChildLayout.parent.trans (parentWithWeights.trans full)
    let caller := Fin.castAddEmb (n := 66) K
    let bank := fun i : Fin (66+K) => i.castAdd 5
    let reg := fun j : Fin 5 => Fin.natAdd (66+K) j
    let start := embStk bank S
    let ready := DirectoryReady v proj w W M.size W.size weights prefixes archiveTail (fun _ => [])
    let reduced := reduce M proj
    let live := LabelStock.live m (w+1) 1
    let bad := fun j => fallbackBit proj.rank_le_height reduced (physicalLabel m (w+1) j)
    let active := fun j => live j && !bad j
    let G := fun j => let label := physicalLabel m (w+1) j; label*reduced*label⁻¹
    let inv := fun i => Ring.inverse (weights i)
    let pos := ordinaryRecursivePosition r g w W
    let size := ordinaryChildVolume r g w W
    let prog := outgoingRowProgram (P := P) (U := U) (common := common) r g pool room
    let privateTapes := (List.finRange (66+K)).filter (fun i => 58 ≤ i.val)
    let slots : Fin 7 ↪ Fin 58 := ⟨![45,46,2,47,48,44,49],by decide⟩
    let scan := ((goodRecordScanPorts.trans slots).trans (Fin.castAddEmb 8)).trans caller
    let skip : Pr P (66+K) columnCapacity prime U := readWithSuccessorClock (scan 1) (advanceDirectory m scan)
    let dispatch := ownerDispatch (caller 57) (caller 56) ((prog.seq (clearWorkTapes privateTapes)).seq skip) skip skip
    let cost := fun j => let base := outgoingRowTime U machine r g w W (prefixes j).length
                         let cursor := 1+(4*(prefixes j).length+4+(m*m*(4*(w+1)+4)+1)+1)
                         (if active j then base+(4*privateTapes.length+1+privateTapes.length*(6*(c*base)))+cursor else cursor) +
                           (if live j then 4 else 3)
    let effect := fun j (word : Fin N → ZMod 2) => ∀ x k,
      let y := transform (diagonal weights) 1 (revExchangeOf (rev m) (G j) (transform (diagonal inv) 1 x))
      word (index (Fin.append y.1 y.2) k) = original j (index (Fin.append x.1 x.2) k)
    Fast.Main.mnProgPush prog ≤ c → (∀ f, Fast.Main.mnProgPush (body f) ≤ c) →
    (∀ j ∈ rs, live j = true → bad j = false →
      ∃ minor : ∀ i (hi : i < r), IsUnit (lead (i+1) (lt_of_lt_of_le hi hr) (G j)).det,
      ∃ before, IncomingRowEffect (w := w) (W := W) hr (G j) minor weights inv (original j) before ∧
        returned j = ordinaryChildOutput (r := r) (g := g) (w := w) before ∘ pos) →
    ready start rs → start.R (caller 57) = rs.map (fun j => bitSymbol (live j)) →
    start.R (caller 56) = rs.map (fun j => bitSymbol (bad j)) →
    S.R (reg 0) = rs.flatMap (fun j => payloadWord (SparseRoleCircuit.encode ∘ returned j)) ++ ownerTail →
    S.R (reg 1) = [] → (S.R (reg 2)).length = N → S.R (reg 3) = [] → S.R (reg 4) = [] →
    (∀ j, readAt blank (start.L (caller 24)) (start.R (caller 24)) j = blank) →
    ∀ (bypass : ℕ → (Fin N → ZMod 2) → Prop),
    (∀ j : Fin R, active j = false → ∃ word, bypass j word ∧ returned j = fun i => word (i.cast size)) →
    ∃ z F n, ∃ output : Fin (R*N) → ZMod 2, z.user = u.user ∧
      n ≤ (rs.map (fun j => 6*N+6+cost j+(4*N+4))).sum+2*rs.length+2+(2*(rs.length*N)+2) ∧
      Exec (fun f => embProg bank id (body f)) (packedOwner (caller 24) (caller 57) dispatch) (mk u S) n (mk z F) ∧
      (∀ j : Fin R, if active j then effect j (ownerRow rfl output j) else bypass j (ownerRow rfl output j)) ∧
      F.L (reg 0) = S.L (reg 0) ∧ F.R (reg 0) = payloadWord (SparseRoleCircuit.encode ∘ output) ++ ownerTail ∧ F.R (reg 1) = [] ∧
      (F.R (reg 2)).length = N ∧ F.R (reg 3) = [] ∧ F.R (reg 4) = [] ∧ ready (embStk bank F) [] ∧
      F.R (bank (caller 57)) = [] ∧ F.R (bank (caller 56)) = [] ∧ F.R (bank (caller 47)) = S.R (bank (caller 47)) := by
  intro m hr K M N V proj rank dim idem factor small weights unit hW prefixes archiveTail ownerTail R pool room body
    u S original returned c rs full machine caller bank reg start ready reduced live bad active G inv pos size prog
    privateTapes slots scan skip dispatch cost effect bounded calls classified directory liveBits badBits queue acc width saved tmp blankPort bypass restored
  let input := fun j (i : Fin N) => returned j (i.cast size.symm)
  let price := fun j => let base := outgoingRowTime U machine r g w W (prefixes j).length
                        base+(4*privateTapes.length+1+privateTapes.length*(6*(c*base)))+
                          (1+(4*(prefixes j).length+4+(m*m*(4*(w+1)+4)+1)+1))
  obtain ⟨z,F,n,rows,user,time,run,actions,left,right,rest⟩ := outgoingDirectoryScan_exec body ((prog.seq (clearWorkTapes privateTapes)).seq skip) v proj weights prefixes
    archiveTail ownerTail rs live bad input effect price u S directory liveBits badBits (by
    change S.R (reg 0) = rs.flatMap (fun j => payloadWord (SparseRoleCircuit.encode ∘ (fun i => returned j (i.cast size.symm)))) ++ ownerTail
    rw [queue]
    exact congrArg (fun f => rs.flatMap f ++ ownerTail) (funext (fun j => (ofFn_cast_payload size (returned j)).symm))) acc width saved tmp blankPort (by
    intro j hj xs a A l b dir read
    obtain ⟨minor,before,inc,returnedEq⟩ := classified j hj l b
    have payload : RecordPayload (full 24) (fun _ => blank) 0
        (ordinaryChildOutput (r := r) (g := g) (w := w) before ∘ pos) A := by
      rw [← returnedEq]
      intro k
      have h := read k
      rw [List.map_ofFn] at h ⊢
      exact h.trans (congrArg (fun xs => RadixToBinary.binaryEncoding.encode (putWord (fun _ => blank) 0 xs k))
        (List.ofFn_congr size (SparseRoleCircuit.encode ∘ returned j)).symm)
    obtain ⟨z,D,n,out,user,time,run,next,result,action,frame⟩ := generatedLiveOutgoingRow_exec
      (common := common) v proj rank dim weights unit prefixes archiveTail (fun _ => []) j xs pool room body a A
      idem factor small dir l b hW (original j) before minor inc payload rfl c bounded calls
    exact ⟨z,D,n,out,user,time,run,next,result,action,frame 57 (by decide),frame 56 (by decide),frame 47 (by decide)⟩)
  obtain ⟨output,action,encoded⟩ := outgoingOwnerRows_pack size rfl active returned effect bypass restored actions
  exact ⟨z,F,n,output,user,time,run,action,left,by rw [right,encoded],rest⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
