module

public import IntegerMultBounds.MathlibTM2.M6.BitOrdinaryIncomingPlacement

/-! Execute the live packed row from generated directory data. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover Cover.Fallback Stack Host
open GoodForm FlatCoordinateLayout LabelTraversal Matrix M8.Exchange M8.ReversedExchange
open IntegerMultBounds.Swap.Shear HeadPivotLayout HeadWidthLayout CrossWeightLayout GoodChildLayout
open Shared50ModularControl (prime)
local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

def IncomingRowEffect {m r w W : ℕ} (hr : r ≤ m)
    (G : Matrix (Fin m) (Fin m) (ZMod (prime^(w+1))))
    (minor : ∀ i (hi : i < r), IsUnit (lead (i+1) (lt_of_lt_of_le hi hr) G).det)
    (weights inv : Fin m → ZMod (prime^(w+1)))
    (word before : Fin ((prime^(w+1))^(m+m)*W) → ZMod 2) : Prop :=
  let M := prime^(w+1)
  let stage := stageAt G r hr minor r le_rfl
  let δ := fun t : Fin m => if t.val < r then stage.M t t else 1
  let δ' := fun t : Fin m => if t.val < r then Ring.inverse (stage.M t t) else 1
  let cross := kMat (pivotMatrix (revPivots m r))
    (rev m * stage.U * rev m * rev m * (stage.L * diagonal δ)) * diagonal (fun t => inv t * δ' t)
  let action := diagonal weights * stage.L' * diagonal inv
  ∀ (x y : Fin m → ZMod M) (k : Fin W), before (index (Fin.append (action.mulVec x)
    ((rev m * stage.U * rev m).mulVec y + cross.mulVec (action.mulVec x))) k) = word (index (Fin.append x y) k)

private theorem pivotWords_cast {m r a M : ℕ} [NeZero M] (G : Matrix (Fin m) (Fin m) (ZMod M))
    (hr : r ≤ m) (minor : ∀ i (hi : i < r), IsUnit (lead (i+1) (lt_of_lt_of_le hi hr) G).det)
    (eq : a = r) (H : ℕ) :
    (List.ofFn fun i : Fin r => binSyms (A := prime) H
      ((stageAt G r hr minor a (by omega)).M (i.cast eq.symm |>.castLE (by omega)) (i.cast eq.symm |>.castLE (by omega))).val).flatten =
    (List.ofFn fun i : Fin r => binSyms (A := prime) H
      ((stageAt G r hr minor r le_rfl).M (i.castLE hr) (i.castLE hr)).val).flatten := by
  subst a
  rfl

noncomputable def incomingRowProgram [M8.Machine.Net] {P U : Type} {common aux : ℕ} (r g : ℕ)
    (pool : (RingFormula.conjugationDepth (r+g)+1)*13 ≤ aux)
    (room : 58+(rowSwapBlock.tapes+35+1) ≤ common+24+31+aux) :
    Pr P (66+(common+24+31+aux)) columnCapacity prime U :=
    let m := r+g
    let hr : r ≤ m := Nat.le_add_right ..
    let K := common+24+31+aux
    let full := ordinaryCaller (by omega : 58 ≤ K)
    let bank := ordinaryPackingBank (by omega : 58 ≤ K)
    let ports := columnPorts.trans (correctionColumnPlacement bank (ordinaryPackingWork room) (ordinaryPackingWork_apart room))
    let machine := GoodChildLayout.parent.trans (parentWithWeights.trans full)
    let slots := stageBank (pivotSlots.trans full) r
    let src := directoryRecordMatrixSlot common aux
    let localCaller := Fin.castAddEmb (n := 66) K
    let write : Pr P (66+K) columnCapacity prime U := ((directoryRecordWriter m common pool).seq
      (if src = slots 15 then .act .done else moveRightOrdered src (localCaller 59) (slots 15))).seq (goodWeights prime r hr slots)
    let load : Pr P (66+K) columnCapacity prime U := packReciprocals prime (ordinaryReciprocalPorts.trans full) (full 54) (List.finRange m)
    let setup := write.seq (load.seq ((Node.umul (m*m) (full 2) (full 51) (full 0)).seq (bcopy (full 2) (full 33) (full 0) (full 1))))
    let cap : 217 ≤ columnCapacity := le_max_left ..
    let inc : Pr P (66+K) columnCapacity prime U := (stateLiftNormalize cap (by decide)).seq (stateLiftPr cap (by decide) Empty.elim (goodIncoming prime r hr machine))
    let is := ordinaryChildPackSchedule r g
    let pack : Pr P (66+K) columnCapacity prime U := statePlacedNormalized ports swapStates_fit swapStates_pos Empty.elim (packSchedule (m+m) is)
    setup.seq (inc.seq pack)

/-- Both nonexceptional branches consume one directory entry and return a word
indexed by the physical row size. Only a live row executes the packing pass. -/
theorem generatedIncomingRow_exec [M8.Machine.Net] {P U : Type} {r g w W common work : ℕ}
    (v : RecursiveInterchangeLayout.Descriptor) :
    let m := r+g
    let hr : r ≤ m := Nat.le_add_right ..
    let K := common+24+31+work
    let M := prime^(w+1)
    let H := M.size
    let J := W.size
    ∀ (proj : Matrix (Fin m) (Fin m) ℚ) (_rank : proj.rank = r)
      (weights : Fin m → ZMod M) (_unit : ∀ i, IsUnit (weights i))
      (prefixes : ℕ → List (Fin (prime+4))) (tail : List (Fin (prime+4)))
      (code : ℕ → List (Fin (prime+4))) (j : ℕ) (js : List ℕ)
      (pool : (RingFormula.conjugationDepth m+1)*13 ≤ work) (room : 58+(rowSwapBlock.tapes+35+1) ≤ K)
      (body : P → Pr P (66+K) columnCapacity prime U) (u : HS (66+K) columnCapacity prime U) (S : Stacks (66+K) prime),
    let full := ordinaryCaller (by omega : 58 ≤ K)
    let bank := ordinaryPackingBank (by omega : 58 ≤ K)
    let ports := columnPorts.trans (correctionColumnPlacement bank (ordinaryPackingWork room) (ordinaryPackingWork_apart room))
    let machine := GoodChildLayout.parent.trans (parentWithWeights.trans full)
    let label := physicalLabel m (w+1) j
    let reduced := IntegerMultBounds.Swap.Modular.reduce M proj
    let G := label*reduced*label⁻¹
    let caller := Fin.castAddEmb (n := 66) K
    let is := ordinaryChildPackSchedule r g
    let prog := incomingRowProgram (P := P) (U := U) (common := common) r g pool room
    let cost := ordinarySetupTime m r w H (prefixes j).length +
      (1+goodIncomingTime (A := prime) (U := U) Empty.elim machine prime w W H J r hr +
      (1+((is.map (fun i => completeSwapTime (P := Empty) (U := U) Empty.elim (m+m) i (i+1) w W H J)).sum+1)))
    let bad := fun k => fallbackBit proj.rank_le_height reduced (physicalLabel m (w+1) k)
    let schedules := fun (xs : List ℕ) => xs.flatMap fun k => if bad k then code k else []
    let ready := DirectoryReady v proj w W H J weights prefixes tail schedules
    let inv := fun i : Fin m => Ring.inverse (weights i)
    let live := LabelStock.live m (w+1) 1 j
    proj*proj = proj → ∀ f : IntegerMultBounds.Swap.LowerTriangular.Factorization Finset.univ Finset.univ proj,
    (∀ k ∈ IntegerMultBounds.Swap.Modular.factorizationDenominators f, k < prime) →
    ready S (j::js) → (live = true → fallbackBit proj.rank_le_height reduced label = false) → 0 < W →
    ∀ word : Fin (M^(m+m)*W) → ZMod 2, RecordPayload (caller 24) (fun _ => blank) 0 word S →
    let privateTapes := (List.finRange (66+K)).filter (fun i => 58 ≤ i.val)
    let scanSlots : Fin 7 ↪ Fin 58 := ⟨![45,46,2,47,48,44,49],by decide⟩
    let scan := ((goodRecordScanPorts.trans scanSlots).trans (Fin.castAddEmb 8)).trans caller
    let advance := readWithSuccessorClock (scan 1) (advanceDirectory m scan)
    ∀ c, Fast.Main.mnProgPush prog ≤ c → (∀ f, Fast.Main.mnProgPush (body f) ≤ c) →
    let cursorTime := 1+(4*(prefixes j).length+4+(m*m*(4*(w+1)+4)+1)+1)
    ∃ y D t out, y.user = u.user ∧
      t ≤ (if live then cost+(4*privateTapes.length+1+privateTapes.length*(6*(c*cost)))+cursorTime else cursorTime) ∧
      Exec body (if live then (prog.seq (clearWorkTapes privateTapes)).seq advance else advance) (mk u S) t (mk y D) ∧
      ready D js ∧ RecordPayload (caller 24) (fun _ => blank) 0 out D ∧
      (∀ k ∈ ([40,56,57] : List (Fin 66)), D.R (caller k) = S.R (caller k)) ∧
      (if live then ∃ minor : ∀ i (hi : i < r), IsUnit (lead (i+1) (lt_of_lt_of_le hi hr) G).det,
        ∃ before, IncomingRowEffect (w := w) (W := W) hr G minor weights inv word before ∧
          ∀ i, out (i.cast (ordinaryChildVolume r g w W)) = before (ordinaryRecursivePosition r g w W i)
       else out = word) := by
  intro m hr K M H J proj rank weights unit prefixes tail code j js pool room body u S full bank ports
    machine label reduced G caller is prog cost bad schedules ready inv live idemProj f small
    start regular positive word payload privateTapes scanSlots scan advance c push calls cursorTime
  have good : bad j = false := by
    by_cases active : live = true
    · exact regular active
    · dsimp only [bad]
      rw [fallbackBit_eq (by omega : 0 < w+1),show LabelStock.live m (w+1) 1 j = false from Bool.eq_false_iff.mpr active]
      rfl
  have skip : schedules (j::js) = schedules js := by simp [schedules,good]
  by_cases active : live = true
  case neg =>
    simp only [active]
    obtain ⟨z,user,run,next⟩ := DirectoryReady.advancePadding body u start skip
    let rest := js.flatMap (LabelDirectory.entry prefixes m (w+1)) ++ tail
    have keep (k : Fin 66) (off : k ≠ 46) := Function.update_of_ne (caller.injective.ne off) rest S.R
    refine ⟨z,_,_,word,user,le_rfl,run,next,?_,?_,rfl⟩
    · intro i
      change readAt blank _ (Function.update S.R (caller 46) rest (caller 24)) _ = _
      rw [keep 24 (by decide)]
      exact payload i
    · intro k hk
      exact keep k ((by decide : ∀ k ∈ ([40,56,57] : List (Fin 66)), k ≠ 46) k hk)
  simp only [active,ite_true]
  obtain ⟨_,idem,factors⟩ := physicalGood_inputs (by omega : 0 < w+1) proj idemProj f small proj.rank_le_height j active good
  rw [rank] at factors
  obtain ⟨L,R,factor⟩ := factors
  have generated := ordinaryGeneratedSetup_exec (common := common) (work := work) (H := H) (J := J) v proj weights prefixes tail schedules (Nat.size_le.mp le_rfl)
    pool unit (by omega : 58 ≤ K) body u S j js start active (regular active) word (by
      intro z
      change _ = readAt blank (S.L (caller 24)) (S.R (caller 24)) z
      simpa only [sub_zero,List.map_ofFn] using (payload z).symm)
  simp only [rank] at generated
  obtain ⟨minor,a,A,n,user,time,prepare,initial,empty,one,clock,scratch,_,extra,inverses,count,pivots,pair,publicFrame⟩ := generated
  have incoming := ordinaryDirectoryIncoming_exec (w := w) (r := r) (g := g) bank (ordinaryPackingWork room)
    (ordinaryPackingWork_apart room) body a A positive
  dsimp only at incoming
  rw [ordinaryPackingBank_entry] at incoming
  obtain ⟨y,D,t,before,hu,ht,run,read,_,headers,_,kept,outside,action⟩ := incoming G minor L R weights inv
    [] [] [] [] [] (fun _ => blank) 0 word idem factor (fun i => Ring.mul_inverse_cancel _ (unit i)) (fun _ _ _ => rfl)
    (by simpa only [List.append_nil] using initial) empty (by rw [List.append_nil]; exact inverses)
    (by rw [List.append_nil]; exact pair) count (by rw [List.append_nil]; exact pivots.trans (pivotWords_cast G hr minor rank H))
    one clock scratch (fun i => extra _ (by change 124 ≤ 124+_; omega))
  have publicKeep (k : Fin 64) (lo : 29 ≤ k.val) (hi : k.val < 58) (off : ∀ i, correctionCallerSlots i ≠ k) :=
    (ordinaryPacking_publicFrame room A D (fun i h off => (kept i h off).2)
      (fun i h off => (outside i h off).2) k lo hi off).trans (publicFrame _ hi)
  obtain ⟨z,F,l,hz,price,done,next,result,frame⟩ := ordinaryDirectoryAdvance_exec body prog u y S D (n+t) c
    (before ∘ ordinaryRecursivePosition r g w W) (hu.trans user) (Exec.seq prepare run) push calls start skip
    ⟨headers.modulus,headers.width,headers.one,headers.padded,headers.clock⟩ publicKeep read
  have bound : n+t ≤ cost := Nat.add_le_add time ht
  let packed := before ∘ ordinaryRecursivePosition r g w W
  let out := fun i => packed (Fin.cast (ordinaryChildVolume r g w W).symm i)
  refine ⟨z,F,l,out,hz,?_,done,next,?_,?_,minor,before,action,fun i => by simp [out,packed]⟩
  · exact price.trans (Nat.add_le_add_right (Nat.add_le_add bound (Nat.add_le_add_left
      (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left c bound))) _)) _)
  · intro k
    have words := List.ofFn_congr (ordinaryChildVolume r g w W) packed
    change _ = RadixToBinary.binaryEncoding.encode (putWord _ _ ((List.ofFn out).map _) k)
    rw [show List.ofFn out = List.ofFn packed from words.symm]
    exact result k
  · intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl
    · exact (frame _ (by decide) (by decide)).2.trans (publicKeep 40 (by decide) (by decide) (by decide))
    · exact (frame _ (by decide) (by decide)).2.trans (publicKeep 56 (by decide) (by decide) (by decide))
    · exact (frame _ (by decide) (by decide)).2.trans (publicKeep 57 (by decide) (by decide) (by decide))

end IntegerMultBounds.MathlibTM2.M6.BitNode
