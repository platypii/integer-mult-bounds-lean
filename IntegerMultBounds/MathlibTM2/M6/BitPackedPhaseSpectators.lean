module

public import IntegerMultBounds.MathlibTM2.M6.BitPackedPhaseCall
public import IntegerMultBounds.MathlibTM2.M6.BitScheduledSeededRows

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open M8.RevMachine RecursiveInterchangeLayout
open Shared50ModularControl (prime)

/-- Removing the two active fields from the sixteen phase coordinates gives
the spectator multiplicity seen by the packed MOVE. -/
theorem phaseSpectators (child : Descriptor) (w W rank : ℕ) (fits : rank ≤ 8)
    (width : child.width = (w+1)*rank) (size : volume prime child = (prime^(w+1))^16*W) :
    CopyChildLayout.spectators child = (prime^(w+1))^(16-2*rank)*W := by
  let M := prime^(w+1)
  have shape : volume prime child = M^(2*rank)*CopyChildLayout.spectators child := by
    simp only [volume,CopyChildLayout.spectators,width,pow_mul,M,two_mul,pow_add]
    ring
  apply Nat.eq_of_mul_eq_mul_left (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _ :
    0 < M^(2*rank))
  rw [← shape,← Nat.mul_assoc,← pow_add,show 2*rank+(16-2*rank) = 16 by omega]
  exact size

private def spectatorSources : Fin 9 ↪ Fin 35 := ⟨![2,27,3,4,5,6,7,8,9],by decide⟩

/-- Put the product on a fresh tape and borrow the multiplication scratch from
the open record. Both input dimensions retain their original binary words. -/
private def spectatorPorts {T : ℕ} (bank : Fin 35 ↪ Fin T) (dst : Fin T) (away : ∀ i, bank i ≠ dst) :
    Fin 10 ↪ Fin T :=
  ⟨Fin.insertNth (2 : Fin 10) dst (fun i => bank (spectatorSources i)),by
    intro i j eq
    induction i using Fin.succAboveCases 2 <;> induction j using Fin.succAboveCases 2 <;>
      simp_all [Function.Injective.eq_iff bank.injective,Function.Injective.eq_iff spectatorSources.injective]⟩

private theorem phaseProductTime (M W d : ℕ) (pos : 0 < M) (rows : 0 < W) (degree : d ≤ 16) :
    dimensionTime M.size W.size d + (4*(d*M.size+W.size)+6) + 2*(M^d*W).size ≤ 30000*(M^16*W) := by
  let V := M^16*W
  have power : M ≤ M^16 := Nat.le_self_pow (by decide) M
  have product : M*W ≤ V := Nat.mul_le_mul_right _ power
  have radix : M ≤ V := (Nat.le_mul_of_pos_right _ rows).trans product
  have tail : W ≤ V := (Nat.le_mul_of_pos_left _ pos).trans product
  have digits (x : ℕ) : x.size ≤ x := Nat.size_le.mpr Nat.lt_two_pow_self
  have square := size_square_le M pos
  have mixed := (Nat.mul_le_mul (digits M) (digits W)).trans product
  have result := (digits (M^d*W)).trans (Nat.mul_le_mul_right W (Nat.pow_le_pow_right pos degree))
  have time := dimensionTime_le M.size W.size d
  have upper : d*((12*M.size+18)*(d*M.size+W.size)+20*M.size+26) ≤
      16*((12*M.size+18)*(16*M.size+W.size)+20*M.size+26) := by gcongr
  have factor := Nat.mul_le_mul_right M.size degree
  change _ ≤ 30000*V
  change (M^d*W).size ≤ V at result
  have linear := time.trans (Nat.add_le_add_left upper _)
  nlinarith only [linear,factor,square,mixed,result,radix,tail,digits M,digits W,
    show 0 < V from Nat.mul_pos (pow_pos pos _) rows]

/-- Compute the packed spectator field from the two dimension words already on
the phase record. All other stacks, including the source payload, are restored. -/
theorem packedSpectatorWord {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (bank : Fin 35 ↪ Fin T) (dst : Fin T) (away : ∀ i, bank i ≠ dst) (rank : ℕ) (fits : rank ≤ 8) :
    ∃ code : Pr P T Q prime U, ∀ (child : Descriptor) (w W : ℕ), 0 < W →
      child.width = (w+1)*rank → volume prime child = (prime^(w+1))^16*W →
      let M := prime^(w+1)
      let n := CopyChildLayout.spectators child
      ∀ u (S : Stacks T prime) (x : Fin (M^16*W) → ZMod 2) record,
      RecordReady (b := prime) (w := w) (W := W) (d := 16) bank M.size W.size
        record SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0 x S →
      S.R dst = [] →
      let F := {S with R := Function.update S.R dst (binSyms n.size n)}
      ∃ z t, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F t (30000*(M^16*W)) := by
  let r := spectatorPorts bank dst away
  refine ⟨swapPrefix r (16-2*rank),?_⟩
  intro child w W rows width size M n u S x record ready empty F
  have spectators := phaseSpectators child w W rank fits width size
  have out : r 2 = dst := rfl
  have free (j : Fin 10) (lo : 2 ≤ j) (hi : j < 9) : S.R (r j) = [] := by
    fin_cases j <;> first | contradiction | exact empty | exact (ready.scratch _ (by decide)).2
  obtain ⟨z,t,user,time,run⟩ := scaledPrefix_exec body r (16-2*rank) M.size W.size M W
    (Nat.lt_size_self _) (Nat.lt_size_self _) u S ready.modulus ready.width free
  rw [canonicalBits_symbols,out,← spectators] at run
  refine ⟨z,t,run,user,?_⟩
  intro js nd
  have growth := prependedWordCharge S dst (binSyms n.size n) js nd
  simp only [empty,List.append_nil,length_binSyms] at growth
  change tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+2*n.size at growth
  have bound := phaseProductTime M W (16-2*rank) (pow_pos Shared50ModularControl.prime_prime.pos _) rows (Nat.sub_le ..)
  change n = M^(16-2*rank)*W at spectators
  rw [← spectators] at bound
  change t+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+_
  omega

/-- Open a packed phase record as a flat descriptor, call its payload worker,
and restore the record and scratch required by the scalar phase. -/
theorem packedPhaseRecordCall [M8.Machine.Net] {T Q : ℕ} {P U : Type}
    (body : P → Pr P T Q prime U) (worker : Pr P T Q prime U)
    (ports : Fin (rowSwapBlock.tapes+35) ↪ Fin T) (slot : Fin (rowSwapBlock.tapes+35))
    (high : 35 ≤ slot.val) (rank : ℕ) (fits : rank ≤ 8) :
    let bank := scheduledRecordPorts ports
    let dst := ports slot
    let fields : Fin 6 → Fin T := ![bank 28,bank 28,bank 28,bank 1,bank 28,dst]
    ∃ code, ∀ (node child : Descriptor) (w W L cutoff price : ℕ), 0 < W → child.width = (w+1)*rank →
      let V := (prime^(w+1))^16*W
      let lane := packedDescriptor child.width (CopyChildLayout.spectators child)
      ∀ position : Fin (volume prime child) ≃ Fin V,
      (∀ i, (position i).val = (CopyChildLayout.packActive child i).val) →
      (∀ (x : Fin (volume prime lane) → ZMod 2) u (D : Stacks T prime),
        (∀ i, D.R (fields i) = (Routines.hdr lane i).map bitSymbol) →
        D.R (bank 34) = binSyms L cutoff →
        (∀ j : Fin (rowSwapBlock.tapes+35), 35 ≤ j.val → j ≠ slot → D.L (ports j) = [] ∧ D.R (ports j) = []) →
        RecordPayload (bank 24) (fun _ => blank) 0 x D →
        ∃ z F t, Exec body worker (mk u D) t (mk z F) ∧ CleanupBound D F t price ∧ z.user = u.user ∧
          RecordPayload (bank 24) (fun _ => blank) 0 (Shared50RecursiveNodeRows.transpose (v := lane) (one_dvd _) x) F ∧
          ∀ j, j ≠ bank 24 → F.L j = D.L j ∧ F.R j = D.R j) →
      ∀ entry, body entry = code →
      ScheduledChildExec node child w W ports (binSyms L cutoff) position body entry
        (price+30400*V) true := by
  intro bank dst fields
  have off (j : Fin (rowSwapBlock.tapes+35)) (hj : 35 ≤ j.val) (i : Fin 35) : bank i ≠ ports j := by
    apply ports.injective.ne
    intro eq
    have e := congrArg Fin.val eq
    change i.val = j.val at e
    omega
  have apart := off slot high
  obtain ⟨setup,prepare⟩ := packedSpectatorWord body bank dst apart rank fits
  let move := openedPackedMoveProgram worker bank rank []
  refine ⟨(setup.seq move).seq (clearWorkTapes [dst]),?_⟩
  intro node child w W L cutoff price rows width V lane position packed work entry installed smaller u S x ready clean
  let M := prime^(w+1)
  have volumeEq : volume prime child = V := by simpa only [Fintype.card_fin] using Fintype.card_congr position
  let n := CopyChildLayout.spectators child
  let B := {S with R := Function.update S.R dst (binSyms n.size n)}
  obtain ⟨a,k,start,user,paid⟩ := prepare child w W rows width volumeEq u S x _ ready (clean slot high).2
  have atBank (i : Fin 35) : B.R (bank i) = S.R (bank i) := Function.update_of_ne (apart i) ..
  have stored := ready.returnPayload (F := B) (outBank := bank) (output := x)
    (fun i _ => ⟨rfl,atBank i⟩) (fun z => by simpa only [atBank] using (ready.src z).symm)
  have free (j : Fin (rowSwapBlock.tapes+35)) (hj : 35 ≤ j.val) (ne : j ≠ slot) :
      B.L (ports j) = [] ∧ B.R (ports j) = [] :=
    ⟨(clean j hj).1,(Function.update_of_ne (ports.injective.ne ne) ..).trans (clean j hj).2⟩
  obtain ⟨b,G,m,y,run,bill,same,out,frame,action⟩ := openedPackedMoveCallerAt body worker bank dst apart rank []
    (by simp) (by simp) child w W L cutoff price position width packed a B x stored
    (Function.update_self ..) (by simp) (by
      intro v D dimensions _ archive payload
      have size : volume prime lane = V := by
        rw [← volumeEq]
        simp only [lane,volume,packedDescriptor,CopyChildLayout.spectators]; ring
      let data := fun i : Fin (volume prime lane) => x (i.cast size)
      have castWord {a b : ℕ} (h : a = b) (f : Fin b → ZMod 2) :
          List.ofFn (fun i : Fin a => f (i.cast h)) = List.ofFn f := by subst b; rfl
      obtain ⟨z,F,t,exec,cost,zu,output,keep⟩ := work data v D dimensions archive (fun j hj ne =>
        ⟨(free j hj ne).1,(Function.update_of_ne (off j hj (moveWidthPorts 3)).symm ..).trans (free j hj ne).2⟩)
        (fun j => by simpa only [data,castWord] using payload j)
      refine ⟨z,F,t,exec,cost,zu,?_,fun j ne _ => keep j ne⟩
      intro j
      simpa only [data,castWord] using output j)
  obtain ⟨z,F,t,exec,zu,cost,payload,keep⟩ := restoreMoveHeaders body [dst] (by simp)
    (payload := bank 24) (by simpa using apart 24) (by simpa using clean slot high)
    start user paid (fun j hj => ⟨rfl,Function.update_of_ne (by simpa using hj) ..⟩) run same bill
    (y := y) (fun j => by simpa only [List.map_ofFn] using out.src j) frame
  rw [installed]
  refine ⟨z,F,t,y,exec,workerCost.weaken (charged := true) cost ?_,zu,?_,?_,?_,action⟩
  · have radix : M ≤ V := (Nat.le_self_pow (by decide : 16 ≠ 0) M).trans (Nat.le_mul_of_pos_right _ rows)
    have atom := (Nat.lt_pow_self (n := w+1) Shared50ModularControl.prime_prime.one_lt).le.trans radix
    have span : child.width ≤ (w+1)*8 := width ▸ Nat.mul_le_mul_left _ fits
    have bits : child.width.size ≤ child.width := Nat.size_le.mpr Nat.lt_two_pow_self
    change 30000*V+(price+4*0+4*w+23*child.width+16*child.width.size+37)+4*1+1 ≤ price+30400*V
    omega
  · exact ready.returnPayload (fun i ne => keep _ (bank.injective.ne ne))
      (fun j => by simpa only [List.map_ofFn] using (payload j).symm)
  · intro j hj
    have h := keep _ (off j hj 24).symm
    exact ⟨h.1.trans (clean j hj).1,h.2.trans (clean j hj).2⟩
  · intro j outside
    exact keep _ (fun eq => outside _ eq.symm)

end IntegerMultBounds.MathlibTM2.M6.BitNode
