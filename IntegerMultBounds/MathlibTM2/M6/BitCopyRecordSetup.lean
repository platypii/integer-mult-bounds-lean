module

public import IntegerMultBounds.MathlibTM2.Host.Embed
public import IntegerMultBounds.MathlibTM2.M6.BitCopyChildLayout
public import IntegerMultBounds.MathlibTM2.Cover.FallbackRecordVolumeHeaders
public import IntegerMultBounds.MathlibTM2.Cover.FallbackNegationDimensions

/-! Prepare the active-first packer's dimension registers from the rank-seven child headers. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode

open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open Shared50ModularControl (prime)

def copyRecordSources : Fin 3 ↪ Fin 6 := ⟨![4,5,0], by decide⟩
def copyRecordTargets : Fin 3 ↪ Fin 35 := ⟨![2,27,28], by decide⟩

def loadDimensions {P U : Type} {T Q A k : ℕ} (src dst : Fin k → Fin T) (tmp : Fin T) :
    List (Fin k) → Pr P T Q A U
  | [] => .act .done
  | i :: rest => .seq (copyDescriptor (src i) tmp (dst i)) (loadDimensions src dst tmp rest)

private theorem loadDimensions_exec {P U : Type} {T Q A k : ℕ} (body : P → Pr P T Q A U)
    (src : Fin k → Fin T) (dst : Fin k ↪ Fin T) (tmp : Fin T) (bits : Fin k → List Bool)
    (apart : ∀ i j, src i ≠ dst j) (ports : ∀ i, [src i,tmp,dst i].Nodup)
    (is : List (Fin k)) (unique : is.Nodup) (v : HS T Q A U) (S : Stacks T A)
    (words : ∀ i z, readAt blank (S.L (src i)) (S.R (src i)) (z-1) = RadixZeroFill.encodedBinary (bits i) z)
    (free : S.L tmp = [] ∧ S.R tmp = []) (empty : ∀ i ∈ is, S.R (dst i) = []) :
    ∃ u F, u.user = v.user ∧ Exec body (loadDimensions src dst tmp is) (mk v S)
      ((is.map (fun i => 8*(bits i).length+8)).sum+1) (mk u F) ∧ F.L = S.L ∧
      (∀ i ∈ is, F.R (dst i) = (bits i).map bitSymbol) ∧
      ∀ j, (∀ i ∈ is, dst i ≠ j) → F.R j = S.R j := by
  induction is generalizing v S with
  | nil => exact ⟨v,S,rfl,Exec.act _ _,rfl,by simp,fun _ _ => rfl⟩
  | cons i is ih =>
    obtain ⟨u,user,load⟩ := copyDescriptor_exec body (ports i) (bits i) v S (words i) free.1 free.2
    rw [empty i (by simp), List.append_nil] at load
    let D : Stacks T A := {S with R := Function.update S.R (dst i) ((bits i).map bitSymbol)}
    have tmpOff : tmp ≠ dst i := (List.nodup_cons.mp (List.nodup_cons.mp (ports i)).2).1 ∘ List.mem_singleton.mpr
    obtain ⟨z,F,hz,run,left,read,off⟩ := ih unique.of_cons u D
      (fun j => by simpa [D,Function.update_of_ne (apart j i)] using words j)
      ⟨free.1,by simpa [D,Function.update_of_ne tmpOff] using free.2⟩
      (fun j hj => by
        have ne : j ≠ i := fun e => unique.notMem (e ▸ hj)
        simpa [D,Function.update_of_ne (dst.injective.ne ne)] using empty j (by simp [hj]))
    refine ⟨z,F,hz.trans user,?_,left,?_,?_⟩
    · simpa only [loadDimensions,List.map_cons,List.sum_cons,Nat.add_assoc] using Exec.seq load run
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · rw [off (dst j) (fun l hl => dst.injective.ne (fun e : l = j => unique.notMem (e ▸ hl)))]
        simp [D]
      · exact read j hj
    · intro j hj
      rw [off j (fun l hl => hj l (List.mem_cons_of_mem _ hl))]
      exact Function.update_of_ne (hj i (by simp)).symm _ _

/-- The modulus, full record suffix and unit are already present in the
six child dimensions. Copy their binary words, preserving the caller's payload. -/
theorem copyRecordHeaders_exec {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (headers : Fin 6 ↪ Fin T) (bank : Fin 35 ↪ Fin T) (apart : ∀ i j, headers i ≠ bank j)
    (w W : ℕ) (u : HS T Q prime U) (S : Stacks T prime)
    (words : ∀ i z, readAt blank (S.L (headers i)) (S.R (headers i)) (z-1) =
      RadixZeroFill.encodedBinary (FlatCoordinateSchedule.bits (RecursiveDimensionBank.values (copyChild (w+1) W) i)) z)
    (empty : ∀ i : Fin 3, S.R (bank (copyRecordTargets i)) = [])
    (tmp : S.L (bank 0) = [] ∧ S.R (bank 0) = []) :
    let M := prime^(w+1)
    let src := copyRecordSources.trans headers
    let dst := copyRecordTargets.trans bank
    ∃ v F n, v.user = u.user ∧ n = 8*(M.size+(M*W).size)+33 ∧
      Exec body (loadDimensions src dst (bank 0) (List.finRange 3))
        (mk u S) n (mk v F) ∧ F.L = S.L ∧
      F.R (bank 2) = binSyms M.size M ∧ F.R (bank 27) = binSyms (M*W).size (M*W) ∧
      F.R (bank 28) = binSyms 1 1 ∧ ∀ j, (∀ i, dst i ≠ j) → F.R j = S.R j := by
  intro M src dst
  have ports (i : Fin 3) : [src i,bank 0,dst i].Nodup := by
    have nd := ((by decide : ∀ i, [0,copyRecordTargets i].Nodup) i).map bank.injective
    exact List.nodup_cons.mpr ⟨by simp [src,dst,apart],nd⟩
  let bits := fun i => FlatCoordinateSchedule.bits (RecursiveDimensionBank.values (copyChild (w+1) W) (copyRecordSources i))
  obtain ⟨v,F,user,run,left,loaded,off⟩ := loadDimensions_exec body src dst (bank 0) bits
    (fun i j => apart _ _) ports _ (List.nodup_finRange 3) u S (fun i => words _) tmp (fun i _ => empty i)
  have base : (bits 0).map (bitSymbol (a := prime)) = binSyms M.size M := canonicalBits_symbols _
  have suffix : (bits 1).map (bitSymbol (a := prime)) = binSyms (M*W).size (M*W) := canonicalBits_symbols _
  have unit : (bits 2).map (bitSymbol (a := prime)) = binSyms 1 1 := by
    change (FlatCoordinateSchedule.bits 1).map bitSymbol = _
    simpa using canonicalBits_symbols (A := prime) 1
  refine ⟨v,F,_,user,?_,run,left,(loaded 0 (List.mem_finRange _)).trans base,
    (loaded 1 (List.mem_finRange _)).trans suffix,(loaded 2 (List.mem_finRange _)).trans unit,
    fun j h => off j (fun i _ => h i)⟩
  have len (i : Fin 3) : ((bits i).map (bitSymbol (a := prime))).length = (bits i).length := by simp
  change (8*(bits 0).length+8)+((8*(bits 1).length+8)+((8*(bits 2).length+8)+0))+1 = _
  rw [←len 0,←len 1,←len 2,base,suffix,unit]
  simp only [length_binSyms]
  omega

/-- Prepare the padded unit and predecessor clock from the loaded modulus,
unit and the caller's binary atom width. Only the two destination stacks change. -/
theorem copyRecordControls_exec {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (bank : Fin 35 ↪ Fin T) (width : Fin T) (apart : ∀ i, width ≠ bank i)
    (w : ℕ) (v : HS T Q prime U) (S : Stacks T prime)
    (base : S.R (bank 2) = binSyms (prime^(w+1)).size (prime^(w+1)))
    (one : S.R (bank 28) = binSyms 1 1)
    (bits : S.R width = binSyms (w+1).size (w+1))
    (empty : ∀ i ∈ ([0,1,3,32,33] : List (Fin 35)), S.R (bank i) = []) :
    let M := prime^(w+1)
    let pad := toBinary (bank 28) (bank 2) (bank 32) (bank 0) (bank 1) (bank 3)
    let clock := toUnary width (bank 33) (bank 0) (bank 1) (bank 3)
    let drop : Act T Q prime U := .pop (.rt (bank 33)) (fun v _ => v) .done
    ∃ z n, z.user = v.user ∧ n ≤ 8*M.size + 6*(w+1) + 11*(w+1).size + 25 ∧
      Exec body (.seq pad (.seq clock (.act drop))) (mk v S) n
        (mk z {S with R := Function.update (Function.update S.R (bank 32) (binSyms M.size 1)) (bank 33) (List.replicate w Node.tick)}) := by
  intro M pad clock drop
  have distinct : [bank 28,bank 2,bank 32,bank 0,bank 1].Nodup :=
    (by decide : ([28,2,32,0,1] : List (Fin 35)).Nodup).map bank.injective
  obtain ⟨v₁,n₁,user₁,bound₁,first⟩ := toBinary_exec body distinct (bank 3) v S
    (empty 32 (by decide)) (empty 0 (by decide)) (empty 1 (by decide))
  simp only [base,one,length_binSyms] at first bound₁
  let D : Stacks T prime := {S with R := Function.update S.R (bank 32) (binSyms M.size 1)}
  have fresh (i : Fin 35) (hi : i ∈ ([0,1,3,33] : List (Fin 35))) : D.R (bank i) = [] := by
    have off : i ≠ 32 := by intro eq; subst i; contradiction
    simpa [D,Function.update_of_ne (bank.injective.ne off)] using empty i (by simp_all)
  have regs : [width,bank 33,bank 0,bank 1,bank 3].Nodup := List.nodup_cons.mpr
    ⟨by simp [apart],(by decide : ([33,0,1,3] : List (Fin 35)).Nodup).map bank.injective⟩
  obtain ⟨v₂,n₂,user₂,bound₂,second⟩ := toUnary_exec_linear (body := body) regs
    (Nat.lt_size_self (w+1)) v₁ D (by simpa [D,Function.update_of_ne (apart 32)] using bits)
    (fresh 0 (by decide)) (fresh 1 (by decide)) (fresh 3 (by decide))
  rw [fresh 33 (by decide),List.append_nil] at second
  let E : Stacks T prime := {D with R := Function.update D.R (bank 33) (List.replicate (w+1) Node.tick)}
  have pop : drop.run (mk v₂ E) = mk v₂ {D with R := Function.update D.R (bank 33) (List.replicate w Node.tick)} := by
    simp [drop,E,Action.run,update_rt,List.replicate_succ]
  refine ⟨v₂,_,user₂.trans user₁,?_,Exec.seq first (Exec.seq second (pop ▸ Exec.act (body := body) drop (mk v₂ E)))⟩
  dsimp only [M]
  omega

noncomputable def copyRecordSetup {P U : Type} {T Q : ℕ} (headers : Fin 6 ↪ Fin T) (bank : Fin 35 ↪ Fin T)
    (width : Fin T) : Pr P T Q prime U :=
  (.seq (loadDimensions (copyRecordSources.trans headers)
          (copyRecordTargets.trans bank) (bank 0) (List.finRange 3))
          (.seq (toBinary (bank 28) (bank 2) (bank 32) (bank 0) (bank 1) (bank 3))
            (.seq (toUnary width (bank 33) (bank 0) (bank 1) (bank 3))
              (.act (.pop (.rt (bank 33)) (fun v _ => v) .done)))))

/-- With the payload already on port 24, the child dimension words and atom-width
word suffice to start the record packer. The caller registers remain available. -/
theorem copyRecordSetup_exec {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (headers : Fin 6 ↪ Fin T) (bank : Fin 35 ↪ Fin T) (apart : ∀ i j, headers i ≠ bank j)
    (width : Fin T) (outside : ∀ i, width ≠ bank i)
    (w W : ℕ) (v : HS T Q prime U) (S : Stacks T prime)
    (words : ∀ i z, readAt blank (S.L (headers i)) (S.R (headers i)) (z-1) =
      RadixZeroFill.encodedBinary (FlatCoordinateSchedule.bits (RecursiveDimensionBank.values (copyChild (w+1) W) i)) z)
    (bits : S.R width = binSyms (w+1).size (w+1))
    (empty : ∀ i : Fin 35, i ≠ 24 → S.L (bank i) = [] ∧ S.R (bank i) = []) :
    let M := prime^(w+1)
    ∀ x : Fin (M^15*(M*W)) → ZMod 2,
      (∀ z, readAt blank (S.L (bank 24)) (S.R (bank 24)) z = RadixToBinary.binaryEncoding.encode
        (putWord (fun _ => blank) 0 (List.ofFn (SparseRoleCircuit.encode ∘ x)) z)) →
      ∃ u F n, u.user = v.user ∧ n ≤ 16*M.size + 8*(M*W).size + 6*(w+1) + 11*(w+1).size + 58 ∧
        Exec body (copyRecordSetup headers bank width) (mk v S) n (mk u F) ∧
        RecordReady (b := prime) (w := w) (d := 15) (W := M*W) bank M.size (M*W).size []
          SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0 x F ∧
        ∀ j, (∀ i, bank i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro M x payload
  obtain ⟨v₁,D,n₁,hv₁,cost₁,load,left,base,suffix,one,off⟩ := copyRecordHeaders_exec body headers bank apart w W v S words
    (fun i => (empty _ ((by decide : ∀ i, copyRecordTargets i ≠ 24) i)).2)
    (empty 0 (by decide))
  have keep (i : Fin 35) (h : i ∉ [2,27,28]) : D.R (bank i) = S.R (bank i) := by
    apply off
    intro k
    apply bank.injective.ne
    exact fun eq => h (eq ▸ (by decide : ∀ k, copyRecordTargets k ∈ ([2,27,28] : List (Fin 35))) k)
  have widthEq := off width (fun i => (outside _).symm)
  obtain ⟨u,n₂,hu,cost₂,controls⟩ := copyRecordControls_exec body bank width outside w v₁ D
    base one (widthEq.trans bits) (fun i hi => (keep i ((by decide : ∀ i ∈ ([0,1,3,32,33] : List (Fin 35)), i ∉ [2,27,28]) i hi)).trans
      (empty i ((by decide : ∀ i ∈ ([0,1,3,32,33] : List (Fin 35)), i ≠ 24) i hi)).2)
  refine ⟨u,_,_,hu.trans hv₁,by dsimp only [M] at *; omega,Exec.seq load controls,?_,?_⟩
  · have modulus : (1 : ZMod M).val = 1 := ZMod.val_one'' (Nat.ne_of_gt (Shared50ModularControl.prime_prime.one_lt.trans_le (Nat.le_self_pow (by omega : w+1 ≠ 0) prime)))
    constructor
    · simpa [Function.update,bank.injective.eq_iff] using base
    · simpa [Function.update,bank.injective.eq_iff] using suffix
    · simpa [Function.update,bank.injective.eq_iff] using one
    · simp [modulus,Function.update,bank.injective.eq_iff,M]
    · simp
    · simp [Function.update,bank.injective.eq_iff,keep 34 (by decide),(empty 34 (by decide)).2]
    · intro i hi
      have safe := (by decide : ∀ i ∈ shearWork, i ∉ ([2,27,28,32,33,24] : List (Fin 35))) i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at safe
      simp [Function.update_of_ne (bank.injective.ne safe.2.2.2.2.1),
        Function.update_of_ne (bank.injective.ne safe.2.2.2.1),keep i (by simp_all),left,empty i safe.2.2.2.2.2]
    · simpa [Function.update,bank.injective.eq_iff,keep 24 (by decide),left] using payload
    · intro z
      simp [Function.update,bank.injective.eq_iff,keep 25 (by decide),left,empty 25 (by decide),readAt]
      rfl
  · intro j hj
    exact ⟨congrFun left j,by
      simpa [Function.update_of_ne (hj 33).symm,Function.update_of_ne (hj 32).symm] using off j (fun i => hj _)⟩

/-- Locate the payload, dimension headers and atom width on the actual caller
bank after COPY header setup. The width survives on product-descriptor tape 3. -/
theorem copyCaller_reads {t T : ℕ} (w W : ℕ) (caller : Tapes t prime)
    (src : Fin t) (x : Fin (RecursiveInterchangeLayout.volume prime (copyChild (w+1) W)) → ZMod 2)
    (atOrigin : caller.head src = 0)
    (data : caller.tape src = M8.Machine.ArbitraryWidthHighExchangeShared.sourceWord x)
    (slots : Fin ((t+6)+15) ↪ Fin T) (S : Stacks T prime) :
    let hs := fun i => FlatCoordinateSchedule.bits (RecursiveDimensionBank.values (copyChild (w+1) W) i)
    let tapes := (caller.append (FixedHeaderBankCopy.headerBank hs)).append (copyHeaderOutput (w+1) W)
    let header := fun i : Fin 6 => slots (Fin.castAdd 15 (Fin.natAdd t i))
    let width := slots (Fin.natAdd (t+6) (Fin.natAdd 9 (3 : Fin 6)))
    let payload := slots (Fin.castAdd 15 (Fin.castAdd 6 src))
    RepT tapes (S.L ∘ slots) (S.R ∘ slots) →
      (∀ i z, readAt blank (S.L (header i)) (S.R (header i)) (z-1) = RadixZeroFill.encodedBinary (hs i) z) ∧
      (∀ z, readAt blank (S.L width) (S.R width) (z-1) =
        RadixZeroFill.encodedBinary (FlatCoordinateSchedule.bits (w+1)) z) ∧
      ∀ z, readAt blank (S.L payload) (S.R payload) z = RadixToBinary.binaryEncoding.encode
        (putWord (fun _ => blank) 0 (List.ofFn (SparseRoleCircuit.encode ∘ x)) z) := by
  intro hs tapes header width payload rep
  refine ⟨fun i z => ?_,fun z => ?_,fun z => ?_⟩
  · have h := (rep (Fin.castAdd 15 (Fin.natAdd t i)) z).symm
    simpa [tapes,header,Tapes.append,FixedHeaderBankCopy.headerBank,FixedHeaderBankCopy.bank,RecursiveDimensionBank.head,RecursiveDimensionBank.tape] using h
  · have h := (rep (Fin.natAdd (t+6) (Fin.natAdd 9 (3 : Fin 6))) z).symm
    simp only [tapes,Function.comp_apply,Tapes.append,copyHeaderOutput,Fin.addCases_right,DimensionProductDescriptor.output] at h
    simpa [width] using h
  · have h := (rep (Fin.castAdd 15 (Fin.castAdd 6 src)) z).symm
    simpa [tapes,payload,Tapes.append,atOrigin,data,swap_source_word] using h

/-- Stage the arithmetic width word, then prepare the record directly on the
represented payload port. Descriptor sources can have trailing stack blanks. -/
theorem copyCallerSetup_exec {P U : Type} {t T Q : ℕ} (body : P → Pr P T Q prime U)
    (w W : ℕ) (caller : Tapes t prime) (src : Fin t)
    (slots : Fin ((t+6)+15) ↪ Fin T) (bank : Fin 35 ↪ Fin T) (staged : Fin T)
    (apart : ∀ i j, slots i = bank j → j = 24)
    (outside : ∀ i, staged ≠ bank i) (privateSlot : ∀ i, staged ≠ slots i)
    (shared : slots (Fin.castAdd 15 (Fin.castAdd 6 src)) = bank 24)
    (v : HS T Q prime U) (S : Stacks T prime) (fresh : S.R staged = [])
    (empty : ∀ i : Fin 35, i ≠ 24 → S.L (bank i) = [] ∧ S.R (bank i) = [])
    (x : Fin (RecursiveInterchangeLayout.volume prime (copyChild (w+1) W)) → ZMod 2)
    (head : caller.head src = 0) (data : caller.tape src = M8.Machine.ArbitraryWidthHighExchangeShared.sourceWord x) :
    let hs := fun i => FlatCoordinateSchedule.bits (RecursiveDimensionBank.values (copyChild (w+1) W) i)
    let tapes := (caller.append (FixedHeaderBankCopy.headerBank hs)).append (copyHeaderOutput (w+1) W)
    let headers := (Fin.natAddEmb t (m := 6)).trans ((Fin.castAddEmb 15).trans slots)
    let width := slots (Fin.natAdd (t+6) (Fin.natAdd 9 (3 : Fin 6)))
    let M := prime^(w+1)
    let size : M^15*(M*W) = RecursiveInterchangeLayout.volume prime (copyChild (w+1) W) := by
      rw [copyChild_volume]; change M^15*(M*W) = M^16*W; ring
    RepT tapes (S.L ∘ slots) (S.R ∘ slots) →
    ∃ u F n, u.user = v.user ∧ n ≤ 16*M.size+8*(M*W).size+6*(w+1)+21*(w+1).size+68 ∧
      Exec body (.seq (.seq (copyDescriptor width (bank 0) staged) (copyRecordSetup headers bank staged))
        (WordCmd.dropR staged))
        (mk v S) n (mk u F) ∧
      RecordReady (b := prime) (w := w) (d := 15) (W := M*W) bank M.size (M*W).size []
        SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0 (fun i => x (i.cast size)) F ∧
      ∀ j, (∀ i, bank i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro hs tapes headers width M size rep
  obtain ⟨words,bits,payload⟩ := copyCaller_reads w W caller src x head data slots S rep
  have ports : [width,bank 0,staged].Nodup := by
    have ne : width ≠ bank 0 := fun e => (by decide : (0 : Fin 35) ≠ 24) (apart _ _ e)
    have ws : width ≠ staged := (privateSlot _).symm
    simp [ne,ws,(outside 0).symm]
  obtain ⟨v₁,hv,load⟩ := copyDescriptor_exec body ports _ v S bits (empty 0 (by decide)).1 (empty 0 (by decide)).2
  rw [fresh,List.append_nil,canonicalBits_symbols] at load
  let D : Stacks T prime := {S with R := Function.update S.R staged (binSyms (w+1).size (w+1))}
  have separate (i j) : headers i ≠ bank j := by
    intro eq
    obtain rfl := apart _ j eq
    have clash := congrArg Fin.val (slots.injective (eq.trans shared.symm))
    simp at clash
    omega
  obtain ⟨u,F,n,hu,bound,run,ready,off⟩ := copyRecordSetup_exec body headers bank separate staged outside w W v₁ D
    (fun i => by simpa [D,headers,Function.update_of_ne (privateSlot _).symm] using words i)
    (by simp [D]) (fun i hi => by simpa [D,Function.update_of_ne (outside i).symm] using empty i hi)
    (fun i => x (i.cast size)) (by
      intro z
      have h := payload z
      rw [shared] at h
      simpa [D,Function.update_of_ne (outside 24).symm,Function.comp_def,
        List.ofFn_congr size] using h)
  have digits : (FlatCoordinateSchedule.bits (w+1)).length = (w+1).size := by
    have h := congrArg List.length (canonicalBits_symbols (A := prime) (w+1))
    simpa using h
  obtain ⟨z,hz,erase⟩ := WordCmd.dropR_exec body staged u F
  have widthWord : F.R staged = binSyms (w+1).size (w+1) := by
    simpa [D] using (off staged (fun i => (outside i).symm)).2
  rw [widthWord,length_binSyms] at erase
  refine ⟨z,_,_,hz.trans (hu.trans hv),?_,Exec.seq (Exec.seq load run) erase,?_,?_⟩
  · rw [digits]; dsimp only [M] at *; omega
  · apply ready.returnPayload
    · intro i _
      exact ⟨rfl,Function.update_of_ne (outside i).symm _ _⟩
    · intro k
      simpa [Function.update_of_ne (outside 24).symm] using (ready.src k).symm
  · intro j free
    obtain ⟨l,r⟩ := off j free
    refine ⟨l,?_⟩
    by_cases eq : j = staged
    · subst j; simpa using fresh.symm
    · simpa [D, Function.update_of_ne eq] using r

/-- Retire a list of distinct right stacks, paying for each stored symbol once. -/
private theorem retire_exec {P U : Type} {T Q A : ℕ} (body : P → Pr P T Q A U)
    (ports : List (Fin T)) (unique : ports.Nodup) (v : HS T Q A U) (S : Stacks T A) :
    ∃ u F, u.user = v.user ∧ Exec body (Prog.seqList (ports.map WordCmd.dropR)) (mk v S)
      ((ports.map (fun j => 2*(S.R j).length+2)).sum+1) (mk u F) ∧ F.L = S.L ∧
      ∀ j, F.R j = if j ∈ ports then [] else S.R j := by
  induction ports generalizing v S with
  | nil => exact ⟨v,S,rfl,Exec.act _ _,rfl,by simp⟩
  | cons i ports ih =>
    obtain ⟨u,hu,erase⟩ := WordCmd.dropR_exec body i v S
    let D : Stacks T A := {S with R := Function.update S.R i []}
    obtain ⟨z,F,hz,rest,left,right⟩ := ih unique.of_cons u D
    have time : ports.map (fun j => 2*(D.R j).length+2) = ports.map (fun j => 2*(S.R j).length+2) := by
      apply List.map_congr_left
      intro j hj
      have ne : j ≠ i := fun eq => unique.notMem (eq ▸ hj)
      simp [D, Function.update_of_ne ne]
    rw [time] at rest
    refine ⟨z,F,hz.trans hu,?_,left,?_⟩
    · simpa only [List.map_cons,List.sum_cons,Nat.add_assoc,Prog.seqList] using Exec.seq erase rest
    · intro j
      by_cases eq : j = i
      · subst j; simp [right,D,unique.notMem]
      · simp [right,D,eq]

/-- After unpacking the changed payload, clear the five control registers that
setup filled. Every left stack and every other right stack are preserved. -/
theorem copyRecordRetire_exec {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (bank : Fin 35 ↪ Fin T) (w W : ℕ) (v : HS T Q prime U) (S : Stacks T prime) :
    let M := prime^(w+1)
    ∀ x : Fin (M^15*(M*W)) → ZMod 2,
      RecordReady (b := prime) (w := w) (d := 15) (W := M*W) bank M.size (M*W).size []
        SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0 x S →
      let ports := ([2,27,28,32,33] : List (Fin 35)).map bank
      ∃ u F, u.user = v.user ∧ Exec body (Prog.seqList (ports.map WordCmd.dropR))
        (mk v S) (4*M.size+2*(M*W).size+2*w+13) (mk u F) ∧ F.L = S.L ∧
        (∀ j, F.R j = if j ∈ ports then [] else S.R j) ∧
        ∀ z, readAt blank (F.L (bank 24)) (F.R (bank 24)) z =
          RadixToBinary.binaryEncoding.encode (putWord (fun _ => blank) 0
            (List.ofFn (SparseRoleCircuit.encode ∘ x)) z) := by
  intro M x ready ports
  obtain ⟨u,F,user,run,left,right⟩ := retire_exec body ports
    ((by decide : ([2,27,28,32,33] : List (Fin 35)).Nodup).map bank.injective) v S
  have payload : bank 24 ∉ ports := by
    intro h
    obtain ⟨i,hi,eq⟩ := List.mem_map.mp h
    exact (by decide : (24 : Fin 35) ∉ [2,27,28,32,33]) (bank.injective eq ▸ hi)
  refine ⟨u,F,user,?_,left,right,?_⟩
  · convert run using 1
    simp only [ports,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,ready.modulus,ready.width,
    ready.one,ready.padded,ready.clock,length_binSyms]
    omega
  · intro z
    rw [left,right]; simp only [payload, ↓reduceIte]
    simpa using ready.src z

open RecursiveInterchangeLayout (volume)
local notation "N" => rowSwapBlock.tapes
local notation "Q" => rowSwapBlock.states
local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩
open FlatCoordinateLayout (index) in
/-- Execute the packed child and return its transpose with the setup registers cleared. -/
theorem copyTransposeReturn_exec [M8.Machine.Net] {P P' U : Type} {T : ℕ} [Fintype P]
    (body : P → Pr P (N+35) Q prime U) (host : P' → Pr P' T Q prime U)
    (placement : Fin (N+35) ↪ Fin T) (ι : P → P')
    (calls : ∀ f, host (ι f) = embProg placement ι (body f)) :
    ∃ setup swaps : ℕ, ∀ (parent : RecursiveInterchangeLayout.Descriptor) w rows
      (splitRows : parent.rows = 142080*rows),
      let M := prime^(w+1)
      let W := M^112 * (parent.beforeRows*rows*parent.beforeH*parent.between*parent.afterD)
      let position := copyRecursivePosition parent w rows splitRows
      0 < W →
      let suffix := M*W
      let size : M^15*suffix = volume prime (copyChild (w+1) W) := by
        rw [copyChild_volume]; change M^15*(M*W) = M^16*W; ring
      let bank : Fin 35 ↪ Fin (N+35) := (Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)
      let clean := fun (D : Stacks (N+35) prime) => ∀ k : Fin (N+35), 35 ≤ k.val → D.L k = [] ∧ D.R k = []
      ∀ {t} (caller : Tapes t prime) (src : Fin t) (slots : Fin ((t+6)+15) ↪ Fin T) (staged : Fin T)
        (v : HS T Q prime U) (S : Stacks T prime)
        (x : Fin (volume prime (copyChild (w+1) W)) → ZMod 2) (child : Pr P (N+35) Q prime U) (budget : ℕ),
      let physical := bank.trans placement
      let headers := (Fin.natAddEmb t (m := 6)).trans ((Fin.castAddEmb 15).trans slots)
      let width := slots (Fin.natAdd (t+6) (Fin.natAdd 9 (3 : Fin 6)))
      let hs := fun i => FlatCoordinateSchedule.bits (RecursiveDimensionBank.values (copyChild (w+1) W) i)
      let output := fun i => Shared50RecursiveNodeRows.transpose (one_dvd _) x (Fin.cast size i)
      let stored := RecordReady (b := prime) (w := w) (d := 15) (W := suffix)
        bank (Nat.size M) (Nat.size suffix) [] SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0
      (∀ v D word, stored word D → clean D → ∃ z F n changed, z.user = v.user ∧ n ≤ budget ∧
        Exec body child (mk v D) n (mk z F) ∧ stored changed F ∧ clean F ∧
        ∀ i, changed (position i) = Shared50RecursiveNodeRows.transpose (one_dvd _) (word ∘ position) i) →
      (∀ i j, slots i = physical j → j = 24) → (∀ i, staged ≠ physical i) →
      (∀ i, staged ≠ slots i) → slots (Fin.castAdd 15 (Fin.castAdd 6 src)) = physical 24 →
      S.R staged = [] → (∀ i : Fin 35, i ≠ 24 → S.L (physical i) = [] ∧ S.R (physical i) = []) →
      caller.head src = 0 → caller.tape src = M8.Machine.ArbitraryWidthHighExchangeShared.sourceWord x →
      RepT ((caller.append (FixedHeaderBankCopy.headerBank hs)).append (copyHeaderOutput (w+1) W))
        (S.L ∘ slots) (S.R ∘ slots) → clean (embStk placement S) →
      let ports := ([2,27,28,32,33] : List (Fin 35)).map bank
      ∃ z F n, z.user = v.user ∧
        n ≤ budget + 2*((setup+swaps*swapVolumeRate w)*(M^15*suffix)) ∧
        Exec host (.seq (.seq (.seq (copyDescriptor width (physical 0) staged) (copyRecordSetup headers physical staged))
          (WordCmd.dropR staged)) (embProg placement ι (.seq (.seq (packSchedule 15 copyPackSchedule)
          (.seq child (packSchedule 15 copyPackSchedule.reverse))) (Prog.seqList (ports.map WordCmd.dropR)))))
          (mk v S) n (mk z F) ∧ clean (embStk placement F) ∧ (∀ j ∈ ports, F.R (placement j) = []) ∧
        (∀ j, (∀ i, placement i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j) ∧
        ∀ k, readAt blank (F.L (placement (bank 24))) (F.R (placement (bank 24))) k =
          RadixToBinary.binaryEncoding.encode (putWord (fun _ => blank) 0
            (List.ofFn (SparseRoleCircuit.encode ∘ output)) k) := by
  obtain ⟨setup,swaps,transpose⟩ := withCopyTranspose_exec body
  refine ⟨setup+70,swaps,?_⟩
  intro parent w rows splitRows M W position hW suffix size bank clean t caller src slots staged v S x child budget physical headers width hs output stored call
    apart outside privateSlot shared fresh empty head data rep free ports
  obtain ⟨a,B,m,ha,hm,prepare,ready,off⟩ := copyCallerSetup_exec host w W caller src slots physical staged
    apart outside privateSlot shared v S fresh empty x head data rep
  have start : stored (fun i => x (Fin.cast size i)) (embStk placement B) :=
    ⟨ready.modulus,ready.width,ready.one,ready.padded,ready.clock,ready.archive,ready.scratch,ready.src,ready.dst⟩
  have available : clean (embStk placement B) := by
    intro k hk
    have kept := off (placement k) (by
      intro i eq
      have eq' : bank i = k := placement.injective eq
      rw [← eq'] at hk
      exact (Nat.not_le_of_lt i.isLt) hk)
    exact ⟨kept.1.trans (free k hk).1,kept.2.trans (free k hk).2⟩
  obtain ⟨u,D,n,hu,time,run,placed,clear⟩ :=
    transpose w W hW (embDn placement a) (embStk placement B) [] (fun _ => blank) 0 x child budget (by
      intro z F word storedWord cleanWord
      obtain ⟨y,G,n,changed,user,time,run,placed,clear,transposed⟩ := call z F word storedWord cleanWord
      exact ⟨y,G,n,changed,user,time,run,placed,clear,
        copyRecursivePacked_swap parent w rows splitRows word changed transposed⟩) start available
  obtain ⟨z,F,hz,erase,left,right,read⟩ := copyRecordRetire_exec body bank w W u D output placed
  obtain ⟨y,G,execute,_,user,project,frame⟩ :=
    exec_emb placement.injective calls (Exec.seq run erase) a rfl B rfl
  refine ⟨y,G,_,(user.trans (hz.trans hu)).trans ha,?_,Exec.seq prepare execute,?_,?_,?_,?_⟩
  · let V := M^15*suffix
    have pos : 0 < M := pow_pos Shared50ModularControl.prime_prime.pos _
    have hsuf : 0 < suffix := Nat.mul_pos pos hW
    have hv : 1 ≤ V := Nat.mul_pos (pow_pos pos _) hsuf
    have bits (k : ℕ) : k.size ≤ k := Nat.size_le.mpr Nat.lt_two_pow_self
    have mV : M ≤ V := (Nat.le_self_pow (by decide : 15 ≠ 0) M).trans (Nat.le_mul_of_pos_right _ hsuf)
    have sV : suffix ≤ V := Nat.le_mul_of_pos_left _ (pow_pos pos _)
    have wV : w+1 ≤ V := (Nat.le_of_lt (Nat.lt_two_pow_self (n := w+1))).trans
      ((Nat.pow_le_pow_left Shared50ModularControl.prime_prime.two_le _).trans mV)
    change n ≤ budget + 2*((setup+swaps*swapVolumeRate w)*V) at time
    change m ≤ 16*M.size+8*suffix.size+6*(w+1)+21*(w+1).size+68 at hm
    change m+(n+(4*M.size+2*suffix.size+2*w+13)) ≤ budget+2*((setup+70+swaps*swapVolumeRate w)*V)
    have room : 2*((setup+70+swaps*swapVolumeRate w)*V) =
        2*((setup+swaps*swapVolumeRate w)*V)+140*V := by ring
    rw [room]
    have := bits M
    have := bits suffix
    have := bits (w+1)
    omega
  · rw [project]
    intro k hk
    have outside : k ∉ ports := by
      intro mem
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp mem
      exact (Nat.not_le_of_lt i.isLt) hk
    exact ⟨(congrFun left k).trans (clear k hk).1, (right k).trans (by change (if k ∈ ports then [] else D.R k) = []; simp [outside,(clear k hk).2])⟩
  · intro j hj
    change (embStk placement G).R j = []
    rw [project]
    rw [right]; change (if j ∈ ports then [] else D.R j) = []; simp [hj]

  · intro j hj
    have kept := off j (fun i => hj (bank i))
    exact ⟨(frame j hj).1.trans kept.1,(frame j hj).2.trans kept.2⟩
  · change ∀ k, readAt blank ((embStk placement G).L (bank 24)) ((embStk placement G).R (bank 24)) k = _
    rwa [project]

/-- At a recursive call the wrapper contributes a single volume-width term.
The coefficient is independent of the child dimensions and its running time. -/
theorem copyReturn_parentCost [M8.Machine.Net] (setup swaps : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ w V budget n : ℕ,
      n ≤ budget + 2*((setup+swaps*swapVolumeRate w)*V) →
      (n : ℝ) ≤ budget + C*V*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau := by
  let K := (3808275 : ℝ) + M8.RevMachine.LeafCore.C
  have pos : 0 < M8.RevMachine.LeafCore.C := (Classical.choose_spec M8.Machine.ArbitraryWidthOriginalTotalRun.uniform_bound).1
  refine ⟨2*(setup+swaps*K)+1,by dsimp [K]; positivity,?_⟩
  intro w V budget n bound
  let power := ((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau
  have one : 1 ≤ power := Real.one_le_rpow (by exact_mod_cast Nat.le_add_left 1 w)
    M8.Machine.BudgetBound.exponent_range.1.le
  have rate : (swapVolumeRate w : ℝ) ≤ K*power := swapVolumeRate_le w
  have fixed : (setup : ℝ) ≤ setup*power := le_mul_of_one_le_right (by positivity) one
  calc
    (n : ℝ) ≤ budget + 2*((setup+swaps*(swapVolumeRate w : ℝ))*V) := by exact_mod_cast bound
    _ ≤ budget + 2*((setup*power+swaps*(K*power))*V) := by gcongr
    _ ≤ _ := by change _ ≤ budget+(2*(setup+swaps*K)+1)*V*power; nlinarith [mul_nonneg (Nat.cast_nonneg V) (zero_le_one.trans one)]

/-- At bounded widths the represented caller executes the direct packed child in linear volume cost. -/
theorem copyStoppedReturn_exec [M8.Machine.Net] {P P' U : Type} {T : ℕ} [Fintype P]
    (body : P → Pr P (N+35) Q prime U) (host : P' → Pr P' T Q prime U)
    (placement : Fin (N+35) ↪ Fin T) (ι : P → P')
    (calls : ∀ f, host (ι f) = embProg placement ι (body f)) :
    ∀ cutoff : ℕ, ∃ rate : ℕ, ∀ (parent : RecursiveInterchangeLayout.Descriptor) w rows
      (splitRows : parent.rows = 142080*rows),
      let M := prime^(w+1)
      let W := M^112 * (parent.beforeRows*rows*parent.beforeH*parent.between*parent.afterD)
      w ≤ cutoff →
      0 < W →
      let suffix := M*W
      let size : M^15*suffix = volume prime (copyChild (w+1) W) := by
        rw [copyChild_volume]; change M^15*(M*W) = M^16*W; ring
      let bank : Fin 35 ↪ Fin (N+35) := (Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)
      let clean := fun (D : Stacks (N+35) prime) => ∀ k : Fin (N+35), 35 ≤ k.val → D.L k = [] ∧ D.R k = []
      ∀ {t} (caller : Tapes t prime) (src : Fin t) (slots : Fin ((t+6)+15) ↪ Fin T) (staged : Fin T)
        (v : HS T Q prime U) (S : Stacks T prime)
        (x : Fin (volume prime (copyChild (w+1) W)) → ZMod 2) ,
      let physical := bank.trans placement
      let headers := (Fin.natAddEmb t (m := 6)).trans ((Fin.castAddEmb 15).trans slots)
      let width := slots (Fin.natAdd (t+6) (Fin.natAdd 9 (3 : Fin 6)))
      let hs := fun i => FlatCoordinateSchedule.bits (RecursiveDimensionBank.values (copyChild (w+1) W) i)
      let output := fun i => Shared50RecursiveNodeRows.transpose (one_dvd _) x (Fin.cast size i)
      (∀ i j, slots i = physical j → j = 24) → (∀ i, staged ≠ physical i) →
      (∀ i, staged ≠ slots i) → slots (Fin.castAdd 15 (Fin.castAdd 6 src)) = physical 24 →
      S.R staged = [] → (∀ i : Fin 35, i ≠ 24 → S.L (physical i) = [] ∧ S.R (physical i) = []) →
      caller.head src = 0 → caller.tape src = M8.Machine.ArbitraryWidthHighExchangeShared.sourceWord x →
      RepT ((caller.append (FixedHeaderBankCopy.headerBank hs)).append (copyHeaderOutput (w+1) W))
        (S.L ∘ slots) (S.R ∘ slots) → clean (embStk placement S) →
      let ports := ([2,27,28,32,33] : List (Fin 35)).map bank
      ∃ z F n, z.user = v.user ∧
        n ≤ rate*(M^15*suffix) ∧
        Exec host (.seq (.seq (.seq (copyDescriptor width (physical 0) staged) (copyRecordSetup headers physical staged))
          (WordCmd.dropR staged)) (embProg placement ι (.seq (.seq (packSchedule 15 copyPackSchedule)
          (.seq (packSchedule 15 (middleTailSchedule 7 7)) (packSchedule 15 copyPackSchedule.reverse))) (Prog.seqList (ports.map WordCmd.dropR)))))
          (mk v S) n (mk z F) ∧ clean (embStk placement F) ∧ (∀ j ∈ ports, F.R (placement j) = []) ∧
        (∀ j, (∀ i, placement i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j) ∧
        ∀ k, readAt blank (F.L (placement (bank 24))) (F.R (placement (bank 24))) k =
          RadixToBinary.binaryEncoding.encode (putWord (fun _ => blank) 0
            (List.ofFn (SparseRoleCircuit.encode ∘ output)) k) := by
  intro cutoff
  obtain ⟨setup,swaps,wrapper⟩ := copyTransposeReturn_exec body host placement ι calls
  obtain ⟨base,passes,leaf⟩ := copyPackedBase_exec body
  let rates := ((List.range (cutoff+1)).map swapVolumeRate).sum
  refine ⟨base+passes*rates+2*(setup+swaps*rates),?_⟩
  intro parent w rows splitRows M W small positive suffix size bank clean t caller src slots staged v S x
    physical headers width hs output apart outside privateSlot shared fresh empty head data rep free ports
  have hm : 0 < M := pow_pos Shared50ModularControl.prime_prime.pos _
  have hsuf : 0 < suffix := Nat.mul_pos hm positive
  have run := wrapper parent w rows splitRows positive caller src slots staged v S x
    (packSchedule 15 (middleTailSchedule 7 7)) ((base+passes*swapVolumeRate w)*(M^15*suffix)) (by
      intro u D word ready clear
      obtain ⟨z,F,n,changed,user,time,exec,placed,blank,swap⟩ := leaf w suffix hsuf u D word ready clear
      exact ⟨z,F,n,changed,user,time,exec,placed,blank,copyPacked_recursiveTranspose parent w rows splitRows word changed swap⟩)
    apart outside privateSlot shared fresh empty head data rep free
  obtain ⟨z,F,n,user,time,result⟩ := run
  refine ⟨z,F,n,user,time.trans ?_,result⟩
  let V := M^15*suffix
  have rate : swapVolumeRate w ≤ rates := List.single_le_sum (fun _ _ => Nat.zero_le _) (swapVolumeRate w)
    (List.mem_map.mpr ⟨w,List.mem_range.mpr (by omega),rfl⟩)
  change (base+passes*swapVolumeRate w)*V + 2*((setup+swaps*swapVolumeRate w)*V) ≤ _
  calc
    _ ≤ (base+passes*rates)*V + 2*((setup+swaps*rates)*V) := by gcongr
    _ = _ := by ring


end IntegerMultBounds.MathlibTM2.M6.BitNode
