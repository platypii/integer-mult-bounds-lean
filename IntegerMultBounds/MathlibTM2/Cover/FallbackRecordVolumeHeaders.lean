module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackRecordWordWidth
public import IntegerMultBounds.MathlibTM2.Cover.FallbackSwapDimensions
public import IntegerMultBounds.MathlibTM2.Cover.FallbackLeafReturnHeaders

/-! Generate the two equal field-volume factors and trailing width of the record payload. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host

def recordInputSources : Fin 4 ↪ Fin 58 := ⟨![2,44,45,55],by decide⟩

def recordInputTargets : Fin 4 ↪ Fin 24 := ⟨![2,20,22,23],by decide⟩

/-- Load the modulus, unit, clock, and parent weight archive from the caller.
Only those four right stacks change, so a prepared matrix survives the copy. -/
theorem loadRecordInputs_exec {T Q A : ℕ} {F U : Type} (body : F → Pr F T Q A U)
    (caller : Fin 58 ↪ Fin T) (record : Fin 24 ↪ Fin T) (apart : ∀ i j, caller i ≠ record j)
    (u : HS T Q A U) (S : Stacks T A)
    (empty : ∀ i : Fin 4, S.R (record (recordInputTargets i)) = [])
    (tmp : S.R (record 0) = []) (aux : S.R (record 1) = []) :
    let src := recordInputSources.trans caller
    let dst := recordInputTargets.trans record
    ∃ z D, z.user = u.user ∧ Exec body (Record.copyLeafHeaders src dst (record 0) (record 1) (List.finRange 4))
      (mk u S) (((List.finRange 4).map (fun i => 6*(S.R (src i)).length+6)).sum+1) (mk z D) ∧
      D.L = S.L ∧ D.R (record 2) = S.R (caller 2) ∧ D.R (record 20) = S.R (caller 44) ∧
      D.R (record 22) = S.R (caller 45) ∧ D.R (record 23) = S.R (caller 55) ∧
      ∀ j, (∀ i, dst i ≠ j) → D.R j = S.R j := by
  intro src dst
  have ports (i : Fin 4) : [src i,dst i,record 0,record 1].Nodup := by
    have nd := ((by decide : ∀ i, [recordInputTargets i,0,1].Nodup) i).map record.injective
    apply List.nodup_cons.mpr
    exact ⟨by simp [src,dst,apart],nd⟩
  obtain ⟨z,D,user,run,left,loaded,off⟩ := Record.copyLeafHeaders_exec body src dst (record 0) (record 1)
    (fun i j => apart _ _) ports _ (List.nodup_finRange 4) u S tmp aux (fun i _ => empty i)
  exact ⟨z,D,user,run,left,loaded 0 (List.mem_finRange _),loaded 1 (List.mem_finRange _),
    loaded 2 (List.mem_finRange _),loaded 3 (List.mem_finRange _),fun j h => off j (fun i _ => h i)⟩

theorem canonicalBits_symbols {A : ℕ} (a : ℕ) : (FlatCoordinateSchedule.bits a).map (bitSymbol (a := A)) = binSyms a.size a := by
  rw [binSyms_eq]
  congr 1
  exact BinaryCanonicalData.value_injective _ _ (FlatCoordinateSchedule.bits_canonical _)
    (Mult.PhaseCellToeplitz.binBits_size_canonical _) ((FlatCoordinateSchedule.bits_value _).trans
      (Routing.binaryCanonical_value_binBits _ _ (Nat.lt_size_self _)).symm)

/-- Use the stored modulus twice: its padded copy counts the input field,
and its canonical copy counts the bits kept for each coefficient. -/
theorem canonicalRecordArchive_exec {T Q A : ℕ} {F U : Type} (body : F → Pr F T Q A U)
    (r : Fin 7 ↪ Fin T) (dst : Fin T) (outside : ∀ i, dst ≠ r i)
    (M H : ℕ) (hm : M < 2^H) (xs : List ℕ) (below : ∀ x ∈ xs, x < M)
    (tail : List (Fin (A+4))) (u : HS T Q A U) (S : Stacks T A)
    (modulus : S.R (r 0) = binSyms H M) (input : S.R (r 1) = (xs.map (binSyms H)).flatten ++ tail)
    (empty : ∀ i ∈ ([2,3,4,5,6] : List (Fin 7)), S.R (r i) = []) :
    let words := (xs.map (binSyms (A := A) M.size)).flatten
    let setup := Routing.binaryCanonicalCopyProgram (r 0) (r 5) (r 3) (r 4)
    let pack := (narrowRecordWords r xs.length).seq (moveR (r 6) dst id)
    ∃ z, z.user = u.user ∧ Exec body (setup.seq pack) (mk u S)
      ((10*H+12)+(xs.length*(10*M.size+8*(H-M.size)+12)+1+(2*words.length+2)))
      (mk z {S with R := Function.update (Function.update (Function.update S.R (r 5) (binSyms M.size M)) (r 1) tail) dst (words ++ S.R dst)}) := by
  intro words setup pack
  have ports := ((by decide : ([0,5,3,4] : List (Fin 7)).Nodup).map r.injective)
  obtain ⟨v,hv,copy⟩ := swapWidth_exec body _ _ _ _ ports H M hm u S modulus
    (empty 5 (by decide)) (empty 3 (by decide)) (empty 4 (by decide))
  rw [canonicalBits_symbols] at copy
  let E : Stacks T A := {S with R := Function.update S.R (r 5) (binSyms M.size M)}
  have size : M.size+(H-M.size) = H := Nat.add_sub_of_le (Nat.size_le.mpr hm)
  obtain ⟨z,hz,run⟩ := narrowRecordArchive_exec body r dst outside M.size (H-M.size) xs
    (fun x h => (below x h).trans (Nat.lt_size_self _)) tail v E
    (by simpa [E,r.injective.eq_iff,size] using input)
    (by simp [E,r.injective.eq_iff,modulus,size,length_binSyms]) (by simp [E,length_binSyms])
    (by intro i hi
        have ok := (by decide : ∀ i ∈ ([2,3,4,6] : List (Fin 7)), i ≠ 5 ∧ i ∈ ([2,3,4,5,6] : List (Fin 7))) i hi
        simp [E,r.injective.eq_iff,ok.1,empty i ok.2])
  refine ⟨z,hz.trans hv,?_⟩
  simpa only [E,Function.update_of_ne (outside 5)] using Exec.seq copy run

/-- In the joined caller and record bank the modulus is borrowed from caller
slot 2. The private canonical modulus and parent archive occupy slots 2 and 23. -/
def parentArchivePorts : Fin 7 ↪ Fin 82 := ⟨![2,76,58,59,61,60,62],by decide⟩

theorem loadCanonicalParents_exec {T Q A : ℕ} {F U : Type} (body : F → Pr F T Q A U)
    (host : Fin 82 ↪ Fin T) (M H : ℕ) (hm : M < 2^H) (xs : List ℕ) (below : ∀ x ∈ xs, x < M)
    (u : HS T Q A U) (S : Stacks T A) (modulus : S.R (host 2) = binSyms H M)
    (archive : S.R (host 55) = (xs.map (binSyms H)).flatten)
    (empty : ∀ i ∈ ([58,59,60,61,62,76,81] : List (Fin 82)), S.R (host i) = []) :
    let r := parentArchivePorts.trans host
    let copy := bcopy (host 55) (host 76) (host 59) (host 61)
    let setup := Routing.binaryCanonicalCopyProgram (r 0) (r 5) (r 3) (r 4)
    let pack := (narrowRecordWords r xs.length).seq (moveR (r 6) (host 81) id)
    let words := (xs.map (binSyms (A := A) M.size)).flatten
    ∃ z, z.user = u.user ∧ Exec body (copy.seq (setup.seq pack)) (mk u S)
      ((6*(S.R (host 55)).length+6)+((10*H+12)+(xs.length*(10*M.size+8*(H-M.size)+12)+1+(2*words.length+2))))
      (mk z {S with R := Function.update (Function.update S.R (host 60) (binSyms M.size M)) (host 81) words}) := by
  intro r copy setup pack words
  have regs := ((by decide : ([55,76,59,61] : List (Fin 82)).Nodup).map host.injective)
  obtain ⟨v,hv,load⟩ := bcopy_exec body regs u S (empty 59 (by decide)) (empty 61 (by decide))
  rw [empty 76 (by decide),List.append_nil] at load
  let E : Stacks T A := {S with R := Function.update S.R (host 76) (S.R (host 55))}
  have distinct (i : Fin 7) : host 81 ≠ r i :=
    host.injective.ne ((by decide : ∀ i, 81 ≠ parentArchivePorts i) i)
  obtain ⟨z,hz,run⟩ := canonicalRecordArchive_exec body r (host 81) distinct M H hm xs below [] v E
    (by change E.R (host 2) = _; simp [E,host.injective.eq_iff,modulus])
    (by change E.R (host 76) = _; simp [E,archive])
    (by intro i hi
        have ok := (by decide : ∀ i ∈ ([2,3,4,5,6] : List (Fin 7)), parentArchivePorts i ≠ 76 ∧
          parentArchivePorts i ∈ ([58,59,60,61,62,76,81] : List (Fin 82))) i hi
        simp [E,r,host.injective.eq_iff,ok.1,empty _ ok.2])
  refine ⟨z,hz.trans hv,(Exec.seq load run).cast rfl ?_⟩
  congr 2
  funext j
  change Function.update (Function.update (Function.update E.R (host 60) _) (host 76) []) (host 81) _ j = _
  by_cases a : j = host 81 <;> by_cases b : j = host 76 <;> by_cases c : j = host 60 <;>
    simp_all [words,E,host.injective.eq_iff]

theorem recordVolumeHeaders_exec {T Q A : ℕ} {F U : Type}
    (body : F → Pr F T Q A U) (r : Fin 10 ↪ Fin T) (width : Fin T) (outside : ∀ i, width ≠ r i)
    (d H J M W : ℕ) (hm : M < 2^H) (hw : W < 2^J) (u : HS T Q A U) (S : Stacks T A)
    (base : S.R (r 0) = binSyms H M) (one : S.R (r 1) = binSyms 1 1)
    (trailing : S.R width = binSyms J W) (free : ∀ i : Fin 10, 2 ≤ i → S.R (r i) = []) :
    ∃ z n, z.user = u.user ∧ n ≤ dimensionTime H 1 d + (4*(d*H+1)+6) + (10*J+12) ∧
      Exec body ((swapPrefix r d).seq (Routing.binaryCanonicalCopyProgram width (r 9) (r 3) (r 4)))
        (mk u S) n (mk z {S with R := Function.update (Function.update S.R (r 2) (binSyms (M^d).size (M^d))) (r 9) (binSyms W.size W)}) := by
  obtain ⟨v,t,user,time,power⟩ := swapPrefix_exec body r d H M hm u S base one (fun i hi _ => free i hi)
  let D : Stacks T A := {S with R := Function.update S.R (r 2) ((FlatCoordinateSchedule.bits (M^d)).map bitSymbol)}
  have ports : [width,r 9,r 3,r 4].Nodup := by simp [outside,r.injective.eq_iff]
  obtain ⟨z,hz,copy⟩ := swapWidth_exec body width (r 9) (r 3) (r 4) ports J W hw v D
    (by simp [D,outside,trailing]) (by simp [D,r.injective.eq_iff,free])
    (by simp [D,r.injective.eq_iff,free]) (by simp [D,r.injective.eq_iff,free])
  refine ⟨z,_,hz.trans user,Nat.add_le_add_right time _,?_⟩
  simpa only [D,canonicalBits_symbols] using Exec.seq power copy

/-- The first 58 slots are the recursive caller bank. The following eight
slots hold the six loop controls and two temporary words. -/
def recordDimensionPorts : Fin 10 ↪ Fin 66 := ⟨![2,28,61,58,60,62,63,64,65,59],by decide⟩

/-- Port zero is the caller's payload. Port one selects the private coordinate
role, and the remaining ports are the six controls produced below. -/
def recordRoundTripPorts {K : ℕ} (slot : Fin K) : Fin 8 ↪ Fin (66+K) :=
  let positions : Fin 8 ↪ Fin 66 := ⟨![24,0,58,59,60,61,62,63],by decide⟩
  (positions.trans (Fin.castAddEmb K)).trans (Equiv.swap ((0 : Fin 66).castAdd K) (slot.natAdd 66)).toEmbedding

theorem recordRoundTripPorts_shared {K : ℕ} (slot : Fin K) :
    recordRoundTripPorts slot 1 = slot.natAdd 66 := by
  change Equiv.swap ((0 : Fin 66).castAdd K) (slot.natAdd 66) ((0 : Fin 66).castAdd K) = _
  exact Equiv.swap_apply_left _ _

theorem recordRoundTripPorts_other {K : ℕ} (slot : Fin K) (j : Fin 8) (ne : j ≠ 1) :
    recordRoundTripPorts slot j = ((![24,0,58,59,60,61,62,63] j : Fin 66).castAdd K) := by
  apply Equiv.swap_apply_of_ne_of_ne
  · exact (Fin.castAddEmb K).injective.ne ((by decide : ∀ j : Fin 8, j ≠ 1 →
      (![24,0,58,59,60,61,62,63] j : Fin 66) ≠ 0) j ne)
  · intro eq
    have h := congrArg Fin.val eq
    change (![24,0,58,59,60,61,62,63] j : Fin 66).val = 66+slot.val at h
    have := (![24,0,58,59,60,61,62,63] j : Fin 66).isLt
    omega

theorem recordRoundTripPorts_apart {K : ℕ} (slot i : Fin K) (j : Fin 8) (ne : j ≠ 1) :
    i.natAdd 66 ≠ recordRoundTripPorts slot j := by
  rw [recordRoundTripPorts_other slot j ne]
  intro eq
  have h := congrArg Fin.val eq
  change 66+i.val = (![24,0,58,59,60,61,62,63] j : Fin 66).val at h
  have := (![24,0,58,59,60,61,62,63] j : Fin 66).isLt
  omega

def recordCounterSetup {F U : Type} {T Q A : ℕ} (host : Fin 66 ↪ Fin T) (d : ℕ) : Pr F T Q A U :=
  let dim := recordDimensionPorts.trans host
  ((swapPrefix dim d).seq (Routing.binaryCanonicalCopyProgram (host 53) (dim 9) (dim 3) (dim 4))).seq
    (bcopy (host 61) (host 63) (host 64) (host 65))

theorem recordCounterSetup_exec {T Q A : ℕ} {F U : Type} (body : F → Pr F T Q A U)
    (host : Fin 66 ↪ Fin T) (d H J M W : ℕ) (hm : M < 2^H) (hw : W < 2^J)
    (u : HS T Q A U) (S : Stacks T A) (base : S.R (host 2) = binSyms H M)
    (one : S.R (host 28) = binSyms 1 1) (width : S.R (host 53) = binSyms J W)
    (empty : ∀ i : Fin 66, 58 ≤ i.val → S.L (host i) = [] ∧ S.R (host i) = []) :
    ∃ z D n, z.user = u.user ∧ n ≤ dimensionTime H 1 d + (4*(d*H+1)+6) + (10*J+12) + (6*(M^d).size+6) ∧
      Exec body (recordCounterSetup host d) (mk u S) n (mk z D) ∧ D.L = S.L ∧
      (∀ i : Fin 6, let j := host ((i.natAdd 58).castAdd 2)
        D.L j = [] ∧ D.R j = ![[],binSyms W.size W,[],binSyms (M^d).size (M^d),[],binSyms (M^d).size (M^d)] i) ∧
      ∀ j, host 59 ≠ j → host 61 ≠ j → host 63 ≠ j → D.R j = S.R j := by
  let dim := recordDimensionPorts.trans host
  have apart (i) : host 53 ≠ dim i :=
    host.injective.ne ((by decide : ∀ i, 53 ≠ recordDimensionPorts i) i)
  obtain ⟨v,t,user,time,run⟩ := recordVolumeHeaders_exec body dim (host 53) apart d H J M W hm hw u S base one width
    (fun i hi => (empty _ ((by decide : ∀ i : Fin 10, 2 ≤ i → 58 ≤ (recordDimensionPorts i).val) i hi)).2)
  let E : Stacks T A := {S with R := Function.update (Function.update S.R (host 61) (binSyms (M^d).size (M^d))) (host 59) (binSyms W.size W)}
  have spare (i : Fin 66) (h : 58 ≤ i.val) (a : i ≠ 59) (b : i ≠ 61) : E.R (host i) = [] := by
    simp [E,host.injective.eq_iff,a,b,(empty i h).2]
  have regs := ((by decide : ([61,63,64,65] : List (Fin 66)).Nodup).map host.injective)
  obtain ⟨z,hz,copy⟩ := bcopy_exec body regs v E (spare 64 (by decide) (by decide) (by decide))
    (spare 65 (by decide) (by decide) (by decide))
  have power : E.R (host 61) = binSyms (M^d).size (M^d) := by simp [E,host.injective.eq_iff]
  rw [power,spare 63 (by decide) (by decide) (by decide),List.append_nil,length_binSyms] at copy
  refine ⟨z,_,_,hz.trans user,Nat.add_le_add_right time _,Exec.seq run copy,rfl,?_,?_⟩
  · intro i
    constructor
    · exact (empty _ ((by decide : ∀ i : Fin 6, 58 ≤ ((i.natAdd 58).castAdd 2).val) i)).1
    · fin_cases i <;> simp [E,host.injective.eq_iff,Fin.natAdd,Fin.castAdd,empty]
  · intro j a b c
    simp [E,Function.update_of_ne a.symm,Function.update_of_ne b.symm,Function.update_of_ne c.symm]

open IntegerMultBounds.Networks.Shared50ModularControl (prime) in
theorem recordPayloadReturn_exec {T Q : ℕ} {F U : Type} (capacity : 217 ≤ Q)
    (body : F → Pr F T Q prime U) (dim ret : Fin 10 ↪ Fin T) (width : Fin T)
    (outside : ∀ i, width ≠ dim i) (apart : ∀ j, dim 2 ≠ ret j ∧ dim 9 ≠ ret j)
    (d H J M W : ℕ) (hm : M < 2^H) (hw : W < 2^J) (hM : 0 < M) (hW : 0 < W)
    (u : HS T Q prime U) (S : Stacks T prime) (base : S.R (dim 0) = binSyms H M)
    (one : S.R (dim 1) = binSyms 1 1) (trailing : S.R width = binSyms J W)
    (free : ∀ i : Fin 10, 2 ≤ i → S.R (dim i) = [])
    (empty : ∀ i : Fin 10, 2 ≤ i.val → S.L (ret i) = [] ∧ S.R (ret i) = [])
    (source : ℤ → Fin 4) (p : ℤ) (xs : List (ZMod 2)) (length : xs.length = M^(d+d)*W)
    (dst : ∀ z, readAt blank (S.L (ret 0)) (S.R (ret 0)) z = leafBitTape xs z)
    (src : ∀ z, readAt blank (S.L (ret 1)) (S.R (ret 1)) (z-p) = RadixToBinary.binaryEncoding.encode (source z)) :
    let generate := (swapPrefix dim d).seq (Routing.binaryCanonicalCopyProgram width (dim 9) (dim 3) (dim 4))
    let header : Fin 3 → Fin T := ![dim 9,dim 2,dim 2]
    let ports := (Fin.castAddEmb (n := 8) 2).trans ret
    let setup := Record.copyLeafHeaders header (returnHeaderTargets.trans ret) (ret 8) (ret 9) (List.finRange 3)
    let localRun : Pr Empty 8 217 prime U := (.act (pushMarkers [2,3,4,5,6,7]) : Pr Empty 8 217 prime U).seq
      (returnFromOrigin (Function.Embedding.refl _))
    let finish := setup.seq (statePlacedNormalized ports capacity (by decide) Empty.elim localRun)
    ∃ z D n, z.user = u.user ∧ n ≤ dimensionTime H 1 d + (4*(d*H+1)+6) + (10*J+12) +
      (6*(W.size+(M^d).size+(M^d).size)+19+((218*xs.length+1)*13+8)) ∧
      Exec body (generate.seq finish) (mk u S) n (mk z D) ∧
      (∀ z, readAt blank (D.L (ret 1)) (D.R (ret 1)) (z-p) =
        RadixToBinary.binaryEncoding.encode (putWord source p (xs.map SparseRoleCircuit.encode) z)) ∧
      ∀ j, dim 2 ≠ j → dim 9 ≠ j → (∀ i, ret i ≠ j) → D.L j = S.L j ∧ D.R j = S.R j := by
  intro generate header ports setup localRun finish
  obtain ⟨y,t,hy,ht,run⟩ := recordVolumeHeaders_exec body dim width outside d H J M W hm hw u S base one trailing free
  let E : Stacks T prime := {S with R := Function.update (Function.update S.R (dim 2) (binSyms (M^d).size (M^d))) (dim 9) (binSyms W.size W)}
  have keep (j) (a : dim 2 ≠ j) (b : dim 9 ≠ j) : E.R j = S.R j := by simp [E,a.symm,b.symm]
  have len : xs.length = M^d*(M^d*W) := by rw [length,pow_add,Nat.mul_assoc]
  have disjoint (i : Fin 3) (j : Fin 10) : header i ≠ ret j := by
    fin_cases i <;> first | exact (apart j).2 | exact (apart j).1
  obtain ⟨z,D,n,hz,hn,retRun,read,frame⟩ := stagedLeafReturn_exec (pow_pos hM d) (pow_pos hM d) hW
    capacity body ret header disjoint y E source p xs len
    (by intro z; rw [keep _ (apart 0).1 (apart 0).2]; exact dst z)
    (by intro z; rw [keep _ (apart 1).1 (apart 1).2]; exact src z)
    (by intro i; fin_cases i <;> simp [E,header,dim.injective.eq_iff])
    (by intro i hi; rw [keep _ (apart i).1 (apart i).2]; exact empty i hi)
  refine ⟨z,D,_,hz.trans hy,?_,Exec.seq run retRun,read,?_⟩
  · rw [len]; exact Nat.add_le_add ht hn
  · intro j a b off
    exact ⟨(frame j off).1,(frame j off).2.trans (keep j a b)⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
