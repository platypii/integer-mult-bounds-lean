module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodRecordRoundTrip
public import IntegerMultBounds.MathlibTM2.Cover.FallbackMatrixBuildCost
public import IntegerMultBounds.MathlibTM2.Cover.FallbackIdentitySeed
public import IntegerMultBounds.MathlibTM2.Cover.FallbackFormulaInit
public import IntegerMultBounds.MathlibTM2.Cover.FallbackPhysicalScanData
public import IntegerMultBounds.MathlibTM2.Cover.FallbackRecordHeaders
public import IntegerMultBounds.MathlibTM2.Cover.ProjectorWitness
public import IntegerMultBounds.MathlibTM2.Cover.LabelCountBank
public import IntegerMultBounds.MathlibTM2.Cover.FallbackRecordMasks
public import IntegerMultBounds.MathlibTM2.Cover.FallbackRecordCounters

/-! Read a live directory label, compute the conjugate, and run the good-record round trip. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open M8.RevMachine RecursiveInterchangeLayout Matrix Finset IntegerMultBounds.Swap.LowerTriangular
  IntegerMultBounds.Swap.Modular
local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨pow_ne_zero _ Networks.Shared50ModularControl.prime_prime.ne_zero⟩

section
open RingFormula IntegerMultBounds.MathlibTM2.Fast.Main
/-- The queue writer uses private registers, with its output at the matrix tape
consumed by the classified scan. -/
noncomputable def directoryQueueBank [M8.Machine.Net] {K d r : ℕ}
    (room : Record.size d+(rowSwapBlock.tapes+35+2) ≤ K)
    (fits : (36+2*r+1+(conjugationDepth r+1)*13)+3 ≤ K) :=
  let privateBank := (Fin.castLEEmb fits).trans (Fin.natAddEmb 66)
  let output := privateBank ⟨36+2*r,by omega⟩
  privateBank.trans (Equiv.swap output (directoryMatrixTape room)).toEmbedding

theorem directoryQueueBank_archive [M8.Machine.Net] {K d r : ℕ}
    (room : Record.size d+(rowSwapBlock.tapes+35+2) ≤ K)
    (fits : (36+2*r+1+(conjugationDepth r+1)*13)+3 ≤ K) :
    directoryQueueBank room fits ⟨36+2*r,by omega⟩ = directoryMatrixTape room :=
  Equiv.swap_apply_left ..

theorem directoryQueueBank_caller [M8.Machine.Net] {K d r : ℕ}
    (room : Record.size d+(rowSwapBlock.tapes+35+2) ≤ K)
    (fits : (36+2*r+1+(conjugationDepth r+1)*13)+3 ≤ K)
    (i) (j : Fin 66) : directoryQueueBank room fits i ≠ j.castAdd K := by
  let base := (Fin.castLEEmb fits).trans (Fin.natAddEmb 66)
  have off (k) : base k ≠ j.castAdd K := by
    intro eq; have h := congrArg Fin.val eq; change 66+k.val = j.val at h; omega
  have archiveOff : directoryMatrixTape room ≠ j.castAdd K := by
    intro eq; have h := directoryMatrixTape_private room; rw [eq] at h; exact j.isLt.not_ge h
  change Equiv.swap (base _) (directoryMatrixTape room) (base i) ≠ _
  intro eq
  apply off i
  rw [← Equiv.swap_apply_self (base ⟨36+2*r,by omega⟩) (directoryMatrixTape room) (base i),eq]
  exact Equiv.swap_apply_of_ne_of_ne (off _).symm archiveOff.symm

/-- Modulus, prefix width, projector, unit, reciprocal modulus and unit, and both clocks
in the directory reader, elimination bank, and exponent counter, respectively. -/
def directoryQueueHeaderSlots : Fin 8 ↪ Fin 35 :=
  ⟨![8,12,16,17,22,33,34,1],by decide⟩

theorem directoryQueueHeaders_exec [M8.Machine.Net] {K d r Q : ℕ} {P U : Type}
    (room : Record.size d+(rowSwapBlock.tapes+35+2) ≤ K)
    (fits : (36+2*r+1+(conjugationDepth r+1)*13)+3 ≤ K)
    (body : P → Pr P (66+K) Q prime U) (u : HS (66+K) Q prime U) (S : Stacks (66+K) prime) :
    let bank := directoryQueueBank room fits
    let src := fun i : Fin 8 => ((![2,47,48,44,2,44,45,45] i : Fin 66)).castAdd K
    let dst := (directoryQueueHeaderSlots.trans (Fin.castLEEmb (by omega))).trans bank
    let tmp := bank ⟨4,by omega⟩
    let aux := bank ⟨6,by omega⟩
    let pool := QueueLayout.block (n := (conjugationDepth r+1)*13) (36+2*r+1) (by omega) bank
    let srcMod := (2 : Fin 66).castAdd K
    let digits := dst 7
    S.R tmp = [] → S.R aux = [] → (∀ i, S.R (dst i) = []) →
    (∀ i, S.R (pool i) = []) →
    ∃ z F, z.user = u.user ∧ Exec body (((Record.copyLeafHeaders src dst tmp aux (List.finRange 8)).seq
      (initFrames pool srcMod (conjugationDepth r+1))).seq (.act (.push (.rt digits) (fun _ => Node.tick) .done)))
      (mk u S) (((List.finRange 8).map fun i => 6*(S.R (src i)).length+6).sum+1 + ((conjugationDepth r+1)*(6*(S.R srcMod).length+6)+1)+1) (mk z F) ∧
      F.L = S.L ∧ (∀ i, F.R (dst i) = if i = 7 then Node.tick :: S.R (src i) else S.R (src i)) ∧
      (∀ j : Fin 66, F.R (j.castAdd K) = S.R (j.castAdd K)) ∧
      (∀ k ≤ conjugationDepth r, F.R (frame pool k 2) = S.R srcMod) ∧
      (∀ k ≤ conjugationDepth r, ∀ i : Fin 13, i ≠ 2 → F.R (frame pool k i) = []) ∧
      ∀ k, (∀ i, dst i ≠ k) → (∀ i, k ≠ pool i) → F.R k = S.R k := by
  intro bank src dst tmp aux pool srcMod digits tmpFree auxFree empty poolFree
  have outside (i : Fin 8) j : src i ≠ bank j := (directoryQueueBank_caller room fits j _).symm
  have separate (i : Fin 8) : dst i ≠ tmp ∧ dst i ≠ aux := by
    have avoid : ∀ j, (directoryQueueHeaderSlots j).val ≠ 4 ∧ (directoryQueueHeaderSlots j).val ≠ 6 := by decide
    constructor <;> intro eq <;> have h := congrArg Fin.val (bank.injective eq)
    · exact (avoid i).1 h
    · exact (avoid i).2 h
  have ports (i) : [src i,dst i,tmp,aux].Nodup := by
    have sd : src i ≠ dst i := outside i _
    have st : src i ≠ tmp := outside i _
    have sa : src i ≠ aux := outside i _
    have ta : tmp ≠ aux := bank.injective.ne (fun eq => (by decide : 4 ≠ 6) (congrArg Fin.val eq))
    simp [sd,st,sa,(separate i).1,(separate i).2,ta]
  obtain ⟨z,F,user,run,left,loaded,keep⟩ := Record.copyLeafHeaders_exec body src dst tmp aux
    (fun i j => outside i _) ports _ (List.nodup_finRange 8) u S tmpFree auxFree (fun i _ => empty i)
  have dp (i j) : dst i ≠ pool j := by
    intro eq
    have h := congrArg Fin.val (bank.injective eq)
    change (directoryQueueHeaderSlots i).val = 36+2*r+1+j.val at h
    have := (directoryQueueHeaderSlots i).isLt
    omega
  have callerKeep (j : Fin 66) := keep (j.castAdd K) (fun i _ => directoryQueueBank_caller room fits _ j)
  have modEq : F.R srcMod = S.R srcMod := callerKeep 2
  have poolBlank (j) := (keep (pool j) (fun i _ => dp i j)).trans (poolFree j)
  obtain ⟨y,E,hy,init,_,_,leftE,moduli,rest⟩ := initFrames_exec body pool srcMod
    (fun j => (directoryQueueBank_caller room fits _ 2).symm) z F poolBlank (conjugationDepth r+1) le_rfl
  rw [modEq] at init moduli
  have frameOff (k) (h : ∀ i, k ≠ pool i) := rest k (fun _ _ => h _)
  let D := {E with R := Function.update E.R digits (Node.tick :: E.R digits)}
  have push : Exec body (.act (.push (.rt digits) (fun _ => Node.tick) .done)) (mk y E) 1 (mk y D) := by
    simpa [D,Action.run,update_rt] using Exec.act (body := body) (.push (.rt digits) (fun _ => Node.tick) .done) (mk y E)
  have intact (k) (off : k ≠ digits) : D.R k = E.R k := Function.update_of_ne off _ _
  have value (i) := (frameOff _ (dp i)).trans (loaded i (List.mem_finRange i))
  refine ⟨y,D,hy.trans user,Exec.seq (Exec.seq run init) push,leftE.trans left,?_,?_,?_,?_,?_⟩
  · intro i
    by_cases eq : i = 7
    · subst i
      exact (Function.update_self ..).trans (by simp only [ite_true]; rw [show E.R digits = _ from value 7])
    · simpa only [if_neg eq] using (intact _ (dst.injective.ne eq)).trans (value i)
  · intro j
    exact (intact _ (directoryQueueBank_caller room fits _ j).symm).trans
      ((frameOff _ (fun i => (directoryQueueBank_caller room fits _ j).symm)).trans (callerKeep j))
  · intro k hk
    exact (intact _ (dp 7 _).symm).trans (moduli k (by omega))
  · intro k hk i ne
    apply (intact _ (dp 7 _).symm).trans
    apply (rest _ (fun l hl eq => ne (congrArg Prod.snd (finProdFinEquiv.injective (pool.injective eq))))).trans
    exact poolBlank _
  · intro k hd hp
    exact (intact k (hd 7).symm).trans ((frameOff k hp).trans (keep k (fun i _ => hd i)))

/-- Construct the fixed-width zero and padding identity in the writer's private bank. -/
theorem directoryQueuePadding_exec [M8.Machine.Net] {K d r Q H w : ℕ} {P U : Type}
    (room : Record.size d+(rowSwapBlock.tapes+35+2) ≤ K)
    (fits : (36+2*r+1+(conjugationDepth r+1)*13)+3 ≤ K)
    (body : P → Pr P (66+K) Q prime U) (u : HS (66+K) Q prime U) (S : Stacks (66+K) prime) :
    let bank := directoryQueueBank room fits
    let base := 36+2*r+1+(conjugationDepth r+1)*13
    let width := bank ⟨8,by omega⟩
    let zero := bank ⟨9,by omega⟩
    let one := bank ⟨17,by omega⟩
    let tmp := bank ⟨4,by omega⟩
    let seed := bank ⟨base+1,by omega⟩
    let saved := bank ⟨base+2,by omega⟩
    let M := prime^(w+1)
    let B := {S with R := Function.update S.R zero (binSyms H 0)}
    let D := {B with R := Function.update B.R seed (matrixWords prime H (1 : Matrix (Fin (d+1)) (Fin (d+1)) (ZMod M)))}
    (S.R width).length = H → S.R one = binSyms H (1 : ZMod M).val →
    S.R zero = [] → S.R seed = [] → S.R tmp = [] → S.R saved = [] →
    ∃ z n, z.user = u.user ∧ n ≤ (4*H+4)+((d+1)*((d+1)*(6*H+6)+1)+1) ∧
      Exec body ((Node.umulSym 1 (bitSymbol false) width zero tmp).seq (identitySeed (d+1) zero one seed tmp saved))
        (mk u S) n (mk z D) := by
  intro bank base width zero one tmp seed saved M B D clock unit zeroFree seedFree tmpFree savedFree
  have large : 35 < base := by dsimp [base]; omega
  have different (i j : Fin (base+3)) (h : i.val ≠ j.val) : bank i ≠ bank j :=
    bank.injective.ne (fun eq => h (congrArg Fin.val eq))
  obtain ⟨y,user,writeZero⟩ := Node.umulSym_exec body 1 (bitSymbol false) (a := width) (b := zero) (t := tmp)
    (different _ _ (by decide : 8 ≠ 9)) (different _ _ (by decide : 8 ≠ 4)) (different _ _ (by decide : 9 ≠ 4)) u S tmpFree
  have binaryZero : (binSyms H 0 : List (Fin (prime+4))) = List.replicate H (bitSymbol false) := by
    simp [binSyms,List.ofFn_const]
  rw [clock,Nat.one_mul,zeroFree,List.append_nil,← binaryZero] at writeZero
  have ports (i : Fin (base+3)) (small : i.val < base) (off : i.val ≠ 4) :
      [bank i,seed,tmp,saved].Nodup := by
    have a : bank i ≠ seed := different _ _ (by change i.val ≠ base+1; omega)
    have b : bank i ≠ tmp := different _ _ off
    have c : bank i ≠ saved := different _ _ (by change i.val ≠ base+2; omega)
    have e : seed ≠ tmp := different _ _ (by change base+1 ≠ 4; omega)
    have f : seed ≠ saved := different _ _ (by change base+1 ≠ base+2; omega)
    have g : tmp ≠ saved := different _ _ (by change 4 ≠ base+2; omega)
    simp [a,b,c,e,f,g]
  have keep (i : Fin (base+3)) (h : i.val ≠ 9) : B.R (bank i) = S.R (bank i) :=
    Function.update_of_ne (different _ _ h) _ _
  obtain ⟨z,n,hz,time,writeSeed⟩ := identitySeed_writes («M» := M) body (d+1) H zero one seed tmp saved
    (ports _ (by change 9 < base; omega) (by decide : 9 ≠ 4))
    (ports _ (by change 17 < base; omega) (by decide : 17 ≠ 4))
    y B ⟨Function.update_self ..,(keep _ (by decide : 17 ≠ 9)).trans unit,
      (keep _ (by decide : 4 ≠ 9)).trans tmpFree,(keep _ (by change base+2 ≠ 9; omega)).trans savedFree⟩
  rw [(keep _ (by change base+1 ≠ 9; omega)).trans seedFree,List.append_nil] at writeSeed
  exact ⟨z,_,hz.trans user,Nat.add_le_add_left time _,Exec.seq writeZero writeSeed⟩

/-- Route the two outputs into the row and column slots for this index.
The packed source stays on caller tape 55. -/
noncomputable def directoryParentPorts [M8.Machine.Net] {K d m : ℕ}
    (room : Record.size d+(rowSwapBlock.tapes+35+2) ≤ K)
    (fits : (36+2*m+1+(conjugationDepth m+1)*13)+3 ≤ K) (j : Fin m) : Fin 19 ↪ Fin (66+K) := by
  let bank := directoryQueueBank room fits
  let slot (i : Fin 19) : Fin ((36+2*m+1+(conjugationDepth m+1)*13)+3) :=
    ⟨if i.val = 0 then 36+m+j.val else if i.val = 14 then 36+j.val else 18+i.val,by
      split_ifs <;> omega⟩
  refine ⟨fun i => if i = 18 then (55 : Fin 66).castAdd K else bank (slot i),?_⟩
  intro i k eq
  dsimp only at eq
  split_ifs at eq with a b b
  · exact a.trans b.symm
  · exact ((directoryQueueBank_caller room fits _ 55) eq.symm).elim
  · exact ((directoryQueueBank_caller room fits _ 55) eq).elim
  · have h := congrArg Fin.val (bank.injective eq)
    have hi : i.val ≠ 18 := fun h => a (Fin.ext h)
    have hk : k.val ≠ 18 := fun h => b (Fin.ext h)
    apply Fin.ext
    dsimp only [slot] at h
    split_ifs at h <;> omega

/-- Read one parent coefficient without consuming the packed word, then
compute its inverse with the writer's reusable exponent clock. -/
theorem directoryParentPair_exec [M8.Machine.Net] {K d Q m H w : ℕ} {P U : Type}
    (room : Record.size d+(rowSwapBlock.tapes+35+2) ≤ K)
    (fits : (36+2*m+1+(conjugationDepth m+1)*13)+3 ≤ K) (body : P → Pr P (66+K) Q prime U)
    (parent inv : Fin m → ZMod (prime^(w+1))) (j : Fin m) (reciprocal : parent j * inv j = 1)
    (hm : prime^(w+1) < 2^H) (u : HS (66+K) Q prime U) (S : Stacks (66+K) prime) :
    let ports := directoryParentPorts room fits j
    let readSlots : Fin 7 ↪ Fin 19 := ⟨![1,4,18,14,2,3,5],by decide⟩
    let readPorts := readSlots.trans ports
    let pivot := (Fin.castLEEmb (by decide : 16 ≤ 19)).trans ports
    S.R (ports 18) = (List.ofFn fun i => binSyms H (parent i).val).flatten →
    S.R (ports 4) = binSyms H (prime^(w+1)) →
    S.R (ports 15) = binSyms H (1 : ZMod (prime^(w+1))).val →
    (S.R (ports 16)).length = w → S.R (ports 17) = [] → S.R (ports 14) = [] →
    (∀ i : Fin 16, i ≠ 4 → i < 13 → S.R (pivot i) = []) →
    let C := 48*H*H+152*H+66
    let B := {S with R := Function.update S.R (ports 14) (binSyms H (parent j).val)}
    let D := {B with R := Function.update B.R (ports 0) (binSyms H (inv j).val)}
    ∃ z n, z.user = u.user ∧ n ≤ (8*(j.val*H)+14*H+22) +
        (6*w+6+(14*H+16+(prime-2)*C+C+w*(12*H+15+prime*C))) ∧
      Exec body ((readMatrixWord j.val readPorts).seq (reusablePivotInverse prime pivot (ports 16) (ports 17)))
        (mk u S) n (mk z D) := by
  intro ports readSlots readPorts pivot packed modulus unit ticks empty fresh free C B D
  let row : Matrix (Fin 1) (Fin m) (ZMod (prime^(w+1))) := fun _ i => parent i
  have scratch (k : Fin 7) (h : k = 0 ∨ 4 ≤ k) : S.R (readPorts k) = [] := by
    fin_cases k <;> first | exact free 1 (by decide) (by decide) | exact free 2 (by decide) (by decide) | exact free 3 (by decide) (by decide) | exact free 5 (by decide) (by decide) | norm_num at h
  obtain ⟨y,hy,read⟩ := readMatrixWord_exec body readPorts row 0 j H u S []
    (by simpa [row,matrixWords,List.ofFn_succ,readPorts,readSlots] using packed)
    ((congrArg List.length modulus).trans (length_binSyms ..)) scratch
  change Exec _ (readMatrixWord (0*m+j.val) _) _ (8*((0*m+j.val)*H)+14*H+22)
    (mk y {S with R := Function.update S.R (ports 14) (binSyms H (parent j).val ++ S.R (ports 14))}) at read
  simp only [Nat.zero_mul,Nat.zero_add,fresh,List.append_nil] at read
  have keep (i : Fin 19) (off : i ≠ 14) : B.R (ports i) = S.R (ports i) := Function.update_of_ne (ports.injective.ne off) _ _
  have inverse := Itinerary.inverse_unique reciprocal
  obtain ⟨z,F,n,user,price,run,_,out,left,inp,output,frame⟩ := reusablePivotInverse_exec body prime w
    Networks.Shared50ModularControl.prime_prime (parent j) (isUnit_iff_exists_inv.mpr ⟨_,reciprocal⟩) pivot (ports 16) (ports 17)
    ((by decide : ([16,17,2,3] : List (Fin 19)).Nodup).map ports.injective)
    (fun i => ports.injective.ne (by intro eq; have h := congrArg Fin.val eq; change i.val = 17 at h; omega))
    H hm y B ((congrArg List.length (keep 16 (by decide))).trans ticks) ((keep 17 (by decide)).trans empty)
    (Function.update_self ..) ((keep 15 (by decide)).trans unit) ((keep 4 (by decide)).trans modulus)
    (fun i hi lt => (keep _ (by intro eq; have h := congrArg Fin.val eq; change i.val = 14 at h; omega)).trans (free i hi lt))
  rw [inverse] at out
  have finalState : F = D := by
    refine Stacks.ext inp output left ?_
    funext k
    by_cases eq : k = ports 0
    · subst k; change F.R (ports 0) = _ at out; rw [out]; exact (Function.update_self (ports 0) _ B.R).symm
    · exact (frame k eq).trans (Function.update_of_ne eq _ _).symm
  exact ⟨z,_,user.trans hy,Nat.add_le_add_left price _,finalState ▸ Exec.seq read run⟩

private theorem directoryParentPorts_separate [M8.Machine.Net] {K d m : ℕ}
    (room : Record.size d+(rowSwapBlock.tapes+35+2) ≤ K)
    (fits : (36+2*m+1+(conjugationDepth m+1)*13)+3 ≤ K) {i j : Fin m} (distinct : i ≠ j)
    (k : Fin 19) : directoryParentPorts room fits i k ≠ directoryParentPorts room fits j 0 ∧
      directoryParentPorts room fits i k ≠ directoryParentPorts room fits j 14 := by
  have ne : i.val ≠ j.val := fun eq => distinct (Fin.ext eq)
  by_cases last : k = 18
  · subst k
    exact ⟨(directoryQueueBank_caller room fits _ 55).symm,(directoryQueueBank_caller room fits _ 55).symm⟩
  have small : k.val < 18 := by
    have h : k.val ≠ 18 := fun eq => last (Fin.ext eq)
    omega
  simp only [directoryParentPorts,Function.Embedding.coeFn_mk,if_neg last,show (0 : Fin 19) ≠ 18 by decide,
    show (14 : Fin 19) ≠ 18 by decide,ite_false]
  constructor <;> intro eq <;> have h := congrArg Fin.val ((directoryQueueBank room fits).injective eq) <;>
    dsimp at h <;> split_ifs at h <;> omega

/-- Load every row coefficient and its reciprocal column coefficient, retaining
the packed parent tape and the other writer registers. -/
theorem directoryParentBank_exec [M8.Machine.Net] {K d Q m H w : ℕ} {P U : Type}
    (room : Record.size d+(rowSwapBlock.tapes+35+2) ≤ K)
    (fits : (36+2*m+1+(conjugationDepth m+1)*13)+3 ≤ K) (body : P → Pr P (66+K) Q prime U)
    (parent inv : Fin m → ZMod (prime^(w+1))) (reciprocal : ∀ j, parent j * inv j = 1)
    (hm : prime^(w+1) < 2^H) (u : HS (66+K) Q prime U) (S : Stacks (66+K) prime) :
    let ports := directoryParentPorts room fits
    let readSlots : Fin 7 ↪ Fin 19 := ⟨![1,4,18,14,2,3,5],by decide⟩
    let pivot := fun j => (Fin.castLEEmb (by decide : 16 ≤ 19)).trans (ports j)
    let program := fun j => (readMatrixWord j.val (readSlots.trans (ports j))).seq
      (reusablePivotInverse prime (pivot j) (ports j 16) (ports j 17))
    let C := 48*H*H+152*H+66
    let price := fun j : Fin m => (8*(j.val*H)+14*H+22)+(6*w+6+(14*H+16+(prime-2)*C+C+w*(12*H+15+prime*C)))
    let bank := directoryQueueBank room fits
    S.R ((55 : Fin 66).castAdd K) = (List.ofFn fun i => binSyms H (parent i).val).flatten →
    S.R (bank ⟨22,by omega⟩) = binSyms H (prime^(w+1)) →
    S.R (bank ⟨33,by omega⟩) = binSyms H (1 : ZMod (prime^(w+1))).val →
    (S.R (bank ⟨34,by omega⟩)).length = w →
    (∀ i, i.val = 35 ∨ (19 ≤ i.val ∧ i.val < 31 ∧ i.val ≠ 22) ∨ (36 ≤ i.val ∧ i.val < 36+2*m) →
      S.R (bank i) = []) →
    ∃ z F n, z.user = u.user ∧ n ≤ ((List.finRange m).map price).sum+1 ∧
      Exec body (Prog.seqList ((List.finRange m).map program)) (mk u S) n (mk z F) ∧
      F.L = S.L ∧ F.inp = S.inp ∧ F.out = S.out ∧
      (∀ j, F.R (ports j 14) = binSyms H (parent j).val ∧ F.R (ports j 0) = binSyms H (inv j).val) ∧
      ∀ k, (∀ j, k ≠ ports j 14 ∧ k ≠ ports j 0) → F.R k = S.R k := by
  intro ports readSlots pivot program C price bank packedHeader modulusHeader unitHeader clockHeader blank
  have ready : ∀ j : Fin m, S.R (ports j 18) = (List.ofFn fun i => binSyms H (parent i).val).flatten ∧
      S.R (ports j 4) = binSyms H (prime^(w+1)) ∧ S.R (ports j 15) = binSyms H (1 : ZMod (prime^(w+1))).val ∧
      (S.R (ports j 16)).length = w ∧ S.R (ports j 17) = [] ∧ S.R (ports j 14) = [] ∧
      ∀ i : Fin 16, i ≠ 4 → i < 13 → S.R (pivot j i) = [] := by
    intro j
    refine ⟨packedHeader,modulusHeader,unitHeader,clockHeader,blank _ (Or.inl rfl),
      blank _ (Or.inr (Or.inr (by change 36 ≤ 36+j.val ∧ 36+j.val < 36+2*m; omega))),?_⟩
    intro i hi small
    by_cases zero : i = 0
    · subst i
      exact blank _ (Or.inr (Or.inr (by change 36 ≤ 36+m+j.val ∧ 36+m+j.val < 36+2*m; omega)))
    · have nz : i.val ≠ 0 := fun eq => zero (Fin.ext eq)
      have notFour : i.val ≠ 4 := fun eq => hi (Fin.ext eq)
      have upper : i.val < 13 := small
      have atSlot : pivot j i = bank ⟨18+i.val,by omega⟩ := by
        let k : Fin 19 := i.castLE (by decide)
        have off : k ≠ 18 := by intro eq; have val := congrArg Fin.val eq; change i.val = 18 at val; omega
        change (if k = 18 then _ else bank ⟨if i.val = 0 then _ else if i.val = 14 then _ else 18+i.val,_⟩) = _
        rw [if_neg off]
        apply congrArg bank
        apply Fin.ext
        change (if i.val = 0 then _ else if i.val = 14 then _ else 18+i.val) = 18+i.val
        rw [if_neg nz,if_neg (show i.val ≠ 14 by omega)]
      rw [atSlot]
      exact blank _ (Or.inr (Or.inl (by change 19 ≤ 18+i.val ∧ 18+i.val < 31 ∧ 18+i.val ≠ 22; omega)))
  have loop (js : List (Fin m)) (unique : js.Nodup) (v : HS (66+K) Q prime U) (B : Stacks (66+K) prime)
      (pending : ∀ j ∈ js, ∀ k, B.R (ports j k) = S.R (ports j k)) :
      ∃ z F n, z.user = v.user ∧ n ≤ (js.map price).sum+1 ∧
        Exec body (Prog.seqList (js.map program)) (mk v B) n (mk z F) ∧
        F.L = B.L ∧ F.inp = B.inp ∧ F.out = B.out ∧
        (∀ j ∈ js, F.R (ports j 14) = binSyms H (parent j).val ∧ F.R (ports j 0) = binSyms H (inv j).val) ∧
        ∀ k, (∀ j ∈ js, k ≠ ports j 14 ∧ k ≠ ports j 0) → F.R k = B.R k := by
    induction js generalizing v B with
    | nil => exact ⟨v,B,1,rfl,by simp,by simpa [Prog.seqList,Action.run] using Exec.act (body := body) .done (mk v B),
        rfl,rfl,rfl,by simp,by simp⟩
    | cons j js ih =>
      have now := pending j List.mem_cons_self
      obtain ⟨packed,modulus,unit,ticks,empty,fresh,free⟩ := ready j
      obtain ⟨y,t,user,time,run⟩ := directoryParentPair_exec room fits body parent inv j (reciprocal j) hm v B
        ((now 18).trans packed) ((now 4).trans modulus) ((now 15).trans unit) ((congrArg List.length (now 16)).trans ticks)
        ((now 17).trans empty) ((now 14).trans fresh) (fun i hi hl => (now _).trans (free i hi hl))
      let E := {B with R := Function.update (Function.update B.R (ports j 14) (binSyms H (parent j).val)) (ports j 0) (binSyms H (inv j).val)}
      have keep (k) (row : k ≠ ports j 14) (col : k ≠ ports j 0) : E.R k = B.R k :=
        (Function.update_of_ne col _ _).trans (Function.update_of_ne row _ _)
      have sep (i) (mem : i ∈ js) k := directoryParentPorts_separate room fits
        (show i ≠ j from fun eq => unique.notMem (eq ▸ mem)) k
      obtain ⟨z,F,n,hz,hn,rest,left,input,output,loaded,frame⟩ := ih unique.tail y E
        (fun i mem k => (keep _ (sep i mem k).2 (sep i mem k).1).trans (pending i (List.mem_cons_of_mem _ mem) k))
      refine ⟨z,F,t+n,hz.trans user,?_,Exec.seq run rest,left,input,output,?_,?_⟩
      · simpa only [List.map_cons,List.sum_cons,Nat.add_assoc] using Nat.add_le_add (show t ≤ price j from time) hn
      · intro i mem
        rcases List.mem_cons.mp mem with rfl | h
        · have stored (k) := frame (ports i k) (fun l hl => by
            have h : i ≠ l := fun eq => unique.notMem (eq ▸ hl)
            exact ⟨(directoryParentPorts_separate room fits h k).2,(directoryParentPorts_separate room fits h k).1⟩)
          exact ⟨(stored 14).trans ((Function.update_of_ne ((ports i).injective.ne (by decide : (14 : Fin 19) ≠ 0)) _ _).trans (Function.update_self ..)),
            (stored 0).trans (Function.update_self ..)⟩
        · exact loaded i h
      · intro k off
        exact (frame k (fun i mem => off i (List.mem_cons_of_mem _ mem))).trans
          (keep k (off j List.mem_cons_self).1 (off j List.mem_cons_self).2)
  obtain ⟨z,F,n,user,time,run,left,input,output,loaded,keep⟩ := loop _ (List.nodup_finRange m) u S (by intros; rfl)
  exact ⟨z,F,n,user,time,run,left,input,output,fun j => loaded j (List.mem_finRange j),fun k h => keep k (fun j _ => h j)⟩

/-- Seed both inputs consumed by the matrix writer from the directory and
selector retained for the classified scan. The two copies reuse the same scratch. -/
theorem directoryQueueInputs_exec [M8.Machine.Net] {K d r Q w records : ℕ} {P U : Type}
    (room : Record.size d+(rowSwapBlock.tapes+35+2) ≤ K)
    (fits : (36+2*r+1+(conjugationDepth r+1)*13)+3 ≤ K)
    (body : P → Pr P (66+K) Q prime U) (u : HS (66+K) Q prime U) (S : Stacks (66+K) prime) :
    let bank := directoryQueueBank room fits
    let base := 36+2*r+1+(conjugationDepth r+1)*13
    let dir := bank ⟨2,by omega⟩
    let mask := bank ⟨base,by omega⟩
    let tmp := bank ⟨base+2,by omega⟩
    let spare := bank ⟨4,by omega⟩
    let source := (46 : Fin 66).castAdd K
    let live := (57 : Fin 66).castAdd K
    let masked := {S with R := Function.update S.R mask (S.R live)}
    let D := {masked with R := Function.update masked.R dir (S.R source)}
    S.R live = (List.range records).map (fun j => bitSymbol (LabelStock.live r (w+1) 1 j)) →
    S.R mask = [] → S.R dir = [] → S.R spare = [] → S.R tmp = [] →
    ∃ v, v.user = u.user ∧ D.R mask = (List.range records).map (fun j => bitSymbol (LabelStock.live r (w+1) 1 j)) ∧
      D.R dir = S.R source ∧ Exec body ((bcopy live mask spare tmp).seq (bcopy source dir spare tmp))
        (mk u S) ((6*records+6)+(6*(S.R source).length+6)) (mk v D) := by
  intro bank base dir mask tmp spare source live masked D bits maskFree dirFree spareFree tmpFree
  have privateOff i (j : Fin 66) := (directoryQueueBank_caller room fits i j).symm
  have below : 4 < base := by dsimp [base]; omega
  have different (i j : Fin (base+3)) (h : i.val ≠ j.val) : bank i ≠ bank j :=
    bank.injective.ne (fun eq => h (congrArg Fin.val eq))
  have sm : spare ≠ mask := different _ _ (by change 4 ≠ base; omega)
  have tm : tmp ≠ mask := different _ _ (by change base+2 ≠ base; omega)
  have dm : dir ≠ mask := different _ _ (by change 2 ≠ base; omega)
  have st : spare ≠ tmp := different _ _ (by change 4 ≠ base+2; omega)
  have ds : dir ≠ spare := different _ _ (by decide : 2 ≠ 4)
  have dt : dir ≠ tmp := different _ _ (by change 2 ≠ base+2; omega)
  have maskRegs : [live,mask,spare,tmp].Nodup := by
    simp [live,mask,spare,tmp,List.nodup_cons,sm.symm,tm.symm,st]
    exact ⟨privateOff _ 57,privateOff _ 57,privateOff _ 57⟩
  have dirRegs : [source,dir,spare,tmp].Nodup := by
    simp [source,dir,spare,tmp,List.nodup_cons,ds,dt,st]
    exact ⟨privateOff _ 46,privateOff _ 46,privateOff _ 46⟩
  obtain ⟨y,hy,writeMask⟩ := bcopy_exec body maskRegs u S spareFree tmpFree
  rw [maskFree,List.append_nil] at writeMask
  have len : (S.R live).length = records := by simp [bits]
  rw [len] at writeMask
  obtain ⟨v,hv,writeDir⟩ := bcopy_exec body dirRegs y masked
    ((Function.update_of_ne sm _ _).trans spareFree) ((Function.update_of_ne tm _ _).trans tmpFree)
  have src : masked.R source = S.R source := Function.update_of_ne (privateOff _ 46) _ _
  have empty : masked.R dir = [] := (Function.update_of_ne dm _ _).trans dirFree
  rw [src,empty,List.append_nil] at writeDir
  exact ⟨v,hv.trans hy,(Function.update_of_ne dm.symm _ _).trans ((Function.update_self ..).trans bits),
    Function.update_self ..,Exec.seq writeMask writeDir⟩

noncomputable def parentCoefficientTime (j w H : ℕ) :=
  let C := 48*H*H+152*H+66
  (8*(j*H)+14*H+22)+(6*w+6+(14*H+16+(prime-2)*C+C+w*(12*H+15+prime*C)))

def directoryHeaderSource (i : Fin 8) : Fin 66 := ![2,47,48,44,2,44,45,45] i

noncomputable def directoryQueueInitTime {K : ℕ} (m d w H records : ℕ) (S : Stacks (66+K) prime) : ℕ :=
  let headers := ((List.finRange 8).map fun i => 6*(S.R ((directoryHeaderSource i).castAdd K)).length+6).sum+1 +
    ((conjugationDepth m+1)*(6*(S.R ((2 : Fin 66).castAdd K)).length+6)+1)+1
  headers+(((List.finRange m).map fun j => parentCoefficientTime j.val w H).sum+1) + ((4*H+4)+((d+1)*((d+1)*(6*H+6)+1)+1)) +
    ((6*records+6)+(6*(S.R ((46 : Fin 66).castAdd K)).length+6))

/-- The counter and selector passes use linear time in batch volume, plus
the initial left stacks that the cleanup program unloads. -/
theorem maskSetup_volume_le (m w records parents tapes left V : ℕ)
    (radix : prime^(w+1) ≤ V) (count : records ≤ V) (boxes : parents ≤ records) :
    (26*prime^w+4) + ((44*records+13*(w+1)+16) + 3*((6+10*(m*m))*records+4) +
      (2*parents+2)) + (left+tapes*(2*prime^w+4)+1) ≤
      left + (140+30*(m*m)+6*tapes)*V := by
  have high := (Nat.pow_le_pow_right Networks.Shared50ModularControl.prime_prime.pos (Nat.le_succ w)).trans radix
  have atom : w+1 ≤ V := Nat.lt_two_pow_self.le.trans
    ((Nat.pow_le_pow_left Networks.Shared50ModularControl.prime_prime.two_le _).trans radix)
  have positive : 1 ≤ V := (pow_pos Networks.Shared50ModularControl.prime_prime.pos w).trans_le high
  nlinarith only [high,atom,positive,count,boxes.trans count,Nat.mul_le_mul_left (m*m) count,
    Nat.mul_le_mul_left tapes high,Nat.mul_le_mul_left tapes positive]

/-- Express the exceptional record count as a fraction of the payload volume
while keeping the ordinary per-record charge separate. -/
private theorem exceptionalBatchCost_le (steps overhead records baseline labels rate N : ℕ)
    (bill : steps ≤ overhead + (records*(baseline+6)+2 + (labels*records/prime)*(rate*N))) :
    (steps : ℝ) ≤ overhead + records*(baseline+6) + 2 +
      ((labels : ℝ)/prime)*rate*(records*N) := by
  have frequency : ((labels*records/prime : ℕ) : ℝ) * prime ≤ (labels : ℝ)*records := by
    exact_mod_cast Nat.div_mul_le_self (labels*records) prime
  have weighted := mul_le_mul_of_nonneg_right frequency (show 0 ≤ (rate : ℝ)*N by positivity)
  have pos : (0 : ℝ) < prime := by exact_mod_cast Networks.Shared50ModularControl.prime_prime.pos
  have rare : ((labels*records/prime : ℕ) : ℝ)*(rate*N) ≤ ((labels : ℝ)/prime)*rate*(records*N) := by
    apply (mul_le_mul_iff_of_pos_right pos).mp
    field_simp
    nlinarith only [weighted]
  have total : (steps : ℝ) ≤ overhead + (records*(baseline+6)+2 + ((labels*records/prime : ℕ) : ℝ)*(rate*N)) := by
    exact_mod_cast bill
  linarith

/-- Per-symbol charge of the pivot setup and the packed coordinate loop at
the leaf exponent, before the record loader and its cleanup. -/
noncomputable def directoryCoordinateRateAt [M8.Machine.Net] (m d tapes push entry leave : ℕ) (power : ℝ) : ℝ :=
  let scans := (1000*(prime+1)+16*(d-1))*(2*(prime.size+1)^2)
  let frame := 1800*(entry+5)+200*(leave+5)+15
  (pivotSetupTime m d 1 1 * (2*(prime.size+1)^2) : ℕ) +
    d*(weightedLeafRate tapes push power + (scans+frame : ℕ)) + 1

noncomputable def directoryCoordinateRate [M8.Machine.Net] (m d w tapes push entry leave : ℕ) : ℝ :=
  directoryCoordinateRateAt m d tapes push entry leave (((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau)

private theorem directoryCoordinateTime_le [M8.Machine.Net] (m d w N tapes push entry leave : ℕ)
    (radix : prime^(w+1) ≤ N) :
    ((pivotSetupTime m d w (prime^(w+1)).size + packedCoordinatesTime d N w tapes push entry leave : ℕ) : ℝ) ≤
      directoryCoordinateRateAt m d tapes push entry leave (((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau)*N := by
  let M := prime^(w+1)
  let scans := (1000*(prime+1)+16*(d-1))*(2*(prime.size+1)^2)
  let frame := 1800*(entry+5)+200*(leave+5)+15
  let pivot := pivotSetupTime m d 1 1*(2*(prime.size+1)^2)
  have init := (pivotSetupTime_radix_le m d d w le_rfl).trans (Nat.mul_le_mul_left pivot radix)
  have leaf := weightedLeafCost_le N (w+1) tapes push (by rw [max_eq_right (Nat.succ_pos w)])
  have pos : 1 ≤ N := (pow_pos Networks.Shared50ModularControl.prime_prime.pos (w+1)).trans_le radix
  change ((pivotSetupTime m d w M.size + (d*(weightedLeafCost N (w+1) tapes push + scans*M + frame*N)+1) : ℕ) : ℝ) ≤
    ((pivot : ℝ)+d*(weightedLeafRate tapes push (((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau)+(scans+frame : ℕ))+1)*N
  push_cast
  have a : (pivotSetupTime m d w M.size : ℝ) ≤ (pivot : ℝ)*N := by exact_mod_cast init
  have b : (scans : ℝ)*M ≤ (scans : ℝ)*N := by exact_mod_cast Nat.mul_le_mul_left scans radix
  have one : (1 : ℝ) ≤ N := by exact_mod_cast pos
  push_cast at leaf
  nlinarith only [a,mul_le_mul_of_nonneg_left (add_le_add leaf b) (Nat.cast_nonneg (α := ℝ) d),one]

noncomputable def directoryQueueInitRate (m d : ℕ) :=
  96 + 12*(conjugationDepth m+1) +
    m*(parentCoefficientTime m 1 1*(2*(prime.size+1)^2)) +
    (d+1)*((d+1)*12+1)+40

/-- Initialization copies the entire directory and projector tapes, including
their tails. The bound uses the lengths of the actual caller tapes. -/
theorem directoryQueueInitTime_binary_le {K : ℕ} (m d w records V : ℕ) (S : Stacks (66+K) prime)
    (radix : prime^(w+1) ≤ V) (count : records ≤ V)
    (directory : (S.R ((46 : Fin 66).castAdd K)).length ≤ V)
    (headers : ∀ j : Fin 66, j.val ∈ ([2,47,48,44,45] : List ℕ) → (S.R (j.castAdd K)).length ≤ V) :
    directoryQueueInitTime m d w (prime^(w+1)).size records S ≤ directoryQueueInitRate m d*V := by
  let M := prime^(w+1)
  let H := M.size
  have positive : 1 ≤ V := (pow_pos Networks.Shared50ModularControl.prime_prime.pos (w+1)).trans_le radix
  have digits : H ≤ V := (Nat.size_le.mpr Nat.lt_two_pow_self).trans radix
  let rate := parentCoefficientTime m 1 1*(2*(prime.size+1)^2)
  have field := prefixSetup_volume_le w 0
  simp only [Nat.zero_add,pow_zero,pow_one] at field
  have coeff (j : Fin m) : parentCoefficientTime j.val w H ≤ rate*V := by
    have uniform : parentCoefficientTime m w H ≤ parentCoefficientTime m 1 1*((w+1)*(H+1)^2) := by
      unfold parentCoefficientTime
      generalize prime = p
      generalize p-2 = k
      ring_nf
      omega
    have mono : parentCoefficientTime j.val w H ≤ parentCoefficientTime m w H := by
      dsimp only [parentCoefficientTime]
      gcongr <;> exact j.isLt.le
    refine (mono.trans uniform).trans ?_
    dsimp only [rate]
    rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left
    exact ((Nat.mul_le_mul_right _ (Nat.le_add_right (w+1) 1)).trans field).trans (Nat.mul_le_mul_left _ radix)
  have total := List.sum_le_sum (fun (j : Fin m) (_ : j ∈ List.finRange m) => coeff j)
  let src := directoryHeaderSource
  have member : ∀ i : Fin 8, (src i).val ∈ ([2,47,48,44,45] : List ℕ) := by decide
  have copies := List.sum_le_sum (fun (i : Fin 8) (_ : i ∈ List.finRange 8) =>
    Nat.add_le_add_right (Nat.mul_le_mul_left 6 (headers (src i) (member i))) 6)
  simp only [List.map_const',List.length_finRange,List.sum_replicate_nat] at copies total
  let depth := conjugationDepth m+1
  have modulus := headers 2 (by decide)
  simp only [directoryQueueInitTime,directoryQueueInitRate]
  have frames := Nat.mul_le_mul_left depth (Nat.add_le_add (Nat.mul_le_mul_left 6 modulus) (Nat.mul_le_mul_left 6 positive))
  have padding := Nat.mul_le_mul_left (d+1) (Nat.add_le_add (Nat.mul_le_mul_left (d+1)
    (Nat.add_le_add (Nat.mul_le_mul_left 6 digits) (Nat.mul_le_mul_left 6 positive))) positive)
  dsimp only [depth,H,M,rate,src] at copies total frames padding digits
  nlinarith only [copies,total,frames,padding,digits,directory,count,positive]

noncomputable def directoryMatrixQueueTime (m d w H records prefixWidth : ℕ) : ℕ :=
  let active := LabelStock.live m (w+1) 1
  let num := fun i j : Fin m => numerator (matrixInput false) (matrixInput true) i j
  let numTime := Finset.univ.sup fun ij : Fin m × Fin m => time H (readTime H) (num ij.1 ij.2)
  let liveCost := liveRecordCost m (d+1) w H prefixWidth numTime (time H (readTime H) (determinant (matrixInput (m := m) false)))
  let size := (d+1)*(d+1)*H
  (List.range records).countP active*(liveCost+4*size) +
    (List.range records).countP (fun j => !active j)*(10*size+6) +
    records*(4*prefixWidth+4+(m*m*(4*(w+1)+4)+1)+6)+4

noncomputable def directoryMatrixRate (m d : ℕ) :=
  matrixBuildCost m (d+1) 1 1 * (2*(prime.size+1)^2) + 14*((d+1)*(d+1)) + 8*(m*m) + 17

/-- At binary precision the matrix arithmetic and the directory counters cost
a constant times the radix per record. The copied prefix is charged by length. -/
theorem directoryMatrixQueueTime_binary_le (m d w records width : ℕ) :
    let M := prime^(w+1)
    directoryMatrixQueueTime m d w M.size records width ≤
      records*((12*m*m+4)*width + directoryMatrixRate m d*M)+4 := by
  intro M
  let H := M.size
  let size := (d+1)*(d+1)*H
  let active := LabelStock.live m (w+1) 1
  let base := matrixBuildCost m (d+1) 1 1 * (2*(prime.size+1)^2)
  have build : matrixBuildCost m (d+1) w H ≤ base*M := by
    refine (matrixBuildCost_le ..).trans ?_
    dsimp only [base]
    rw [Nat.mul_assoc,Nat.mul_assoc]
    apply Nat.mul_le_mul_left
    have bits := prefixSetup_volume_le w 0
    simp only [Nat.zero_add,pow_one,pow_zero] at bits
    exact (Nat.mul_le_mul_right _ (Nat.le_add_right (w+1) 1)).trans bits
  have hH : H ≤ M := Nat.size_le.mpr Nat.lt_two_pow_self
  have hw : w+1 ≤ M := Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_left Networks.Shared50ModularControl.prime_prime.two_le _)
  have pos : 1 ≤ M := pow_pos Networks.Shared50ModularControl.prime_prime.pos _
  have queue :
      directoryMatrixQueueTime m d w H records width =
        (List.range records).countP active*(matrixBuildCost m (d+1) w H + 12*m*m*width + 4*size) +
        (List.range records).countP (fun j => !active j)*(10*size+6) +
        records*(4*width+4+(m*m*(4*(w+1)+4)+1)+6)+4 := by
    unfold directoryMatrixQueueTime matrixBuildCost liveRecordCost
    dsimp only [active,size]
    ring
  have count (f : ℕ → Bool) : (List.range records).countP f ≤ records := by
    simpa using (List.countP_le_length (l := List.range records) (p := f))
  rw [queue]
  have combined := Nat.add_le_add
    (Nat.mul_le_mul (count active) (Nat.add_le_add_right (Nat.add_le_add_right build (12*m*m*width)) (4*size)))
    (Nat.mul_le_mul_right (10*size+6) (count (fun j => !active j)))
  refine (Nat.add_le_add_right (Nat.add_le_add_right combined _) 4).trans ?_
  rw [← Nat.mul_add,← Nat.mul_add]
  apply Nat.add_le_add_right
  apply Nat.mul_le_mul_left
  dsimp only [size,directoryMatrixRate,base] at *
  nlinarith only [Nat.mul_le_mul_left ((d+1)*(d+1)) hH, Nat.mul_le_mul_left (m*m) hw,
    Nat.mul_le_mul_left (m*m) pos,pos]

/-- The queue consumes its mask and a prefix of its directory. With the archive
excluded, clearing the remaining tapes costs at most their pre-writer charge. -/
private theorem queue_cleanup_le {T A : ℕ} (S : Stacks T A) (mask dir archive : Fin T)
    (tail words : List (Fin (A+4))) (work : List (Fin T)) (off : archive ∉ work)
    (length : tail.length ≤ (S.R dir).length) :
    let D := queueResult S mask dir archive tail words
    (work.map fun i => 4*(D.L i).length+2*(D.R i).length+4).sum ≤
      (work.map fun i => 4*(S.L i).length+2*(S.R i).length+4).sum := by
  intro D
  apply List.sum_le_sum
  intro i hi
  have away : i ≠ archive := fun h => off (h ▸ hi)
  have right : (D.R i).length ≤ (S.R i).length := by
    simp only [D,queueResult,Function.update_of_ne away]
    by_cases hd : i = dir
    · subst i; simpa using length
    · rw [Function.update_of_ne hd]
      by_cases hm : i = mask
      · subst i; simp
      · rw [Function.update_of_ne hm]
  change 4*(S.L i).length+2*(D.R i).length+4 ≤ _
  omega

/-- Initialize the physical writer headers, formula frames, and both coefficient banks. -/
theorem directoryQueueSetup_exec [M8.Machine.Net] {K d Q m H w records : ℕ} {P U : Type}
    (room : Record.size d+(rowSwapBlock.tapes+35+2) ≤ K)
    (fits : (36+2*m+1+(conjugationDepth m+1)*13)+3 ≤ K) (body : P → Pr P (66+K) Q prime U)
    (parent inv : Fin m → ZMod (prime^(w+1))) (reciprocal : ∀ j, parent j * inv j = 1)
    (hm : prime^(w+1) < 2^H) (u : HS (66+K) Q prime U) (S : Stacks (66+K) prime) :
    let ports := directoryParentPorts room fits
    let readSlots : Fin 7 ↪ Fin 19 := ⟨![1,4,18,14,2,3,5],by decide⟩
    let pivot := fun j => (Fin.castLEEmb (by decide : 16 ≤ 19)).trans (ports j)
    let program := fun j => (readMatrixWord j.val (readSlots.trans (ports j))).seq
      (reusablePivotInverse prime (pivot j) (ports j 16) (ports j 17))
    let C := 48*H*H+152*H+66
    let price := fun j : Fin m => (8*(j.val*H)+14*H+22)+(6*w+6+(14*H+16+(prime-2)*C+C+w*(12*H+15+prime*C)))
    let bank := directoryQueueBank room fits
    let src := fun i : Fin 8 => ((![2,47,48,44,2,44,45,45] i : Fin 66)).castAdd K
    let dst := (directoryQueueHeaderSlots.trans (Fin.castLEEmb (by omega))).trans bank
    let tmp := bank ⟨4,by omega⟩
    let aux := bank ⟨6,by omega⟩
    let pool := QueueLayout.block (n := (conjugationDepth m+1)*13) (36+2*m+1) (by omega) bank
    let srcMod := (2 : Fin 66).castAdd K
    let digits := dst 7
    let headers := ((Record.copyLeafHeaders src dst tmp aux (List.finRange 8)).seq
      (initFrames pool srcMod (conjugationDepth m+1))).seq (.act (.push (.rt digits) (fun _ => Node.tick) .done))
    let headerTime := ((List.finRange 8).map fun i => 6*(S.R (src i)).length+6).sum+1 +
      ((conjugationDepth m+1)*(6*(S.R srcMod).length+6)+1)+1
    let base := 36+2*m+1+(conjugationDepth m+1)*13
    let zero := bank ⟨9,by omega⟩
    let seed := bank ⟨base+1,by omega⟩
    let saved := bank ⟨base+2,by omega⟩
    let pad := (Node.umulSym 1 (bitSymbol false) (dst 0) zero tmp).seq
      (identitySeed (d+1) zero (dst 3) seed tmp saved)
    let identityWord := matrixWords prime H (1 : Matrix (Fin (d+1)) (Fin (d+1)) (ZMod (prime^(w+1))))
    let padded := fun (F : Stacks (66+K) prime) =>
      {F with R := Function.update (Function.update F.R zero (binSyms H 0)) seed identityWord}
    let mask := bank ⟨base,by omega⟩
    let dir := bank ⟨2,by omega⟩
    let live := (57 : Fin 66).castAdd K
    let source := (46 : Fin 66).castAdd K
    let copies := (bcopy live mask tmp saved).seq (bcopy source dir tmp saved)
    let inputs := fun (F : Stacks (66+K) prime) =>
      {F with R := Function.update (Function.update F.R mask (S.R live)) dir (S.R source)}
    S.R live = (List.range records).map (fun j => bitSymbol (LabelStock.live m (w+1) 1 j)) →
    (∀ i, S.R (bank i) = []) →
    S.R ((55 : Fin 66).castAdd K) = (List.ofFn fun i => binSyms H (parent i).val).flatten →
    S.R srcMod = binSyms H (prime^(w+1)) →
    S.R ((44 : Fin 66).castAdd K) = binSyms H (1 : ZMod (prime^(w+1))).val →
    (S.R ((45 : Fin 66).castAdd K)).length = w →
    ∃ z F n, z.user = u.user ∧ n ≤ headerTime+(((List.finRange m).map price).sum+1) +
        ((4*H+4)+((d+1)*((d+1)*(6*H+6)+1)+1)) + ((6*records+6)+(6*(S.R source).length+6)) ∧
      Exec body (((headers.seq (Prog.seqList ((List.finRange m).map program))).seq pad).seq copies) (mk u S) n (mk z (inputs (padded F))) ∧
      F.L = S.L ∧ (∀ i, F.R (dst i) = if i = 7 then Node.tick :: S.R (src i) else S.R (src i)) ∧
      (∀ j : Fin 66, F.R (j.castAdd K) = S.R (j.castAdd K)) ∧
      (∀ k ≤ conjugationDepth m, F.R (frame pool k 2) = S.R srcMod) ∧
      (∀ k ≤ conjugationDepth m, ∀ i : Fin 13, i ≠ 2 → F.R (frame pool k i) = []) ∧
      (∀ j, F.R (ports j 14) = binSyms H (parent j).val ∧ F.R (ports j 0) = binSyms H (inv j).val) ∧
      (∀ k, k ≠ dir → k ≠ mask → k ≠ seed → k ≠ zero → (inputs (padded F)).R k = F.R k) ∧
      (inputs (padded F)).R dir = S.R source ∧ (inputs (padded F)).R mask = S.R live ∧
      (inputs (padded F)).R seed = identityWord ∧ (inputs (padded F)).R zero = binSyms H 0 ∧
      (∀ i, (i.val < 36 ∧ i.val ∉ ([1,2,8,9,12,16,17,22,33,34] : List ℕ)) ∨
          i.val = 36+2*m ∨ i.val = base+2 → (inputs (padded F)).R (bank i) = []) ∧
      (∀ (e : (Fin m ⊕ Fin m) ≃ Fin (d+1)), ∃ writer : Pr P (66+K) Q prime U,
        ∀ (proj : Matrix (Fin m) (Fin m) ℚ) (prefixes : ℕ → List (Fin (prime+4))) (tail : List (Fin (prime+4))),
        (∃ suffix, S.R ((48 : Fin 66).castAdd K) = matrixWords prime H (reduce (prime^(w+1)) proj) ++ suffix) →
        (∀ j < records, (S.R ((47 : Fin 66).castAdd K)).length = (prefixes j).length) →
        S.R source = (List.range records).flatMap (LabelDirectory.entry prefixes m (w+1)) ++ tail →
        let active := LabelStock.live m (w+1) 1
        let matrix := projectorResidual e (reduce (prime^(w+1)) proj) parent inv
        let words := (List.range records).flatMap fun j => if active j then
          matrixWords prime H (matrix (physicalLabel m (w+1) j)) else identityWord
        let num := fun i j : Fin m => numerator (matrixInput false) (matrixInput true) i j
        let numTime := Finset.univ.sup fun ij : Fin m × Fin m => time H (readTime H) (num ij.1 ij.2)
        let prefixWidth := (S.R ((47 : Fin 66).castAdd K)).length
        let liveCost := liveRecordCost m (d+1) w H prefixWidth numTime (time H (readTime H) (determinant (matrixInput (m := m) false)))
        let size := (d+1)*(d+1)*H
        let result := queueResult (inputs (padded F)) mask dir (directoryMatrixTape room) tail words
        let work := (List.finRange (66+K)).filter fun i => decide (58 ≤ i.val ∧ i ≠ directoryMatrixTape room)
        let cleanup := (work.map fun i => 4*(result.L i).length+2*(result.R i).length+4).sum+1
        let clean := {result with L := fun i => if i ∈ work then [] else result.L i,
                                  R := fun i => if i ∈ work then [] else result.R i}
        let queueTime := (List.range records).countP active*(liveCost+4*size) +
          (List.range records).countP (fun j => !active j)*(10*size+6) +
          records*(4*prefixWidth+4+(m*m*(4*(w+1)+4)+1)+6)+4
        let setup := (((headers.seq (Prog.seqList ((List.finRange m).map program))).seq pad).seq copies)
        ∃ y steps, y.user = u.user ∧ steps ≤ n + queueTime + cleanup ∧
          (∀ c, mnProgPush setup ≤ c → (∀ f, mnProgPush (body f) ≤ c) →
            steps ≤ n + queueTime + ((work.map fun i => 4*(S.L i).length+2*(S.R i).length+4).sum+1 +
              work.length*(6*(c*n)))) ∧
          Exec body (((((headers.seq (Prog.seqList ((List.finRange m).map program))).seq pad).seq copies).seq writer).seq
            (clearWorkTapes work)) (mk u S) steps (mk y clean) ∧
          clean.R (directoryMatrixTape room) = words ∧
          (∀ i : Fin 66, i.val < 58 → clean.L (i.castAdd K) = S.L (i.castAdd K) ∧
            clean.R (i.castAdd K) = S.R (i.castAdd K)) ∧
          (∀ i, 58 ≤ i.val → i ≠ directoryMatrixTape room → clean.L i = [] ∧ clean.R i = [])) ∧
      ∀ k, (∀ i, dst i ≠ k) → (∀ i, k ≠ pool i) →
        (∀ j, k ≠ ports j 14 ∧ k ≠ ports j 0) → F.R k = S.R k := by
  intro ports readSlots pivot program C price bank src dst tmp aux pool srcMod digits headers headerTime base zero seed saved pad identityWord padded mask dir live source copies inputs bits blank
    packed modulus unit clock
  obtain ⟨y,B,user,run,left,values,caller,moduli,scratch,keep⟩ := directoryQueueHeaders_exec room fits body u S
    (blank _) (blank _) (fun i => blank _) (fun i => blank _)
  have free (i : Fin ((36+2*m+1+(conjugationDepth m+1)*13)+3)) (h : i.val = 35 ∨ (19 ≤ i.val ∧ i.val < 31 ∧ i.val ≠ 22) ∨ (36 ≤ i.val ∧ i.val < 36+2*m)) :
      B.R (bank i) = [] := by
    apply (keep _ ?_ ?_).trans (blank i)
    · intro j eq
      have val := congrArg Fin.val (bank.injective eq)
      change (directoryQueueHeaderSlots j).val = i.val at val
      have bounds : ∀ k, (directoryQueueHeaderSlots k).val ≤ 17 ∨
        (directoryQueueHeaderSlots k).val = 22 ∨ (directoryQueueHeaderSlots k).val = 33 ∨
        (directoryQueueHeaderSlots k).val = 34 := by decide
      have := bounds j
      omega
    · intro k eq
      have val := congrArg Fin.val (bank.injective eq)
      change i.val = 36+2*m+1+k.val at val
      omega
  obtain ⟨z,F,n,hz,hn,load,leftF,_,_,coeff,rest⟩ := directoryParentBank_exec room fits body parent inv reciprocal hm y B
    ((caller 55).trans packed) ((values 4).trans modulus) ((values 5).trans unit)
    ((congrArg List.length (values 6)).trans clock) free
  have outside (i : Fin ((36+2*m+1+(conjugationDepth m+1)*13)+3)) (range : i.val < 36 ∨ 36+2*m ≤ i.val) (j : Fin m) :
      bank i ≠ ports j 14 ∧ bank i ≠ ports j 0 := by
    constructor <;> intro eq <;> have val := congrArg Fin.val (bank.injective eq)
    · change i.val = 36+j.val at val; omega
    · change i.val = 36+m+j.val at val; omega
  have poolKeep (k) : F.R (pool k) = B.R (pool k) :=
    rest _ (outside _ (Or.inr (by change 36+2*m ≤ 36+2*m+1+k.val; omega)))
  have header (i) := (rest _ (outside _ (Or.inl (Nat.lt_trans (directoryQueueHeaderSlots i).isLt (by decide))))).trans (values i)
  have unused (i : Fin (base+3)) (whereAt : i.val = 2 ∨ i.val = 4 ∨ i.val = 9 ∨ base ≤ i.val) : F.R (bank i) = [] := by
    have large : 36+2*m ≤ base := by dsimp [base]; omega
    apply (rest _ (outside _ (by omega))).trans
    apply (keep _ ?_ ?_).trans (blank i)
    · intro j eq
      have val := congrArg Fin.val (bank.injective eq)
      change (directoryQueueHeaderSlots j).val = i.val at val
      have off : ∀ k, (directoryQueueHeaderSlots k).val ≠ 2 ∧ (directoryQueueHeaderSlots k).val ≠ 4 ∧ (directoryQueueHeaderSlots k).val ≠ 9 := by decide
      have := off j
      have := (directoryQueueHeaderSlots j).isLt
      omega
    · intro k eq
      have val := congrArg Fin.val (bank.injective eq)
      change i.val = 36+2*m+1+k.val at val
      have := k.isLt
      dsimp [base] at whereAt
      omega
  obtain ⟨finish,l,hu,hl,write⟩ := directoryQueuePadding_exec (w := w) room fits body z F
    ((congrArg List.length ((header 0).trans modulus)).trans (length_binSyms ..)) ((header 3).trans unit)
    (unused _ (by simp [zero])) (unused _ (Or.inr (Or.inr (Or.inr (Nat.le_succ _)))))
    (unused _ (by simp [tmp])) (unused _ (Or.inr (Or.inr (Or.inr (Nat.le_add_right ..)))))
  have callerF (i : Fin 66) := (rest (i.castAdd K) (fun j => ⟨(directoryQueueBank_caller room fits _ i).symm,
    (directoryQueueBank_caller room fits _ i).symm⟩)).trans (caller i)
  have callerPad (i : Fin 66) : (padded F).R (i.castAdd K) = S.R (i.castAdd K) :=
    (Function.update_of_ne (directoryQueueBank_caller room fits _ i).symm _ _).trans
      ((Function.update_of_ne (directoryQueueBank_caller room fits _ i).symm _ _).trans (callerF i))
  have padFree (i : Fin (base+3)) (h : i.val = 2 ∨ i.val = 4 ∨ i.val = base ∨ i.val = base+2) :
      (padded F).R (bank i) = [] := by
    have large : 35 < base := by dsimp [base]; omega
    have a : bank i ≠ seed := bank.injective.ne (by intro eq; have v := congrArg Fin.val eq; change i.val = base+1 at v; omega)
    have b : bank i ≠ zero := bank.injective.ne (by intro eq; have v := congrArg Fin.val eq; change i.val = 9 at v; omega)
    exact (Function.update_of_ne a _ _).trans ((Function.update_of_ne b _ _).trans (unused i (by omega)))
  obtain ⟨endUser,he,_,_,copyRun⟩ := directoryQueueInputs_exec room fits body finish (padded F)
    ((callerPad 57).trans bits) (padFree _ (Or.inr (Or.inr (Or.inl rfl)))) (padFree _ (Or.inl rfl))
    (padFree _ (Or.inr (Or.inl rfl))) (padFree _ (Or.inr (Or.inr (Or.inr rfl))))
  change Exec body copies _ _ (mk endUser {padded F with R := Function.update (Function.update (padded F).R mask ((padded F).R live)) dir ((padded F).R source)}) at copyRun
  rw [show (padded F).R live = S.R live from callerPad 57,show (padded F).R source = S.R source from callerPad 46] at copyRun
  have finalKeep (k) (hd : k ≠ dir) (hm : k ≠ mask) (hs : k ≠ seed) (hz : k ≠ zero) :
      (inputs (padded F)).R k = F.R k :=
    (Function.update_of_ne hd _ _).trans ((Function.update_of_ne hm _ _).trans
      ((Function.update_of_ne hs _ _).trans (Function.update_of_ne hz _ _)))
  have large : 35 < base := by dsimp [base]; omega
  have ne (i j : Fin (base+3)) (h : i.val ≠ j.val) : bank i ≠ bank j := bank.injective.ne (fun eq => h (congrArg Fin.val eq))
  have maskWord : (inputs (padded F)).R mask = S.R live :=
    (Function.update_of_ne (ne _ _ (by change base ≠ 2; omega)) _ _).trans (Function.update_self ..)
  have seedWord : (inputs (padded F)).R seed = identityWord :=
    (Function.update_of_ne (ne _ _ (by change base+1 ≠ 2; omega)) _ _).trans
      ((Function.update_of_ne (ne _ _ (by change base+1 ≠ base; omega)) _ _).trans (Function.update_self ..))
  have zeroWord : (inputs (padded F)).R zero = binSyms H 0 :=
    (Function.update_of_ne (ne _ _ (by decide : 9 ≠ 2)) _ _).trans ((Function.update_of_ne (ne _ _ (by change 9 ≠ base; omega)) _ _).trans
      ((Function.update_of_ne (ne _ _ (by change 9 ≠ base+1; omega)) _ _).trans (Function.update_self ..)))
  have writerBlank (i : Fin (base+3)) (h : (i.val < 36 ∧ i.val ∉ ([1,2,8,9,12,16,17,22,33,34] : List ℕ)) ∨
      i.val = 36+2*m ∨ i.val = base+2) : (inputs (padded F)).R (bank i) = [] := by
    have depthPositive : 0 < (conjugationDepth m+1)*13 := by omega
    have hi : (i.val < 36 ∨ 36+2*m ≤ i.val) ∧ i.val ≠ 2 ∧ i.val ≠ 9 ∧ i.val ≠ base ∧ i.val ≠ base+1 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at h
      dsimp only [base] at *
      omega
    have distinct (k : Fin (base+3)) (ne : i.val ≠ k.val) := bank.injective.ne (fun eq => ne (congrArg Fin.val eq))
    have restored := finalKeep (bank i) (distinct _ hi.2.1) (distinct _ hi.2.2.2.1)
      (distinct _ hi.2.2.2.2) (distinct _ hi.2.2.1)
    apply restored.trans ((rest _ (outside _ hi.1)).trans ((keep _ ?_ ?_).trans (blank i)))
    · intro j eq
      have val := congrArg Fin.val (bank.injective eq)
      change (directoryQueueHeaderSlots j).val = i.val at val
      have mem : ∀ k, (directoryQueueHeaderSlots k).val ∈ ([1,2,8,9,12,16,17,22,33,34] : List ℕ) := by decide
      have small := (directoryQueueHeaderSlots j).isLt
      rcases h with low | h
      · exact low.2 (val ▸ mem j)
      · dsimp only [base] at h
        omega
    · intro j eq
      have val := congrArg Fin.val (bank.injective eq)
      change i.val = 36+2*m+1+j.val at val
      have := j.isLt
      dsimp only [base] at h
      omega
  refine ⟨endUser,F,_,he.trans (hu.trans (hz.trans user)),Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add_left hn _) hl) _,
    Exec.seq (Exec.seq (Exec.seq run load) write) copyRun,leftF.trans left,
    header,
    fun i => (rest _ (fun j => ⟨(directoryQueueBank_caller room fits _ i).symm,(directoryQueueBank_caller room fits _ i).symm⟩)).trans (caller i),
    fun k hk => (poolKeep _).trans (moduli k hk),fun k hk i ne => (poolKeep _).trans (scratch k hk i ne),
    coeff,finalKeep,Function.update_self ..,maskWord,seedWord,zeroWord,writerBlank,?_,fun k hd hp hw => (rest k hw).trans (keep k hd hp)⟩

  intro e
  let D := inputs (padded F)
  have same (i : Fin (base+3)) (ok : i.val ≠ 2 ∧ i.val ≠ base ∧ i.val ≠ base+1 ∧ i.val ≠ 9) :
      D.R (bank i) = F.R (bank i) :=
    finalKeep _ (ne _ _ ok.1) (ne _ _ ok.2.1) (ne _ _ ok.2.2.1) (ne _ _ ok.2.2.2)
  have headValue (j : Fin 8) : D.R (dst j) = if j = 7 then Node.tick :: S.R (src j) else S.R (src j) := by
    apply (same _ ?_).trans (header j)
    have off : ∀ k, (directoryQueueHeaderSlots k).val ≠ 2 ∧ (directoryQueueHeaderSlots k).val ≠ 9 := by decide
    let v := (directoryQueueHeaderSlots j).val
    change v ≠ 2 ∧ v ≠ base ∧ v ≠ base+1 ∧ v ≠ 9
    have hv : v < 35 := (directoryQueueHeaderSlots j).isLt
    exact ⟨(off j).1,by omega,by omega,(off j).2⟩
  have stablePool (j) : D.R (pool j) = F.R (pool j) := by
    apply same
    change 36+2*m+1+j.val ≠ 2 ∧ 36+2*m+1+j.val ≠ base ∧ 36+2*m+1+j.val ≠ base+1 ∧ 36+2*m+1+j.val ≠ 9
    have := j.isLt
    dsimp [base]; omega
  have coeffRow (j : Fin m) : D.R (ports j 14) = binSyms H (parent j).val := by
    apply (same _ ?_).trans (coeff j).1
    change 36+j.val ≠ 2 ∧ 36+j.val ≠ base ∧ 36+j.val ≠ base+1 ∧ 36+j.val ≠ 9
    dsimp [base]; omega
  have coeffCol (j : Fin m) : D.R (ports j 0) = binSyms H (inv j).val := by
    apply (same _ ?_).trans (coeff j).2
    change 36+m+j.val ≠ 2 ∧ 36+m+j.val ≠ base ∧ 36+m+j.val ≠ base+1 ∧ 36+m+j.val ≠ 9
    dsimp [base]; omega
  refine ⟨?_, ?_⟩
  swap
  intro proj prefixes tail projector widths directory active matrix words num numTime prefixWidth liveCost size result work cleanup clean queueTime setup
  have prefixEq : (D.R (dst 1)).length = prefixWidth := congrArg List.length (headValue 1)
  obtain ⟨_,y,t,hy,ht,generate⟩ := physicalResidualQueue_exec body w records (reduce (prime^(w+1)) proj) H hm bank
    prefixes tail e parent inv endUser D seedWord (writerBlank _ (Or.inr (Or.inr rfl)))
    ⟨writerBlank _ (Or.inl (by change 31 < 36 ∧ 31 ∉ ([1,2,8,9,12,16,17,22,33,34] : List ℕ); decide)),fun i j => by
      constructor
      · convert coeffRow i using 2 <;> apply congrArg bank <;> apply Fin.ext <;> exact Nat.zero_add _
      · convert coeffCol j using 2 <;> apply congrArg bank <;> apply Fin.ext <;> exact Nat.zero_add _⟩
    ⟨(by intro i hi; apply writerBlank _ (Or.inl ?_)
         change 0+(0+i.val) < 36 ∧ 0+(0+i.val) ∉ _
         simp only [Nat.zero_add]
         exact (by decide : ∀ x : Fin 18, x ∈ [0,3,4,5,6,7,11,14,15] → x.val < 36 ∧
           x.val ∉ ([1,2,8,9,12,16,17,22,33,34] : List ℕ)) i hi),
      (congrArg List.length ((headValue 0).trans modulus)).trans (length_binSyms ..),
      zeroWord,writerBlank _ (Or.inl (by change 10 < 36 ∧ 10 ∉ ([1,2,8,9,12,16,17,22,33,34] : List ℕ); decide)),(congrArg List.length (headValue 6)).trans clock,
      writerBlank _ (Or.inl (by change 35 < 36 ∧ 35 ∉ ([1,2,8,9,12,16,17,22,33,34] : List ℕ); decide)),writerBlank _ (Or.inl (by change 32 < 36 ∧ 32 ∉ ([1,2,8,9,12,16,17,22,33,34] : List ℕ); decide)),
      (headValue 5).trans unit,(headValue 4).trans modulus,
      (by intro i hi lt; apply writerBlank _ (Or.inl ?_)
          change 0+(18+i.val) < 36 ∧ 0+(18+i.val) ∉ _
          simp only [Nat.zero_add]
          have h : i.val ≠ 4 := fun eq => hi (Fin.ext eq)
          change i.val < 13 at lt
          simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]; omega),
      fun k hk => by
        convert (stablePool _).trans ((poolKeep _).trans ((moduli k hk).trans modulus)) using 2
        apply congrArg bank; apply Fin.ext; exact Nat.zero_add _,
      fun k hk i off => by
        convert (stablePool _).trans ((poolKeep _).trans (scratch k hk i off)) using 2
        apply congrArg bank; apply Fin.ext; exact Nat.zero_add _,
      (by obtain ⟨suffix,h⟩ := projector; exact ⟨suffix,(headValue 2).trans h⟩),(headValue 3).trans unit⟩
    (fun j hj => prefixEq.trans (widths j hj))
    (by change (D.R (dst 7)).length = w+1; rw [headValue]; exact congrArg Nat.succ clock)
    (writerBlank _ (Or.inl (by change 4 < 36 ∧ 4 ∉ ([1,2,8,9,12,16,17,22,33,34] : List ℕ); decide))) (writerBlank _ (Or.inr (Or.inl (Nat.zero_add _))))
    ((Function.update_self ..).trans directory) (writerBlank _ (Or.inl (by change 13 < 36 ∧ 13 ∉ ([1,2,8,9,12,16,17,22,33,34] : List ℕ); decide))) (maskWord.trans bits)
  obtain ⟨finish,userFinish,clear⟩ := clearWorkTapes_exec body work ((List.nodup_finRange _).filter _) y result
  have queueBound : t ≤ queueTime := by
    change t ≤ (List.range records).countP active*(liveRecordCost m (d+1) w H (D.R (dst 1)).length numTime _+4*size) +
      (List.range records).countP (fun j => !active j)*(10*size+6) +
      records*(4*(D.R (dst 1)).length+4+(m*m*(4*(w+1)+4)+1)+6)+4 at ht
    rw [prefixEq] at ht
    exact ht
  refine ⟨finish,headerTime+n+l+((6*records+6)+(6*(S.R source).length+6))+t+cleanup,userFinish.trans (hy.trans (he.trans (hu.trans (hz.trans user)))),Nat.add_le_add_right (Nat.add_le_add_left queueBound _) _,?_,?_,?_,?_,?_⟩
  · intro c setupPush calls
    have initialRun := Exec.seq (Exec.seq (Exec.seq run load) write) copyRun
    have growth := cleanup_cost_le work initialRun setupPush calls
    have dirLength : tail.length ≤ (D.R dir).length := by
      change tail.length ≤ (Function.update (Function.update (padded F).R mask (S.R live)) dir (S.R source) dir).length
      rw [Function.update_self,directory,List.length_append]
      omega
    have shrink := queue_cleanup_le D mask dir (directoryMatrixTape room) tail words work
      (by simp [work]) dirLength
    exact Nat.add_le_add (Nat.add_le_add_left queueBound _) ((Nat.add_le_add_right shrink 1).trans growth)
  · have archiveEq : (QueueLayout.block (n := base) 0 (by omega) bank) ⟨36+2*m,by dsimp [base]; omega⟩ =
        directoryMatrixTape room := by
      rw [← directoryQueueBank_archive room fits]
      apply congrArg bank
      apply Fin.ext
      exact Nat.zero_add _
    change Exec body _ (mk endUser D) t (mk y (queueResult D mask dir
      ((QueueLayout.block (n := base) 0 (by omega) bank) ⟨36+2*m,by dsimp [base]; omega⟩) tail words)) at generate
    have endpoint := congrArg (fun a => queueResult D mask dir a tail words) archiveEq
    change queueResult D mask dir _ tail words = result at endpoint
    rw [endpoint] at generate
    have combined := Exec.seq (Exec.seq (Exec.seq (Exec.seq (Exec.seq run load) write) copyRun) generate) clear
    exact combined
  · have off : directoryMatrixTape room ∉ work := by simp [work]
    exact (if_neg off).trans (Function.update_self ..)
  · intro i hi
    have low : (i.castAdd K) ∉ work := by simp [work,Nat.not_le_of_lt hi]
    have off (j) := (directoryQueueBank_caller room fits j i).symm
    have archiveOff : i.castAdd K ≠ directoryMatrixTape room := by
      rw [← directoryQueueBank_archive room fits]
      exact off _
    refine ⟨(if_neg low).trans (congrFun (leftF.trans left) _),(if_neg low).trans ?_⟩
    exact (Function.update_of_ne archiveOff _ _).trans ((Function.update_of_ne (off _) _ _).trans
      ((Function.update_of_ne (off _) _ _).trans ((Function.update_of_ne (off _) _ _).trans
        ((Function.update_of_ne (off _) _ _).trans (callerPad i)))))
  · intro i hi off
    have mem : i ∈ work := by simp [work,hi,off]
    exact ⟨if_pos mem,if_pos mem⟩

/-- The writer returns all caller tapes intact, including the live and exceptional
selectors. Its matrix stream is on the tape used by the classified scan. -/
theorem directoryQueue_endpoint [M8.Machine.Net] {K d r w W : ℕ}
    (room : Record.size d+(rowSwapBlock.tapes+35+2) ≤ K)
    (fits : (36+2*r+1+(conjugationDepth r+1)*13)+3 ≤ K)
    (data : ScanData r d w W) (e : (Fin r ⊕ Fin r) ≃ Fin (d+1)) (proj : Matrix (Fin r) (Fin r) ℚ)
    (parent inv : Fin r → ZMod (prime^(w+1))) (tail : List (Fin (prime+4))) (S : Stacks (66+K) prime) :
    let bank := directoryQueueBank room fits
    let dir := bank ⟨2,by omega⟩
    let mask := bank ⟨36+2*r+1+(conjugationDepth r+1)*13,by omega⟩
    let archive := bank ⟨36+2*r,by omega⟩
    let masked := {S with R := Function.update S.R mask (S.R ((57 : Fin 66).castAdd K))}
    let copied := {masked with R := Function.update masked.R dir (S.R ((46 : Fin 66).castAdd K))}
    let words := (List.range data.records).flatMap fun j =>
      if LabelStock.live r (w+1) 1 j then matrixWords prime data.H
        (projectorResidual e (reduce (prime^(w+1)) proj) parent inv (physicalLabel r (w+1) j))
      else matrixWords prime data.H (1 : Matrix (Fin (d+1)) (Fin (d+1)) (ZMod (prime^(w+1))))
    let D := queueResult copied mask dir archive tail words
    D.R (directoryMatrixTape room) = (data.physical e proj parent inv).matrices 0 ∧
      embStk (Fin.castAddEmb K (n := 66)) D = embStk (Fin.castAddEmb K (n := 66)) S := by
  intro bank dir mask archive masked copied words D
  constructor
  · rw [← directoryQueueBank_archive room fits]
    exact (Function.update_self ..).trans (data.physical_archive e proj parent inv).symm
  · refine Stacks.ext rfl rfl rfl ?_
    funext j
    have off (i) := (directoryQueueBank_caller room fits i j).symm
    change D.R (j.castAdd K) = S.R (j.castAdd K)
    exact (Function.update_of_ne (off ⟨36+2*r,by omega⟩) _ _).trans
      ((Function.update_of_ne (off ⟨2,by omega⟩) _ _).trans
        ((Function.update_of_ne (off ⟨36+2*r+1+(conjugationDepth r+1)*13,by omega⟩) _ _).trans
          ((Function.update_of_ne (off ⟨2,by omega⟩) _ _).trans
            (Function.update_of_ne (off ⟨36+2*r+1+(conjugationDepth r+1)*13,by omega⟩) _ _))))

end

open RingFormula in
noncomputable def generatedRecordTime (m w H prefixWidth headerCost tripCost : ℕ) : ℕ :=
  (((conjugationDepth m+1)*(6*H+6)+1 + (((4*H+4)+(recordConjugationTime m w H prefixWidth+(2*H+2)))+((conjugationDepth m+1)*(2*H+2)+1))) + (21*(w+1)+13)) + headerCost + tripCost + (1+(4*prefixWidth+4+(m*m*(4*(w+1)+4)+1)+1))

def descriptorHeaderCost (v : Descriptor) :=
  (((List.finRange 6).map fun i => 6*(Routines.hdr v i).length+6).sum+1)+1

theorem descriptorHeaderCost_le (v : Descriptor) (positive : v.Positive) :
    descriptorHeaderCost v ≤ 110*volume prime v := by
  let V := volume prime v
  have size (i) := RecursiveRowsNode.header_length v positive _ (Routines.hdr_headers v) i
  have each (i : Fin 6) (_ : i ∈ List.finRange 6) :
      6*(Routines.hdr v i).length+6 ≤ 12*V+6 := by have := size i; dsimp [V]; omega
  have total := List.sum_le_sum each
  simp only [List.map_const',List.length_finRange,List.sum_replicate_nat] at total
  have pos := RecursiveAffinePrepare.volume_positive Networks.Shared50ModularControl.prime_prime.two_le v positive
  unfold descriptorHeaderCost
  dsimp only [V] at total
  omega

open RingFormula in
noncomputable def generatedRecordRate (m : ℕ) :=
  matrixBuildCost m 0 1 1 * (2*(prime.size+1)^2) + 16*(conjugationDepth m+1) + 8*(m*m)+200

open RingFormula in
theorem generatedRecordTime_binary_le (m w prefixWidth tripCost : ℕ) (v : Descriptor)
    (positive : v.Positive) (radix : prime^(w+1) ≤ volume prime v) :
    let M := prime^(w+1)
    let V := volume prime v
    generatedRecordTime m w M.size prefixWidth (descriptorHeaderCost v) tripCost ≤
      tripCost + (12*m*m+4)*prefixWidth +
        generatedRecordRate m*V := by
  intro M V
  have bits : M.size ≤ V := (Nat.size_le.mpr Nat.lt_two_pow_self).trans radix
  have hw : w+1 ≤ V := Nat.lt_two_pow_self.le.trans
    ((Nat.pow_le_pow_left Networks.Shared50ModularControl.prime_prime.two_le _).trans radix)
  have pos : 0 < V := (pow_pos Networks.Shared50ModularControl.prime_prime.pos _).trans_le radix
  have gen := recordConjugationTime_binary_le m w prefixWidth
  unfold generatedRecordTime generatedRecordRate
  change recordConjugationTime m w M.size prefixWidth ≤
    12*m*m*prefixWidth + matrixBuildCost m 0 1 1 * (2*(prime.size+1)^2)*M at gen
  have headers : descriptorHeaderCost v ≤ 110*V := descriptorHeaderCost_le v positive
  have hd := Nat.le_mul_of_pos_right (conjugationDepth m+1) pos
  have hm := Nat.le_mul_of_pos_right (m*m) pos
  have cost := Nat.mul_le_mul_left (matrixBuildCost m 0 1 1 * (2*(prime.size+1)^2)) radix
  change M ≤ V at radix
  change matrixBuildCost m 0 1 1 * (2*(prime.size+1)^2)*M ≤ _*V at cost
  nlinarith only [gen,headers,hd,hm,cost,pos,bits,hw,
    Nat.mul_le_mul_left (conjugationDepth m+1) bits, Nat.mul_le_mul_left (m*m) hw]

/-- Read the modulus and the unit from the caller. The other reciprocal
registers borrow the elimination bank before elimination starts. -/
def goodRecordPivotPorts : Fin 16 ↪ Fin 82 :=
  ⟨![58,59,60,61,2,63,64,65,66,67,68,69,70,74,72,44],by decide⟩

def goodRecordCounterPorts : Fin 2 ↪ Fin 82 := ⟨![45,73],by decide⟩

/-- Six caller tapes hold the directory inputs. The remaining twelve
registers borrow blank elimination tapes until the matrix is produced. -/
def goodRecordDirectoryPorts (headers : Fin 6 ↪ Fin 58) : Fin 18 ↪ Fin 82 :=
  let order : Fin 18 ↪ Fin (6+12) := ⟨![6,0,1,7,8,9,10,11,2,17,12,13,3,14,15,16,4,5],by decide⟩
  let scratch : Fin 12 ↪ Fin 24 := ⟨![2,3,4,5,6,7,17,8,9,10,11,18],by decide⟩
  ((order.trans finSumFinEquiv.symm.toEmbedding).trans (headers.sumMap scratch)).trans finSumFinEquiv.toEmbedding

/-- Borrow a blank register for the padded zero word and release it after
the matrix writer has consumed the constant. -/
theorem withRecordZero_exec {T Q A : ℕ} {P U : Type} (body : P → Pr P T Q A U)
    (src zero tmp dst : Fin T) (ports : [src,zero,tmp].Nodup) (apart : dst ≠ zero)
    (program : Pr P T Q A U) (word : List (Fin (A+4))) (cost : ℕ)
    (u : HS T Q A U) (S : Stacks T A) (blank : S.R zero = []) (free : S.R tmp = []) :
    let H := (S.R src).length
    let B := {S with R := Function.update S.R zero (binSyms H 0)}
    (∀ v : HS T Q A U, ∃ y n, y.user = v.user ∧ n ≤ cost ∧ Exec body program (mk v B) n
      (mk y {B with R := Function.update B.R dst (word ++ B.R dst)})) →
    ∃ z t, z.user = u.user ∧ t ≤ (4*H+4)+(cost+(2*H+2)) ∧
      Exec body ((Node.umulSym 1 (bitSymbol false) src zero tmp).seq (program.seq (bclear zero)))
        (mk u S) t (mk z {S with R := Function.update S.R dst (word ++ S.R dst)}) := by
  intro H B writer
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_or] at ports
  obtain ⟨v,hv,fill⟩ := Node.umulSym_exec body 1 (bitSymbol false) ports.1.1 ports.1.2.1 ports.2.1.1 u S free
  have code : binSyms (A := A) H 0 = List.replicate H (bitSymbol false) := by simp [binSyms,List.ofFn_const]
  rw [Nat.one_mul,blank,List.append_nil,← code] at fill
  obtain ⟨y,n,hy,hn,run⟩ := writer v
  let E := {B with R := Function.update B.R dst (word ++ B.R dst)}
  obtain ⟨z,hz,_,clear⟩ := bclear_exec body zero y E
  have len : (E.R zero).length = H := by simp [E,B,apart.symm,length_binSyms]
  rw [len] at clear
  refine ⟨z,_,hz.trans (hy.trans hv),Nat.add_le_add_left (Nat.add_le_add_right hn _) _,Exec.seq fill (Exec.seq run ?_)⟩
  simpa only [E,B,Function.update_of_ne apart,Function.update_comm apart,
    Function.update_idem,← blank,Function.update_eq_self] using clear

private theorem emptyCommonTape {T : ℕ} (hs : Fin 6 → List Bool) (c : Fin 24 → Option ℕ)
    (k : Fin (CommonBank.count T)) (ha : ∀ i, CommonBank.auxSlot i ≠ k)
    (hh : ∀ i, CommonBank.headerSlot i ≠ k) (x : ℤ) :
    (CommonBank.bank (SharedBank.empty T prime) hs (fun _ => blank) 0
      (SharedBank.empty 1 prime) (SharedBank.empty 1 prime) c (SharedBank.empty 2 prime)).tape k x = blank := by
  simp only [CommonBank.bank, Shared50RecursiveBank.bank, RecursiveCallBank.bank,
    RecursiveShiftRoleBank.common, SharedBank.empty, RecursiveCallBank.work]
  revert ha hh
  induction k using Fin.addCases with
  | left k => intro _ _; simp [Tapes.append]
  | right k =>
    induction k using Fin.addCases with
    | left k =>
      change Fin (1+6) at k
      induction k using Fin.addCases with
      | left k => intro _ _; simp [Tapes.append]
      | right k => intro _ hh; exact absurd rfl (hh k)
    | right k =>
      induction k using Fin.addCases with
      | right k => intro _ _; simp [Tapes.append]
      | left k =>
        induction k using Fin.addCases with
        | left k => intro _ _; fin_cases k <;> simp [Tapes.append]
        | right k =>
          induction k using Fin.addCases with
          | left k => intro _ _; simp [Tapes.append]
          | right k =>
            induction k using Fin.addCases with
            | left k => intro _ _; simp [Tapes.append]
            | right k => intro ha _; exact absurd rfl (ha k)

private theorem counterCleanup_le {K A : ℕ} (S : Stacks K A) (tapes digits : List (Fin K))
    (counter : Fin K) (high : ℕ) (separate : counter ∉ digits) (empty : ∀ i ∈ tapes, S.R i = []) :
    let R := LabelCountBank.fill digits high (Function.update S.R counter (List.replicate high Node.tick))
    (tapes.map fun i => 4*(S.L i).length+2*(R i).length+4).sum ≤
      (tapes.map fun i => 4*(S.L i).length).sum + tapes.length*(2*high+4) := by
  intro R
  have bound (i) (hi : i ∈ tapes) : (R i).length ≤ high := by
    by_cases digit : i ∈ digits <;> by_cases eq : i = counter <;>
      simp_all [R,LabelCountBank.fill]
  calc
    _ ≤ (tapes.map fun i => 4*(S.L i).length+(2*high+4)).sum :=
      List.sum_le_sum fun i hi => by have := bound i hi; omega
    _ = _ := by simp [List.sum_map_add,List.map_const']

private theorem recordRadix_le_volume (v : Descriptor) (positive : v.Positive) (w d : ℕ)
    (width : v.width = d*(w+1)) (active : 0 < d) : prime^(w+1) ≤ volume prime v := by
  have atom : w+1 ≤ v.width := width ▸ Nat.le_mul_of_pos_left _ active
  have hp := Networks.Shared50ModularControl.prime_prime.pos
  have pre := Nat.mul_pos (Nat.mul_pos positive.1 positive.2.1) positive.2.2.1
  exact (Nat.pow_le_pow_right hp atom).trans
        ((Nat.le_mul_of_pos_left _ pre).trans ((Nat.le_mul_of_pos_right _ positive.2.2.2.1).trans
          ((Nat.le_mul_of_pos_right _ (pow_pos hp _)).trans (Nat.le_mul_of_pos_right _ positive.2.2.2.2))))

private theorem generatedCharge_binary_le (m w d W prefixWidth raw budget clear push H J : ℕ)
    (v : Descriptor) (positive : v.Positive) (width : v.width = d*(w+1))
    (active : 0 < d ∧ H = (prime^(w+1)).size ∧ J = W.size) :
    let V := volume prime v
    let trip := if 0 < d ∧ H = (prime^(w+1)).size ∧ J = W.size then
      min raw (budget + recordRoundTripRate m*V) else raw
    let cost := generatedRecordTime m w H prefixWidth (descriptorHeaderCost v) trip
    let binary := budget + recordRoundTripRate m*V + (12*m*m+4)*prefixWidth + generatedRecordRate m*V
    cost + (clear + 6*(push*cost)) ≤ binary + (clear + 6*(push*binary)) := by
  intro V trip cost binary
  have tripBound : trip ≤ budget + recordRoundTripRate m*V := by
    simpa only [trip,if_pos active] using min_le_right raw (budget + recordRoundTripRate m*V)
  have bound : cost ≤ binary := by
    dsimp only [cost,binary]
    rw [active.2.1]
    exact (generatedRecordTime_binary_le m w _ _ v positive (recordRadix_le_volume v positive w d width active.1)).trans
      (Nat.add_le_add_right (Nat.add_le_add_right tripBound _) _)
  exact Nat.add_le_add bound (Nat.add_le_add_left (Nat.mul_le_mul_left 6 (Nat.mul_le_mul_left push bound)) clear)

/-- Caller tapes shared by the generated good, padding and exceptional records. -/
def DirectoryReady {m K : ℕ} (v : Descriptor) (proj : Matrix (Fin m) (Fin m) ℚ)
    (w W H J : ℕ) (parent : Fin m → ZMod (prime^(w+1)))
    (prefixes : ℕ → List (Fin (prime+4))) (archiveTail : List (Fin (prime+4)))
    (schedules : List ℕ → List (Fin (prime+4))) (D : Stacks (66+K) prime) (pending : List ℕ) :=
  let caller := Fin.castAddEmb (n := 66) K
  let M := prime^(w+1)
  D.R (caller 46) = pending.flatMap (LabelDirectory.entry prefixes m (w+1)) ++ archiveTail ∧
    (∀ j ∈ pending, (D.R (caller 47)).length = (prefixes j).length) ∧
    (∀ i : Fin (66+K), 58 ≤ i.val → D.L i = [] ∧ D.R i = []) ∧ D.R (caller 49) = [] ∧
    (∃ suffix, D.R (caller 48) = matrixWords prime H (reduce M proj) ++ suffix) ∧
    D.R (caller 2) = binSyms H M ∧ D.R (caller 28) = binSyms 1 1 ∧ D.R (caller 53) = binSyms J W ∧
    (∀ i : Fin 6, D.R (caller ((i.natAdd 33).castLE (by decide : 39 ≤ 66))) = (Routines.hdr v i).map bitSymbol) ∧
    D.R (caller 44) = binSyms H (1 : ZMod M).val ∧ (D.R (caller 45)).length = w ∧
    D.R (caller 55) = (List.ofFn fun i => binSyms H (parent i).val).flatten ∧ D.R (caller 54) = schedules pending

theorem DirectoryReady.updateSelector {m K w W H J : ℕ} {v : Descriptor}
    {proj : Matrix (Fin m) (Fin m) ℚ} {parent : Fin m → ZMod (prime^(w+1))}
    {prefixes : ℕ → List (Fin (prime+4))} {archiveTail : List (Fin (prime+4))}
    {schedules : List ℕ → List (Fin (prime+4))} {S : Stacks (66+K) prime} {is : List ℕ}
    (port : Fin 66) (lo : 56 ≤ port.val) (hi : port.val ≤ 57) (xs : List (Fin (prime+4)))
    (h : DirectoryReady v proj w W H J parent prefixes archiveTail schedules S is) :
    DirectoryReady v proj w W H J parent prefixes archiveTail schedules
      {S with R := Function.update S.R (port.castAdd K) xs} is := by
  let caller := Fin.castAddEmb (n := 66) K
  have apart (i : Fin 66) (hi : i ≠ port) : caller i ≠ caller port := caller.injective.ne hi
  have pr (i : Fin (66+K)) (hi : 58 ≤ i.val) : i ≠ caller port := by
    intro eq; subst i; change 58 ≤ port.val at hi; omega
  let src := fun i : Fin 6 => caller ((i.natAdd 33).castLE (by decide : 39 ≤ 66))
  have so (i) : src i ≠ caller port := apart _ (by intro eq; have h := congrArg Fin.val eq; change 33+i.val = port.val at h; omega)
  have right (i : Fin 66) (small : i.val < 56) := Function.update_of_ne (apart i (by intro eq; subst port; omega)) xs S.R
  obtain ⟨hd,hw,hp,hb,hq,h2,h28,h53,hs,h44,h45,h55,h54⟩ := h
  refine ⟨(right 46 (by decide)).trans hd,fun j hj => (congrArg List.length (right 47 (by decide))).trans (hw j hj),
    fun i hi => ⟨(hp i hi).1,(Function.update_of_ne (pr i hi) _ _).trans (hp i hi).2⟩,
    (right 49 (by decide)).trans hb,?_,(right 2 (by decide)).trans h2,(right 28 (by decide)).trans h28,
    (right 53 (by decide)).trans h53,fun i => (Function.update_of_ne (so i) _ _).trans (hs i),
    (right 44 (by decide)).trans h44,(congrArg List.length (right 45 (by decide))).trans h45,
    (right 55 (by decide)).trans h55,(right 54 (by decide)).trans h54⟩
  · obtain ⟨suffix,eq⟩ := hq; exact ⟨suffix,(right 48 (by decide)).trans eq⟩

/-- The physical executor advances the two queues and clears its workspace.
These endpoints restore every condition consumed by the next ordinary record. -/
theorem DirectoryReady.afterExceptional [M8.Machine.Net] {m K dimension w W H J label : ℕ}
    {v : Descriptor} {proj : Matrix (Fin m) (Fin m) ℚ} {parent : Fin m → ZMod (prime^(w+1))}
    {prefixes : ℕ → List (Fin (prime+4))} {archiveTail : List (Fin (prime+4))}
    {schedules : List ℕ → List (Fin (prime+4))} {labels : List ℕ}
    (room : Record.size dimension+(rowSwapBlock.tapes+35+2) ≤ K+1)
    (S F : Stacks (66+(K+1)) prime) :
    let placement := directoryOrdinaryBank room
    let caller := Fin.castAddEmb (n := 66) (K+1)
    let ready := DirectoryReady v proj w W H J parent prefixes archiveTail schedules
    ready (embStk placement S) (label :: labels) →
    F.R (caller 46) = labels.flatMap (LabelDirectory.entry prefixes m (w+1)) ++ archiveTail →
    F.R (caller 54) = schedules labels →
    (∀ i, 58 ≤ i.val → i ≠ directoryMatrixTape room → F.L i = [] ∧ F.R i = []) →
    (∀ j : Fin 58, j ≠ 24 → j ≠ 54 → j ≠ 46 → F.R (caller (j.castAdd 8)) = S.R (caller (j.castAdd 8))) →
    ready (embStk placement F) labels := by
  intro placement caller ready start directory schedule clean frame
  obtain ⟨_,widths,_,scratch,⟨suffix,matrix⟩,base,unit,trailing,headers,one,clock,parents,_⟩ := start
  have cell (B : Stacks (66+(K+1)) prime) (i : Fin 66) :
      (embStk placement B).R (i.castAdd K) = B.R (caller i) := congrArg B.R (directoryOrdinaryBank_caller room i)
  have keep (j : Fin 58) (p : j ≠ 24) (q : j ≠ 54) (h : j ≠ 46) :=
    ((cell F (j.castAdd 8)).trans (frame j p q h)).trans (cell S (j.castAdd 8)).symm
  refine ⟨(cell F 46).trans directory,fun j hj => (congrArg List.length (keep 47 (by decide) (by decide) (by decide))).trans
    (widths j (List.mem_cons_of_mem _ hj)),(directoryOrdinaryBank_clear_iff room F).2 clean,
    (keep 49 (by decide) (by decide) (by decide)).trans scratch,
    ⟨suffix,(keep 48 (by decide) (by decide) (by decide)).trans matrix⟩,
    (keep 2 (by decide) (by decide) (by decide)).trans base,(keep 28 (by decide) (by decide) (by decide)).trans unit,
    (keep 53 (by decide) (by decide) (by decide)).trans trailing,?_,
    (keep 44 (by decide) (by decide) (by decide)).trans one,
    (congrArg List.length (keep 45 (by decide) (by decide) (by decide))).trans clock,
    (keep 55 (by decide) (by decide) (by decide)).trans parents,(cell F 54).trans schedule⟩
  intro i
  let j := (i.natAdd 33).castLE (by decide : 39 ≤ 58)
  have range : 33 ≤ j.val ∧ j.val < 39 := by change 33 ≤ 33+i.val ∧ 33+i.val < 39; omega
  apply (keep j ?_ ?_ ?_).trans (headers i) <;> intro eq <;> have h := congrArg Fin.val eq <;> first | (change j.val = 24 at h; omega) | (change j.val = 54 at h; omega) | (change j.val = 46 at h; omega)

open IntegerMultBounds.MathlibTM2.Fast.Main in
/-- Contents of the binary payload tape at its saved head. -/
def RecordPayload {K N : ℕ} (port : Fin K) (source : ℤ → Fin 4) (head : ℤ)
    (word : Fin N → ZMod 2) (S : Stacks K prime) : Prop :=
  ∀ z, readAt blank (S.L port) (S.R port) (z-head) = RadixToBinary.binaryEncoding.encode
    (putWord source head ((List.ofFn word).map SparseRoleCircuit.encode) z)

/-- Removing the matrix tape leaves the ordinary scan with its original caller
data and blank workspace, including the payload at the original head position. -/
theorem DirectoryReady.afterMatrixWriter [M8.Machine.Net] {m K d w W H J N : ℕ} {v : Descriptor}
    {proj : Matrix (Fin m) (Fin m) ℚ} {parent : Fin m → ZMod (prime^(w+1))}
    {prefixes : ℕ → List (Fin (prime+4))} {archiveTail : List (Fin (prime+4))}
    {schedules : List ℕ → List (Fin (prime+4))} {pending : List ℕ}
    {source : ℤ → Fin 4} {head : ℤ} {word : Fin N → ZMod 2}
    (room : Record.size d+(rowSwapBlock.tapes+35+2) ≤ K+1)
    (S D : Stacks (66+(K+1)) prime)
    (caller : ∀ i : Fin 66, i.val < 58 → D.L (i.castAdd (K+1)) = S.L (i.castAdd (K+1)) ∧
      D.R (i.castAdd (K+1)) = S.R (i.castAdd (K+1)))
    (blank : ∀ i, 58 ≤ i.val → i ≠ directoryMatrixTape room → D.L i = [] ∧ D.R i = []) :
    let bank := directoryOrdinaryBank room
    let ready := DirectoryReady v proj w W H J parent prefixes archiveTail schedules
    let payload := RecordPayload ((24 : Fin 66).castAdd K) source head word
    ready (embStk bank S) pending → payload (embStk bank S) →
      ready (embStk bank D) pending ∧ payload (embStk bank D) := by
  intro bank ready payload initial packed
  have old := initial.2.2.1
  have cleared := (directoryOrdinaryBank_clear_iff room D).2 blank
  have agree (i : Fin (66+K)) :
      (embStk bank D).L i = (embStk bank S).L i ∧ (embStk bank D).R i = (embStk bank S).R i := by
    by_cases hi : 58 ≤ i.val
    · exact ⟨(cleared i hi).1.trans (old i hi).1.symm,(cleared i hi).2.trans (old i hi).2.symm⟩
    · let j : Fin 66 := ⟨i.val,by omega⟩
      have eq : i = j.castAdd K := Fin.ext rfl
      rw [eq]
      change D.L (bank (j.castAdd K)) = S.L (bank (j.castAdd K)) ∧
        D.R (bank (j.castAdd K)) = S.R (bank (j.castAdd K))
      rw [directoryOrdinaryBank_caller]
      exact caller j (Nat.lt_of_not_ge hi)
  have left := funext fun i => (agree i).1
  have right := funext fun i => (agree i).2
  constructor
  · simpa only [ready,DirectoryReady,left,right] using initial
  · simpa only [payload,RecordPayload,left,right] using packed

theorem recordPayload_ordinaryBank [M8.Machine.Net] {K d N : ℕ}
    (room : Record.size d+(rowSwapBlock.tapes+35+2) ≤ K+1) (source : ℤ → Fin 4)
    (head : ℤ) (word : Fin N → ZMod 2) (S : Stacks (66+(K+1)) prime) :
    RecordPayload ((24 : Fin 66).castAdd K) source head word (embStk (directoryOrdinaryBank room) S) ↔
      RecordPayload ((24 : Fin 66).castAdd (K+1)) source head word S := by
  simp only [RecordPayload,embStk,Function.comp_apply,directoryOrdinaryBank_caller]

/-- The ordinary two-field word fills exactly one exceptional matrix payload. -/
theorem directoryPayloadLength {m d M W N : ℕ} (e : (Fin m ⊕ Fin m) ≃ Fin (d+1))
    (length : N = M^m*(M^m*W)) : M^(d+1)*W = N := by
  have dimension : m+m = d+1 := by simpa using Fintype.card_congr e
  rw [← dimension,pow_add,Nat.mul_assoc,length]

/-- Casting the concatenated address to the physical matrix dimension leaves the
serialized pivot instructions in the order generated by the directory. -/
theorem directorySchedule_cast {m n A : ℕ} (dimension : m+m = n)
    (P g : Matrix (Fin m) (Fin m) (ZMod prime)) (parent inv : Fin m → ZMod prime) :
    residualSchedule (A := A) (projectorResidual (finSumFinEquiv.trans (finCongr dimension)) P parent inv g) =
      residualSchedule (projectorResidual finSumFinEquiv P parent inv g) := by
  subst n
  rfl

open IntegerMultBounds.MathlibTM2.Fast.Main in
/-- Execute an exceptional entry from the generated caller frame and return
the same frame at the next label, with the transformed word still in place. -/
theorem DirectoryReady.runExceptional [M8.Machine.Net] {m d K w W J N : ℕ} {P U : Type}
    (dimension : m+m = d+1) (v : Descriptor) (proj : Matrix (Fin m) (Fin m) ℚ)
    (idem : proj*proj = proj) (adm : Admissible prime proj)
    (parent inv : Fin m → ZMod (prime^(w+1))) (reciprocal : ∀ i, parent i * inv i = 1)
    (data : ScanData m d w W) (hm : prime^(w+1) < 2^data.H) (hw : W < 2^J) (positive : 0 < W)
    (room : Record.size d+(rowSwapBlock.tapes+35+2) ≤ K+1)
    (capacity : (anchorProgram d true).1+(anchorProgram d false).1+1 ≤ columnCapacity)
    (body : P → Pr P (66+(K+1)) columnCapacity prime U) (c : ℕ) (bodyBound : ∀ f, mnProgPush (body f) ≤ c)
    (prefixes : ℕ → List (Fin (prime+4))) (archiveTail : List (Fin (prime+4)))
    (bad : ℕ → Bool) (j : ℕ) (inside : j < data.records)
    (live : LabelStock.live m (w+1) 1 j = true) (exceptional : bad j = true)
    (source : ℤ → Fin 4) (head : ℤ) (length : N = (prime^(w+1))^m*((prime^(w+1))^m*W)) (original : Fin N → ZMod 2)
    (u : HS (66+(K+1)) columnCapacity prime U) (S : Stacks (66+(K+1)) prime) :
    let e := finSumFinEquiv.trans (finCongr dimension)
    let physical := data.physical e proj parent inv
    let φ := LabelRing.res prime (w+1) (by omega)
    let code := fun k => residualSchedule (A := prime) (projectorResidual finSumFinEquiv (reduce prime proj)
      (φ ∘ parent) (φ ∘ inv) (LabelStock.residue m (w+1) 1 k))
    let schedule := fun (xs : List ℕ) => xs.flatMap fun k => if bad k then code k else []
    let ready := DirectoryReady v proj w W data.H J parent prefixes archiveTail schedule
    let placement := directoryOrdinaryBank room
    let caller := Fin.castAddEmb (n := 66) (K+1)
    let payload := fun (word : Fin N → ZMod 2) D =>
      RecordPayload ((24 : Fin 66).castAdd K) source head word (embStk placement D)
    let labels := (List.range data.records).drop (j+1)
    ready (embStk placement S) ((List.range data.records).drop j) → S.R (directoryMatrixTape room) = physical.matrices j →
    payload original S →
    let C := physical.table (LabelStock.residue m (w+1) 1 j)
    let rows := classPivots C
    let privateTapes := (List.finRange (66+(K+1))).filter fun i => decide (58 ≤ i.val ∧ i ≠ directoryMatrixTape room)
    ∃ z D n next, z.user = u.user ∧ n ≤ exceptionalRecordTime U rows (negativeAnchor rows C) m w W data.H J
      privateTapes.length (max (mnProgPush (directoryExceptionalCore (P := P) (U := U) d room capacity)) c) (prefixes j).length ∧
      Exec body (directoryExceptionalProgram m d room capacity) (mk u S) n (mk z D) ∧
      ready (embStk placement D) labels ∧ D.R (directoryMatrixTape room) = physical.matrices (j+1) ∧
      (∀ x k, next ((FlatCoordinateLayout.index ((projectorResidual e (reduce (prime^(w+1)) proj) parent inv
        (physicalLabel m (w+1) j)).mulVec x) k).cast (directoryPayloadLength e length)) = original ((FlatCoordinateLayout.index x k).cast (directoryPayloadLength e length))) ∧
      payload next D ∧ D.R (caller 57) = S.R (caller 57) ∧ D.R (caller 56) = S.R (caller 56) := by
  have volumeEq := directoryPayloadLength (finSumFinEquiv.trans (finCongr dimension)) length
  cases volumeEq
  intro e physical φ code schedule ready placement caller payload labels start matrix input C rows privateTapes
  have index : j < (List.range data.records).length := by simpa using inside
  have suffix : (List.range data.records).drop j = j :: labels := by
    simpa only [List.getElem_range] using (List.getElem_cons_drop index).symm
  rw [suffix] at start
  have physicalInput := (recordPayload_ordinaryBank room source head original S).1 input
  have initialReady := start
  obtain ⟨directory,widths,privateBlank,scratch,_,base,unit,width,_,one,clock,_,queue⟩ := start
  have cell (i : Fin 66) : (embStk placement S).R (i.castAdd K) = S.R (caller i) :=
    congrArg S.R (directoryOrdinaryBank_caller room i)
  let counter := caller 58
  let filled := {S with R := Function.update S.R counter (List.replicate ((prime^(w+1))^(d+1)*W) Node.tick)}
  have keep (i : Fin 66) (ne : i ≠ 58) : filled.R (caller i) = S.R (caller i) :=
    Function.update_of_ne (caller.injective.ne ne) _ _
  have scheduleNow : S.R (caller 54) = code j ++ schedule labels := by
    have parts : schedule (j :: labels) = code j ++ schedule labels := by
      simp only [schedule,List.flatMap_cons,exceptional,ite_true]
    exact (cell 54).symm.trans (queue.trans parts)
  have archive : filled.R (directoryMatrixTape room) = physical.matrices j :=
    (Function.update_of_ne (directoryResidualBank_off room _ _ 58 (by decide)) _ _).trans matrix
  obtain ⟨z,D,n,next,user,time,run,tail,clean,effect,pivots,output,dir,frame⟩ :=
    scheduledProjectorRecord_exec e proj idem adm parent inv reciprocal j live data inside J hm hw positive
      room capacity body u S (schedule labels) original source head
      ((cell 2).symm.trans base) ((cell 53).symm.trans width) ((directoryOrdinaryBank_clear_iff room S).1 privateBlank)
      ((keep 28 (by decide)).trans ((cell 28).symm.trans unit))
      ((keep 44 (by decide)).trans ((cell 44).symm.trans one)) archive
      (fun z => by have eq := physicalInput z; change readAt _ (S.L (caller 24)) (filled.R (caller 24)) _ = _
                   rw [keep 24 (by decide)]; exact eq)
      (((keep 54 (by decide)).trans scheduleNow).trans
        (congrArg (fun xs => xs ++ schedule labels) (directorySchedule_cast dimension _ _ _ _).symm)) c bodyBound prefixes labels archiveTail
      ((keep 46 (by decide)).trans ((cell 46).symm.trans directory))
      ((congrArg List.length ((keep 47 (by decide)).trans (cell 47).symm)).trans (widths j List.mem_cons_self))
      ((congrArg List.length ((keep 45 (by decide)).trans (cell 45).symm)).trans clock)
      ((keep 49 (by decide)).trans ((cell 49).symm.trans scratch))
  have kept (i : Fin 58) (p : i ≠ 24) (q : i ≠ 54) (h : i ≠ 46) :=
    (frame i p q h).2.trans (keep (i.castAdd 8) (by intro eq; have val := congrArg Fin.val eq; change i.val = 58 at val; omega))
  exact ⟨z,D,n,next,user,time,run,DirectoryReady.afterExceptional room S D initialReady
    dir pivots clean kept,tail,effect,(recordPayload_ordinaryBank room source head next D).2 output,kept 57 (by decide) (by decide) (by decide),
    kept 56 (by decide) (by decide) (by decide)⟩

/-- Uniform exceptional charge per payload symbol for a fixed machine layout. -/
noncomputable def exceptionalVolumeRate [M8.Machine.Net] (U : Type) (d m tapes push w : ℕ) : ℕ :=
  let coefficients := exceptionalRecordTime_binary_le U d m tapes push
  coefficients.choose + coefficients.choose_spec.choose * swapVolumeRate w

private theorem atomPower_eq [M8.Machine.Net] (L d w : ℕ) (active : 0 < d) (width : L = d*(w+1)) :
    ((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau =
      (L : ℝ)^M8.Machine.BudgetBound.tau / (d : ℝ)^M8.Machine.BudgetBound.tau := by
  rw [width,Nat.cast_mul,Real.mul_rpow (Nat.cast_nonneg d) (Nat.cast_nonneg (w+1))]
  have pos : (0 : ℝ) < d := by exact_mod_cast active
  field_simp

private theorem batchRate_mono (fixed records labels N : ℕ) {b r b' r' : ℝ}
    (ordinary : b ≤ b') (exceptional : r ≤ r') :
    (fixed : ℝ) + records*(b+6)+2 + ((labels : ℝ)/prime)*r*(records*N) ≤
      fixed + records*(b'+6)+2 + ((labels : ℝ)/prime)*r'*(records*N) := by
  gcongr

noncomputable def exceptionalRateAt [M8.Machine.Net] (U : Type) (d m tapes push : ℕ) (power : ℝ) : ℝ :=
  let coeff := exceptionalRecordTime_binary_le U d m tapes push
  coeff.choose + (coeff.choose_spec.choose : ℝ)*((3808275+M8.RevMachine.LeafCore.C)*power)

private theorem exceptionalVolumeRate_le [M8.Machine.Net] (U : Type) (d m tapes push w : ℕ) :
    (exceptionalVolumeRate U d m tapes push w : ℝ) ≤
      exceptionalRateAt U d m tapes push (((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau) := by
  unfold exceptionalVolumeRate exceptionalRateAt
  push_cast
  gcongr
  simpa only [Nat.cast_add,Nat.cast_one] using swapVolumeRate_le w

private theorem exceptionalVolumeRate_bound [M8.Machine.Net] (U : Type) (d m tapes push w W prefixWidth : ℕ)
    (rows : Fin (d+1) → Fin (d+1)) (negative : Bool) (positive : 0 < W) :
    exceptionalRecordTime U rows negative m w W (prime^(w+1)).size W.size tapes push prefixWidth ≤
      exceptionalVolumeRate U d m tapes push w * ((prime^(w+1))^(d+1)*W) + 4*prefixWidth :=
  (exceptionalRecordTime_binary_le U d m tapes push).choose_spec.choose_spec rows negative w W prefixWidth positive

open IntegerMultBounds.MathlibTM2.Fast.Main in
/-- Endpoint and time bound for the generated three-branch directory program. -/
def ArchiveRun [M8.Machine.Net] {m d K w W J N : ℕ} {P U : Type}
    (dimension : m+m = d+1) (vDescriptor : Descriptor) (proj : Matrix (Fin m) (Fin m) ℚ)
    (parent inv : Fin m → ZMod (prime^(w+1)))
    (data : ScanData m d w W)
    (room : Record.size d+(rowSwapBlock.tapes+35+2) ≤ K+1)
    (capacity : (anchorProgram d true).1+(anchorProgram d false).1+1 ≤ columnCapacity)
    (body : P → Pr P (66+(K+1)) columnCapacity prime U) (c : ℕ)
    (prefixes : ℕ → List (Fin (prime+4))) (archiveTail : List (Fin (prime+4)))
    (rankFits : proj.rank ≤ m)
    (source : ℤ → Fin 4) (head : ℤ) (length : N = (prime^(w+1))^m*((prime^(w+1))^m*W)) (original : Fin N → ZMod 2)
    (good skip : Pr P (66+K) columnCapacity prime U) (ordinaryCost : ℕ → ℕ) (ordinaryCeiling : ℕ)
    (ordinaryEffect : ℕ → (Fin N → ZMod 2) → (Fin N → ZMod 2) → Prop)
    (u : HS (66+(K+1)) columnCapacity prime U) (S : Stacks (66+(K+1)) prime) : Prop :=
    let e := finSumFinEquiv.trans (finCongr dimension)
    let physical := data.physical e proj parent inv
    let φ := LabelRing.res prime (w+1) (by omega)
    let live := LabelStock.live m (w+1) 1
    let bad := fun j => fallbackBit rankFits (reduce (prime^(w+1)) proj) (physicalLabel m (w+1) j)
    let code := fun k => residualSchedule (A := prime) (projectorResidual finSumFinEquiv (reduce prime proj)
      (φ ∘ parent) (φ ∘ inv) (LabelStock.residue m (w+1) 1 k))
    let schedule := fun (xs : List ℕ) => xs.flatMap fun k => if bad k then code k else []
    let ready := DirectoryReady vDescriptor proj w W data.H J parent prefixes archiveTail schedule
    let placement := directoryOrdinaryBank room
    let caller := Fin.castAddEmb (n := 66) K
    let payload := RecordPayload (N := N) (caller 24) source head
    let pending := fun j => (List.range data.records).drop j
    let frame := fun j word D => ready D (pending j) ∧ payload word D
    let costBad := fun j =>
      let C := physical.table (LabelStock.residue m (w+1) 1 j)
      let rows := classPivots C
      let scratch := (List.finRange (66+(K+1))).filter fun i => decide (58 ≤ i.val ∧ i ≠ directoryMatrixTape room)
      exceptionalRecordTime U rows (negativeAnchor rows C) m w W data.H J scratch.length
        (max (mnProgPush (directoryExceptionalCore (P := P) (U := U) d room capacity)) c) (prefixes j).length
    let effect := fun j (x y : Fin N → ZMod 2) => if live j && bad j then
      ∀ a k, y ((FlatCoordinateLayout.index ((projectorResidual e (reduce (prime^(w+1)) proj) parent inv
        (physicalLabel m (w+1) j)).mulVec a) k).cast (directoryPayloadLength e length)) =
        x ((FlatCoordinateLayout.index a k).cast (directoryPayloadLength e length))
      else ordinaryEffect j x y
    frame 0 original (embStk placement S) → S.R (directoryMatrixTape room) = physical.matrices 0 →
    S.R (placement (caller 57)) = (List.range data.records).map (fun j => bitSymbol (live j)) →
    S.R (placement (caller 56)) = (List.range data.records).map (fun j => bitSymbol (bad j)) →
    let advance := dropWords (placement (caller 2)) (directoryMatrixTape room) (placement (caller 59)) ((d+1)*(d+1))
    let cost := fun j => if live j && bad j then costBad j else ordinaryCost j + ((d+1)*(d+1)*(4*data.H+4)+1)
    let exceptionalCount := ((∑ k ∈ Finset.range proj.rank, (k+1)*(m+1))*data.records)/prime
    let priced := fun n => ∀ parents baseline budget, data.records = parents*(prime^(w+1))^(m*m) →
      let ordinaryTime := data.records*(baseline+6)+2
      ordinaryTime ≤ budget →
      (∀ j < data.records, ¬ (live j = true ∧ bad j = true) →
        ordinaryCost j + ((d+1)*(d+1)*(4*data.H+4)+1) ≤ baseline ∨
        (data.H = Nat.size (prime^(w+1)) ∧ 0 < W ∧ ordinaryCost j + (prime^(w+1))^(d+1)*W ≤ baseline)) →
      (0 < exceptionalCount → ∀ j < data.records, live j = true → bad j = true →
        costBad j ≤ baseline+(budget-ordinaryTime)/exceptionalCount) → n ≤ budget
    let scratch := (List.finRange (66+(K+1))).filter fun i => decide (58 ≤ i.val ∧ i ≠ directoryMatrixTape room)
    let push := max (mnProgPush (directoryExceptionalCore (P := P) (U := U) d room capacity)) c
    let binaryTime := fun n => ∀ parents baseline, data.records = parents*(prime^(w+1))^(m*m) →
      data.H = (prime^(w+1)).size → J = W.size →
      ordinaryCeiling + N ≤ baseline →
      n ≤ data.records*(baseline+6)+2 + exceptionalCount*(exceptionalVolumeRate U d m scratch.length push w*N)
    ∃ z B n next, z.user = u.user ∧ frame data.records next (embStk placement B) ∧
      (List.range data.records).foldl (fun possible j y => ∃ x, possible x ∧ effect j x y) (· = original) next ∧
      B.R (directoryMatrixTape room) = [] ∧ B.R (placement (caller 57)) = [] ∧ B.R (placement (caller 56)) = [] ∧
      priced n ∧ binaryTime n ∧ n ≤ ((List.range data.records).map fun j => cost j+2+4).sum+2 ∧
      Exec body (classifiedScan (placement (caller 57)) (placement (caller 56)) ((embProg placement id good).seq advance)
        (directoryExceptionalProgram m d room capacity) ((embProg placement id skip).seq advance)) (mk u S) n (mk z B)

open IntegerMultBounds.MathlibTM2.Fast.Main RingFormula in
def GeneratedArchiveRun [M8.Machine.Net] {m d K w W J N : ℕ} {P U : Type}
    (dimension : m+m = d+1) (vDescriptor : Descriptor) (proj : Matrix (Fin m) (Fin m) ℚ)
    (parent inv : Fin m → ZMod (prime^(w+1)))
    (data : ScanData m d w W)
    (room : Record.size d+(rowSwapBlock.tapes+35+2) ≤ K+1)
    (capacity : (anchorProgram d true).1+(anchorProgram d false).1+1 ≤ columnCapacity)
    (body : P → Pr P (66+(K+1)) columnCapacity prime U) (c : ℕ)
    (prefixes : ℕ → List (Fin (prime+4))) (archiveTail : List (Fin (prime+4)))
    (rankFits : proj.rank ≤ m)
    (source : ℤ → Fin 4) (head : ℤ) (length : N = (prime^(w+1))^m*((prime^(w+1))^m*W)) (original : Fin N → ZMod 2)
    (good skip : Pr P (66+K) columnCapacity prime U) (ordinaryCost : ℕ → ℕ) (ordinaryCeiling : ℕ)
    (ordinaryEffect : ℕ → (Fin N → ZMod 2) → (Fin N → ZMod 2) → Prop)
    (u : HS (66+(K+1)) columnCapacity prime U) (S : Stacks (66+(K+1)) prime)
    : Prop :=
    let e := finSumFinEquiv.trans (finCongr dimension)
    let physical := data.physical e proj parent inv
    let φ := LabelRing.res prime (w+1) (by omega)
    let live := LabelStock.live m (w+1) 1
    let bad := fun j => fallbackBit rankFits (reduce (prime^(w+1)) proj) (physicalLabel m (w+1) j)
    let code := fun k => residualSchedule (A := prime) (projectorResidual finSumFinEquiv (reduce prime proj)
      (φ ∘ parent) (φ ∘ inv) (LabelStock.residue m (w+1) 1 k))
    let schedule := fun (xs : List ℕ) => xs.flatMap fun k => if bad k then code k else []
    let ready := DirectoryReady vDescriptor proj w W data.H J parent prefixes archiveTail schedule
    let placement := directoryOrdinaryBank room
    let caller := Fin.castAddEmb (n := 66) K
    let payload := RecordPayload (N := N) (caller 24) source head
    let pending := fun j => (List.range data.records).drop j
    let frame := fun j word D => ready D (pending j) ∧ payload word D
    let effect := fun j (x y : Fin N → ZMod 2) => if live j && bad j then
      ∀ a k, y ((FlatCoordinateLayout.index ((projectorResidual e (reduce (prime^(w+1)) proj) parent inv
        (physicalLabel m (w+1) j)).mulVec a) k).cast (directoryPayloadLength e length)) =
        x ((FlatCoordinateLayout.index a k).cast (directoryPayloadLength e length))
      else ordinaryEffect j x y
    frame 0 original (embStk placement S) →
    S.R (directoryMatrixTape room) = [] →
    S.R ((57 : Fin 66).castAdd (K+1)) = (List.range data.records).map (fun j => bitSymbol (live j)) →
    S.R ((56 : Fin 66).castAdd (K+1)) = (List.range data.records).map (fun j => bitSymbol (bad j)) →
    let advance := dropWords (placement (caller 2)) (directoryMatrixTape room) (placement (caller 59)) ((d+1)*(d+1))
    let exceptionalCount := ((∑ k ∈ Finset.range proj.rank, (k+1)*(m+1))*data.records)/prime
    let scratch := (List.finRange (66+(K+1))).filter fun i => decide (58 ≤ i.val ∧ i ≠ directoryMatrixTape room)
    let push := max (mnProgPush (directoryExceptionalCore (P := P) (U := U) d room capacity)) c
    let binaryTime := fun n => ∀ parents baseline, data.records = parents*(prime^(w+1))^(m*m) →
      data.H = (prime^(w+1)).size → J = W.size →
      ordinaryCeiling + N ≤ baseline →
      n ≤ data.records*(baseline+6)+2 + exceptionalCount*(exceptionalVolumeRate U d m scratch.length push w*N)
    let initTime := directoryQueueInitTime m d w data.H data.records S
    let queueTime := directoryMatrixQueueTime m d w data.H data.records (S.R ((47 : Fin 66).castAdd (K+1))).length
    ∃ (prepare : Pr P (66+(K+1)) columnCapacity prime U), ∃ z B setupSteps n next, z.user = u.user ∧ frame data.records next (embStk placement B) ∧
      (List.range data.records).foldl (fun possible j y => ∃ x, possible x ∧ effect j x y) (· = original) next ∧
      B.R (directoryMatrixTape room) = [] ∧ B.R (placement (caller 57)) = [] ∧ B.R (placement (caller 56)) = [] ∧
      binaryTime n ∧ (∀ p, mnProgPush prepare ≤ p → (∀ f, mnProgPush (body f) ≤ p) →
        setupSteps ≤ initTime + queueTime + (4*scratch.length+1 + scratch.length*(6*(p*initTime)))) ∧
      (let span := max (S.R ((47 : Fin 66).castAdd (K+1))).length N
       let V := data.records*span
       let suffix := (S.R ((48 : Fin 66).castAdd (K+1))).drop (m*m*data.H)
       let extent := (1+m*m)*V + archiveTail.length + suffix.length
       let budget := directoryQueueInitRate m d*extent
       ∀ p, mnProgPush prepare ≤ p → (∀ f, mnProgPush (body f) ≤ p) →
         data.H = (prime^(w+1)).size → 0 < W → 0 < data.records →
         let preparation := budget + ((12*m*m+4+directoryMatrixRate m d)*V+4) +
           (4*scratch.length+1 + scratch.length*(6*(p*budget)))
         setupSteps ≤ preparation ∧
           ∀ parents baseline, data.records = parents*(prime^(w+1))^(m*m) → J = W.size →
             ordinaryCeiling + N ≤ baseline →
             setupSteps+n ≤ preparation + (data.records*(baseline+6)+2 +
               exceptionalCount*(exceptionalVolumeRate U d m scratch.length push w*N))) ∧
      (∀ p parents baseline, mnProgPush prepare ≤ p → (∀ f, mnProgPush (body f) ≤ p) →
        data.records = parents*(prime^(w+1))^(m*m) → data.H = (prime^(w+1)).size → J = W.size →
        0 < W → ordinaryCeiling + N ≤ baseline →
        let width := (S.R ((47 : Fin 66).castAdd (K+1))).length
        setupSteps+n ≤ initTime + (data.records*((12*m*m+4)*width+directoryMatrixRate m d*N)+4) +
          (4*scratch.length+1 + scratch.length*(6*(p*initTime))) +
          (data.records*(baseline+6)+2 + exceptionalCount*(exceptionalVolumeRate U d m scratch.length push w*N))) ∧
      Exec body (prepare.seq (classifiedScan (placement (caller 57)) (placement (caller 56)) ((embProg placement id good).seq advance)
        (directoryExceptionalProgram m d room capacity) ((embProg placement id skip).seq advance))) (mk u S) (setupSteps+n) (mk z B)

open IntegerMultBounds.MathlibTM2.Fast.Main RingFormula in
/-- Bound the two matrix-writer charges by the volume occupied by the ready
directory, including the saved suffix of the projector tape. -/
theorem DirectoryReady.matrixSetup_volume [M8.Machine.Net] {m d K w W J N : ℕ}
    {v : Descriptor} {proj : Matrix (Fin m) (Fin m) ℚ} {parent : Fin m → ZMod (prime^(w+1))}
    {prefixes : ℕ → List (Fin (prime+4))} {archiveTail : List (Fin (prime+4))}
    {schedule : List ℕ → List (Fin (prime+4))} (data : ScanData m d w W)
    (room : Record.size d+(rowSwapBlock.tapes+35+2) ≤ K+1) (S : Stacks (66+(K+1)) prime)
    (initial : DirectoryReady v proj w W data.H J parent prefixes archiveTail schedule (embStk (directoryOrdinaryBank room) S)
      (List.range data.records)) (precision : data.H = (prime^(w+1)).size)
    (radixPayload : prime^(w+1) ≤ N) (nonempty : 0 < data.records) :
    let span := max (S.R ((47 : Fin 66).castAdd (K+1))).length N
    let V := data.records*span
    let suffix := (S.R ((48 : Fin 66).castAdd (K+1))).drop (m*m*data.H)
    let extent := (1+m*m)*V + archiveTail.length + suffix.length
    let budget := directoryQueueInitRate m d*extent
    let initTime := directoryQueueInitTime m d w data.H data.records S
    let queueTime := directoryMatrixQueueTime m d w data.H data.records (S.R ((47 : Fin 66).castAdd (K+1))).length
    initTime ≤ budget ∧ queueTime ≤ (12*m*m+4+directoryMatrixRate m d)*V+4 := by
  intro span V suffix extent budget initTime queueTime
  obtain ⟨directory,widths,_,_,projector,modulus,_,_,_,unit,clock,_,_⟩ := initial
  have port (j : Fin 66) : directoryOrdinaryBank room ((Fin.castAddEmb K) j) = j.castAdd (K+1) := directoryOrdinaryBank_caller room j
  simp only [embStk,Function.comp_apply,port] at directory widths projector modulus unit clock
  have Mpos : 0 < prime^(w+1) := pow_pos Networks.Shared50ModularControl.prime_prime.pos _
  have payloadSpan : N ≤ span := le_max_right ..
  have spanVolume : span ≤ V := Nat.le_mul_of_pos_left _ nonempty
  have payloadVolume : N ≤ V := payloadSpan.trans spanVolume
  have prefixSpan : (S.R ((47 : Fin 66).castAdd (K+1))).length ≤ span := le_max_left ..
  have volumeExtent : V ≤ extent := by
    dsimp only [extent]; rw [Nat.add_mul,one_mul]; omega
  have radix := (radixPayload.trans payloadVolume).trans volumeExtent
  have recordsFit : data.records ≤ extent :=
    (Nat.le_mul_of_pos_right _ ((Mpos.trans_le radixPayload).trans_le payloadSpan)).trans volumeExtent
  have digits : data.H ≤ extent := precision ▸ (Nat.size_le.mpr Nat.lt_two_pow_self).trans radix
  have atomN : w+1 ≤ N := Nat.lt_two_pow_self.le.trans
    ((Nat.pow_le_pow_left Networks.Shared50ModularControl.prime_prime.two_le _).trans radixPayload)
  have atom := ((Nat.le_succ w).trans atomN).trans (payloadVolume.trans volumeExtent)
  let width := (S.R ((47 : Fin 66).castAdd (K+1))).length
  have directorySize : (S.R ((46 : Fin 66).castAdd (K+1))).length ≤ extent := by
    rw [directory]
    simp only [List.length_append,List.flatMap_def]
    rw [BlockRotationData.uniform_volume (width+(w+1)*(m*m))]
    · simp only [List.length_map,List.length_range]
      have words := Nat.mul_le_mul_left data.records (Nat.add_le_add prefixSpan (Nat.mul_le_mul_right (m*m) (atomN.trans payloadSpan)))
      dsimp only [extent]
      calc
        _ ≤ data.records*(span+span*(m*m)) + archiveTail.length := Nat.add_le_add_right words _
        _ = (1+m*m)*V + archiveTail.length := by dsimp only [V]; ring
        _ ≤ _ := Nat.le_add_right _ _
    · intro word mem
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp mem
      rw [LabelDirectory.entry_length,← widths j (hj)]
  have projectorSize : (S.R ((48 : Fin 66).castAdd (K+1))).length ≤ extent := by
    obtain ⟨tail,h⟩ := projector
    dsimp only [extent,suffix]
    rw [h,← length_matrixWords prime data.H (reduce (prime^(w+1)) proj),List.drop_left,
      List.length_append,length_matrixWords]
    have hH : data.H ≤ V := precision ▸ (Nat.size_le.mpr Nat.lt_two_pow_self).trans (radixPayload.trans payloadVolume)
    have entry := Nat.mul_le_mul_left (m*m) hH
    rw [Nat.add_mul,one_mul]
    omega
  have initLe : initTime ≤ budget := by
    dsimp only [initTime,budget]
    rw [precision]
    apply directoryQueueInitTime_binary_le _ _ _ _ _ S radix recordsFit directorySize
    intro j hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with h | h | h | h | h
    · have eq : j = 2 := Fin.ext h
      subst j; rw [modulus,length_binSyms]; exact digits
    · have eq : j = 47 := Fin.ext h
      exact eq ▸ prefixSpan.trans (spanVolume.trans volumeExtent)
    · have eq : j = 48 := Fin.ext h
      exact eq ▸ projectorSize
    · have eq : j = 44 := Fin.ext h
      subst j; rw [unit,length_binSyms]; exact digits
    · have eq : j = 45 := Fin.ext h
      subst j; rw [clock]; exact atom
  have queueVolume : queueTime ≤ (12*m*m+4+directoryMatrixRate m d)*V+4 := by
    dsimp only [queueTime]
    rw [precision]
    refine (directoryMatrixQueueTime_binary_le ..).trans (Nat.add_le_add_right ?_ 4)
    calc
      _ ≤ data.records*((12*m*m+4)*span+directoryMatrixRate m d*span) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add (Nat.mul_le_mul_left _ prefixSpan) (Nat.mul_le_mul_left _ (radixPayload.trans payloadSpan)))
      _ = (12*m*m+4+directoryMatrixRate m d)*V := by dsimp only [V]; ring
  exact ⟨initLe,queueVolume⟩

open IntegerMultBounds.MathlibTM2.Fast.Main RingFormula in
theorem generatedArchive_exec [M8.Machine.Net] {m d K w W J N : ℕ} {P U : Type}
    (dimension : m+m = d+1) (vDescriptor : Descriptor) (proj : Matrix (Fin m) (Fin m) ℚ)
    (parent inv : Fin m → ZMod (prime^(w+1)))
    (data : ScanData m d w W)
    (room : Record.size d+(rowSwapBlock.tapes+35+2) ≤ K+1)
    (capacity : (anchorProgram d true).1+(anchorProgram d false).1+1 ≤ columnCapacity)
    (body : P → Pr P (66+(K+1)) columnCapacity prime U) (c : ℕ)
    (prefixes : ℕ → List (Fin (prime+4))) (archiveTail : List (Fin (prime+4)))
    (rankFits : proj.rank ≤ m)
    (source : ℤ → Fin 4) (head : ℤ) (length : N = (prime^(w+1))^m*((prime^(w+1))^m*W)) (original : Fin N → ZMod 2)
    (good skip : Pr P (66+K) columnCapacity prime U) (ordinaryCost : ℕ → ℕ) (ordinaryCeiling : ℕ)
    (ordinaryEffect : ℕ → (Fin N → ZMod 2) → (Fin N → ZMod 2) → Prop)
    (u : HS (66+(K+1)) columnCapacity prime U) (S : Stacks (66+(K+1)) prime)
    (fits : (36+2*m+1+(conjugationDepth m+1)*13)+3 ≤ K+1)
    (hm : prime^(w+1) < 2^data.H) (reciprocal : ∀ i, parent i * inv i = 1)
    (scan : ∀ y D, ArchiveRun (J := J) dimension vDescriptor proj parent inv data room capacity body c prefixes
      archiveTail rankFits source head length original good skip ordinaryCost ordinaryCeiling ordinaryEffect y D) :
    GeneratedArchiveRun (J := J) dimension vDescriptor proj parent inv data room capacity body c prefixes
      archiveTail rankFits source head length original good skip ordinaryCost ordinaryCeiling ordinaryEffect u S := by
  unfold GeneratedArchiveRun
  intro e physical φ live bad code schedule ready placement caller payload pending frame effect initial empty liveBits badBits
    advance exceptionalCount scratch push binaryTime initTime queueTime
  have input := initial.1
  obtain ⟨directory,widths,privateBlank,_,projector,modulus,_,_,_,unit,clock,weights,_⟩ := input
  have port (j : Fin 66) : directoryOrdinaryBank room ((Fin.castAddEmb K) j) = j.castAdd (K+1) := directoryOrdinaryBank_caller room j
  simp only [embStk,Function.comp_apply,placement,port] at directory widths projector modulus unit clock weights
  have free (i) : S.R (directoryQueueBank room fits i) = [] := by
    by_cases eq : directoryQueueBank room fits i = directoryMatrixTape room
    · rw [eq]; exact empty
    · apply ((directoryOrdinaryBank_clear_iff room S).1 privateBlank _ ?_ eq).2
      by_contra! low
      let j : Fin 66 := ⟨(directoryQueueBank room fits i).val,by omega⟩
      exact directoryQueueBank_caller room fits i j (Fin.ext rfl)
  obtain ⟨_,_,init,_,initBound,_,_,_,_,_,_,_,_,_,_,_,_,_,generate,_⟩ :=
    directoryQueueSetup_exec room fits body parent inv reciprocal hm u S liveBits free weights modulus unit clock
  obtain ⟨writer,runWriter⟩ := generate e
  obtain ⟨y,t,userY,writerTime,inputTime,write,archive,keep,clear⟩ := runWriter proj prefixes archiveTail projector
    (fun j hj => widths j (by simpa [pending] using hj)) directory
  have start := DirectoryReady.afterMatrixWriter room S _ keep clear initial.1 initial.2
  have bits (j : Fin 66) (hj : j.val < 58) := (keep j hj).2
  obtain ⟨z,B,n,next,userZ,done,history,emptyArchive,emptyLive,emptyBad,_,time,_,run⟩ :=
    scan y _ start (archive.trans (data.physical_archive e proj parent inv).symm)
      (by rw [port]; exact (bits 57 (by decide)).trans liveBits)
      (by rw [port]; exact (bits 56 (by decide)).trans badBits)
  have blankCost : (scratch.map fun i => 4*(S.L i).length+2*(S.R i).length+4).sum = 4*scratch.length := by
    have each (i) (hi : i ∈ scratch) : 4*(S.L i).length+2*(S.R i).length+4 = 4 := by
      have mem : 58 ≤ i.val ∧ i ≠ directoryMatrixTape room := by simpa [scratch] using hi
      obtain ⟨left,right⟩ := (directoryOrdinaryBank_clear_iff room S).1 privateBlank i mem.1 mem.2
      simp [left,right]
    rw [List.map_congr_left each]
    simp [Nat.mul_comm]
  have charge (p : ℕ) (bound : t ≤ init + queueTime +
      ((scratch.map fun i => 4*(S.L i).length+2*(S.R i).length+4).sum+1 + scratch.length*(6*(p*init)))) :
      t ≤ initTime + queueTime + (4*scratch.length+1 + scratch.length*(6*(p*initTime))) := by
    rw [blankCost] at bound
    exact bound.trans (Nat.add_le_add (Nat.add_le_add_right initBound _) (Nat.add_le_add_left
      (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left p initBound))) _))
  refine ⟨_,z,B,t,n,next,userZ.trans userY,done,history,emptyArchive,emptyLive,emptyBad,time,?_,?_,?_,Exec.seq write run⟩
  · intro p hp calls
    exact charge p (inputTime p (max_le_iff.mp (max_le_iff.mp hp).1).1 calls)
  · intro span V suffix extent budget p hp calls precision positive nonempty preparation
    let M := prime^(w+1)
    have Mpos : 0 < M := pow_pos Networks.Shared50ModularControl.prime_prime.pos _
    have radixPayload : M ≤ N := by
      rw [← directoryPayloadLength e length,pow_succ]
      exact (Nat.le_mul_of_pos_left _ (pow_pos Mpos d)).trans (Nat.le_mul_of_pos_right _ positive)
    have ⟨initLe,queueVolume⟩ := DirectoryReady.matrixSetup_volume (v := vDescriptor) (proj := proj) (parent := parent) (J := J) (prefixes := prefixes) (archiveTail := archiveTail) (schedule := schedule) data room S
      (by simpa only [pending,List.drop_zero] using initial.1) precision radixPayload nonempty
    have setup : t ≤ preparation := (charge p (inputTime p (max_le_iff.mp (max_le_iff.mp hp).1).1 calls)).trans
      (Nat.add_le_add (Nat.add_le_add initLe queueVolume) (Nat.add_le_add_left
        (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left p initLe))) _))
    exact ⟨setup,fun parents baseline count weight ceiling =>
      Nat.add_le_add setup (time parents baseline count precision weight ceiling)⟩
  · intro p parents baseline hp calls count precision weight positive ceiling width
    have Mpos : 0 < prime^(w+1) := pow_pos Networks.Shared50ModularControl.prime_prime.pos _
    have radix : prime^(w+1) ≤ N := by
      rw [← directoryPayloadLength e length,pow_succ]
      exact (Nat.le_mul_of_pos_left _ (pow_pos Mpos d)).trans (Nat.le_mul_of_pos_right _ positive)
    have queueBound : queueTime ≤ data.records*((12*m*m+4)*width+directoryMatrixRate m d*N)+4 := by
      dsimp only [queueTime]
      rw [precision]
      exact (directoryMatrixQueueTime_binary_le ..).trans (Nat.add_le_add_right
        (Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.mul_le_mul_left _ radix) _)) _)
    have setup := charge p (inputTime p (max_le_iff.mp (max_le_iff.mp hp).1).1 calls)
    exact Nat.add_le_add (setup.trans (Nat.add_le_add_right (Nat.add_le_add_left queueBound _) _))
      (time parents baseline count precision weight ceiling)

open IntegerMultBounds.MathlibTM2.Fast.Main in
/-- Run the generated directory frame with its physical exceptional projector and shared matrix archive. -/
theorem DirectoryReady.runArchive [M8.Machine.Net] {m d K w W J N : ℕ} {P U : Type}
    (dimension : m+m = d+1) (vDescriptor : Descriptor) (proj : Matrix (Fin m) (Fin m) ℚ)
    (idem : proj*proj = proj) (adm : Admissible prime proj)
    (parent inv : Fin m → ZMod (prime^(w+1))) (reciprocal : ∀ i, parent i * inv i = 1)
    (data : ScanData m d w W) (hm : prime^(w+1) < 2^data.H) (hw : W < 2^J) (positive : 0 < W)
    (room : Record.size d+(rowSwapBlock.tapes+35+2) ≤ K+1)
    (capacity : (anchorProgram d true).1+(anchorProgram d false).1+1 ≤ columnCapacity)
    (body : P → Pr P (66+(K+1)) columnCapacity prime U) (c : ℕ) (bodyBound : ∀ f, mnProgPush (body f) ≤ c)
    (prefixes : ℕ → List (Fin (prime+4))) (archiveTail : List (Fin (prime+4)))
    (factor : Factorization univ univ proj) (small : ∀ k ∈ factorizationDenominators factor, k < prime)
    (rankFits : proj.rank ≤ m)
    (source : ℤ → Fin 4) (head : ℤ) (length : N = (prime^(w+1))^m*((prime^(w+1))^m*W)) (original : Fin N → ZMod 2)
    (u : HS (66+(K+1)) columnCapacity prime U) (S : Stacks (66+(K+1)) prime) :
    let e := finSumFinEquiv.trans (finCongr dimension)
    let physical := data.physical e proj parent inv
    let φ := LabelRing.res prime (w+1) (by omega)
    let live := LabelStock.live m (w+1) 1
    let bad := fun j => fallbackBit rankFits (reduce (prime^(w+1)) proj) (physicalLabel m (w+1) j)
    let code := fun k => residualSchedule (A := prime) (projectorResidual finSumFinEquiv (reduce prime proj)
      (φ ∘ parent) (φ ∘ inv) (LabelStock.residue m (w+1) 1 k))
    let schedule := fun (xs : List ℕ) => xs.flatMap fun k => if bad k then code k else []
    let ready := DirectoryReady vDescriptor proj w W data.H J parent prefixes archiveTail schedule
    let placement := directoryOrdinaryBank room
    let caller := Fin.castAddEmb (n := 66) K
    let payload := RecordPayload (N := N) (caller 24) source head
    let pending := fun j => (List.range data.records).drop j
    let frame := fun j word D => ready D (pending j) ∧ payload word D
    let costBad := fun j =>
      let C := physical.table (LabelStock.residue m (w+1) 1 j)
      let rows := classPivots C
      let scratch := (List.finRange (66+(K+1))).filter fun i => decide (58 ≤ i.val ∧ i ≠ directoryMatrixTape room)
      exceptionalRecordTime U rows (negativeAnchor rows C) m w W data.H J scratch.length
        (max (mnProgPush (directoryExceptionalCore (P := P) (U := U) d room capacity)) c) (prefixes j).length
    ∀ (localBody : P → Pr P (66+K) columnCapacity prime U)
      (calls : ∀ f, body f = embProg placement id (localBody f))
      (good skip : Pr P (66+K) columnCapacity prime U) (ordinaryCost : ℕ → ℕ) (ordinaryCeiling : ℕ)
      (ordinaryEffect : ℕ → (Fin N → ZMod 2) → (Fin N → ZMod 2) → Prop),
    let effect := fun j (x y : Fin N → ZMod 2) => if live j && bad j then
      ∀ a k, y ((FlatCoordinateLayout.index ((projectorResidual e (reduce (prime^(w+1)) proj) parent inv
        (physicalLabel m (w+1) j)).mulVec a) k).cast (directoryPayloadLength e length)) =
        x ((FlatCoordinateLayout.index a k).cast (directoryPayloadLength e length))
      else ordinaryEffect j x y
    (∀ j, (prefixes j).length = (prefixes 0).length →
      max (4*(prefixes j).length) (ordinaryCost j) ≤ ordinaryCeiling) →
    (∀ j labels word v S, ¬ (live j = true ∧ bad j = true) → ready S (j :: labels) → payload word S →
      ∃ z D n next, z.user = v.user ∧ n ≤ ordinaryCost j ∧
        Exec localBody (if live j then good else skip) (mk v S) n (mk z D) ∧ ready D labels ∧
        ordinaryEffect j word next ∧ payload next D ∧ D.R (caller 57) = S.R (caller 57) ∧ D.R (caller 56) = S.R (caller 56)) →
    ArchiveRun (J := J) dimension vDescriptor proj parent inv data room capacity body c prefixes archiveTail
      rankFits source head length original good skip ordinaryCost ordinaryCeiling ordinaryEffect u S := by
  intro e physical φ live bad code schedule ready placement caller payload pending frame costBad localBody calls
    good skip ordinaryCost ordinaryCeiling ordinaryEffect effect ceiling ordinary
  unfold ArchiveRun
  dsimp only
  intro start queue liveBits badBits
  have release (port : Fin 66) (lo : 56 ≤ port.val) (hi : port.val ≤ 57) j x D bits (h : frame j x D) :
      frame j x {D with R := Function.update D.R (caller port) bits} := by
    refine ⟨DirectoryReady.updateSelector port lo hi bits h.1,?_⟩
    have ne : caller 24 ≠ caller port := caller.injective.ne (by intro eq; subst port; contradiction)
    simpa only [payload,RecordPayload,Function.update_of_ne ne] using h.2
  obtain ⟨z,B,n,user,⟨⟨next,history,done⟩,tail⟩,mask,mode,bound,time,run⟩ :=
    physical.classifiedArchive_exec room id proj idem factor small rankFits localBody body calls good skip
      (directoryExceptionalProgram m d room capacity) ordinaryCost costBad original effect frame
      (fun j x D k bits sel h => by rcases sel with rfl | rfl
                                    · exact release 57 (by decide) (by decide) j x D bits h
                                    · exact release 56 (by decide) (by decide) j x D bits h)
      (by
        intro j inside no x v D h
        change j < data.records at inside
        change ¬ (live j = true ∧ bad j = true) at no
        have index : j < (List.range data.records).length := by simpa using inside
        have suffix : pending j = j :: pending (j+1) := by
          simpa only [List.getElem_range] using (List.getElem_cons_drop index).symm
        obtain ⟨z,B,n,y,user,time,run,done,action,out,mask,mode⟩ :=
          ordinary j _ x v D no (suffix ▸ h.1) h.2
        exact ⟨y,z,B,n,user,by simpa [effect,no] using action,⟨done,out⟩,mask,mode,
          by change (B.R ((Fin.castAddEmb K) 2)).length = data.H; rw [done.2.2.2.2.2.1,length_binSyms],(done.2.2.1 _ (by decide : 58 ≤ 59)).2,time,run⟩)
      (by
        intro j inside liveJ badJ x v D h matrix
        change live j = true at liveJ
        change bad j = true at badJ
        obtain ⟨z,B,n,y,user,time,run,done,tail,action,out,mask,mode⟩ :=
          DirectoryReady.runExceptional dimension vDescriptor proj idem adm parent inv reciprocal data hm hw positive
            room capacity body c bodyBound prefixes archiveTail bad j inside liveJ badJ source head length x v D h.1 matrix h.2
        exact ⟨y,z,B,n,user,by simpa [effect,liveJ,badJ] using action,⟨done,out⟩,tail,
          by rw [directoryOrdinaryBank_caller]; exact mask,
          by rw [directoryOrdinaryBank_caller]; exact mode,time,run⟩)
      u S start queue liveBits badBits
  refine ⟨z,B,n,next,user,done,history,tail,mask,mode,bound,?_,time,run⟩
  intro parents baseline shape hWidth jWidth fits
  let scratch := (List.finRange (66+(K+1))).filter fun i => decide (58 ≤ i.val ∧ i ≠ directoryMatrixTape room)
  let push := max (mnProgPush (directoryExceptionalCore (P := P) (U := U) d room capacity)) c
  let extra := exceptionalVolumeRate U d m scratch.length push w*N
  let count := ((∑ k ∈ Finset.range proj.rank, (k+1)*(m+1))*data.records)/prime
  have volumeEq := directoryPayloadLength e length
  have localPrice (j : ℕ) (inside : j < data.records) :
      max (4*(prefixes j).length) (ordinaryCost j) ≤ ordinaryCeiling := by
    have widths := start.1.2.1
    simp only [List.drop_zero,List.mem_range] at widths
    exact ceiling j ((widths j inside).symm.trans (widths 0 (by omega)))
  apply bound parents baseline (data.records*(baseline+6)+2+count*extra) shape (Nat.le_add_right ..)
  · intro j hj no
    exact Or.inr ⟨hWidth,positive,volumeEq ▸ (Nat.add_le_add_right ((Nat.le_max_right ..).trans (localPrice j hj)) N).trans fits⟩
  · intro pos j hj _ _
    change 0 < count at pos
    change costBad j ≤ baseline + (data.records*(baseline+6)+2+count*extra-(data.records*(baseline+6)+2))/count
    rw [Nat.add_sub_cancel_left,Nat.mul_div_cancel_left _ pos]
    have prefixBound : 4*(prefixes j).length ≤ baseline :=
      ((Nat.le_max_left ..).trans (localPrice j hj)).trans ((Nat.le_add_right ..).trans fits)
    let C := physical.table (LabelStock.residue m (w+1) 1 j)
    have price := exceptionalVolumeRate_bound U d m scratch.length push w W (prefixes j).length
      (classPivots C) (negativeAnchor (classPivots C) C) positive
    change exceptionalRecordTime U (classPivots C) _ m w W data.H J scratch.length push _ ≤ _
    rw [hWidth,jWidth]
    exact price.trans ((Nat.add_le_add_left prefixBound _).trans_eq (by rw [volumeEq,Nat.add_comm]))

private theorem ordinaryCharge_le {width padding good ceiling : ℕ} (live : Bool)
    (prefixBound : 4*width ≤ padding) (cheap : padding ≤ good) (same : good = ceiling) :
    max (4*width) (if live then good else padding) ≤ ceiling := by
  cases live <;> simp only [Bool.false_eq_true,ite_false,ite_true,max_le_iff] <;> omega

private theorem classifiedStep {α β : Type*} (ok : ℕ → α → β → Prop) (live bad : Bool)
    (gc bc pc : ℕ) (g b p : α) (ge be pe : β)
    (ordinary : ¬ (live = true ∧ bad = true) → ok (if live then gc else pc)
      (if live then g else p) (if live then ge else pe))
    (repair : live = true → bad = true → ok bc b be) :
    ok (if live then (if bad then bc else gc) else pc)
      (if live then (if bad then b else g) else p) (if live then (if bad then be else ge) else pe) := by
  cases live <;> cases bad <;> simp_all

open RingFormula LabelTraversal IntegerMultBounds.MathlibTM2.Fast.Main

/-- Shared directory layout, program and prices. The single-record statement also
places the ordinary program beside the matrix stream used by the exceptional branch. -/
def GeneratedRecordSpec [M8.Machine.Net] {T m work Q fields H J W : ℕ} {F U : Type}
    (v : Descriptor) (positive : v.Positive) (w : ℕ) (proj : Matrix (Fin m) (Fin m) ℚ)
    (width : v.width = proj.rank*(w+1)) (idem : proj*proj = proj)
    (factor : Factorization univ univ proj) (hd : ∀ a ∈ factorizationDenominators factor, a < prime)
    (rankFits : proj.rank ≤ m) (parent parentInv : Fin m → ZMod (prime^(w+1)))
    (reciprocal : ∀ i, parent i * parentInv i = 1)
    (io : Fin T) (arity : ℕ)
    (hm : prime^(w+1) < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (length : volume prime v = (prime^(w+1))^fields*((prime^(w+1))^fields*W))
    (capacity : 217 ≤ Q) (source : ℤ → Fin 4) (head : ℤ)
    (fits : LeafCore.small ≤ work) (cap : (LeafCore.core io).states ≤ Q) (single : Bool) : Prop :=
    let d := proj.rank
    let common := CommonBank.count T
    let host := common+24
    let M := prime^(w+1)
    let N := volume prime v
    let entry : Graph.Block common prime := Blocks.seqB LeafRoutines.offsets (Blocks.seqB Blocks.push LeafRoutines.view)
    let leave : Graph.Block common prime := Blocks.seqB Blocks.restore LeafRoutines.advance
    let record := (Fin.natAddEmb common (m := 24)).trans ((Fin.castAddEmb 31).trans (Fin.castAddEmb work))
    let bank := (Fin.castLEEmb (by decide : 23 ≤ 24)).trans record
    let commonPorts := ((Fin.castAddEmb (n := common) 24).trans (Fin.castAddEmb 31)).trans (Fin.castAddEmb work)
    let aux := (⟨CommonBank.auxSlot,by
      intro i j eq
      apply Fin.ext
      have h := congrArg Fin.val eq
      simp only [CommonBank.auxSlot_val] at h
      omega⟩ : Fin 24 ↪ Fin common).trans commonPorts
    let hdrPorts := (⟨CommonBank.headerSlot,by
      intro i j eq
      apply Fin.ext
      have h := congrArg Fin.val eq
      simp only [CommonBank.headerSlot_val] at h
      omega⟩ : Fin 6 ↪ Fin common).trans commonPorts
    let logical := {v with width := d}
    let addr := fun a row pre mid post (x : IntegerMultBounds.Swap.Shear.State (Fin d) (ZMod M)) =>
      index M logical a row pre (FlatCoordinateLayout.rank x.1).val mid (FlatCoordinateLayout.rank x.2).val post
    let inner := Fin.natAddEmb 66 (m := (host+31)+work)
    let caller := Fin.castAddEmb (n := 66) ((host+31)+work)
    let K := 66+((host+31)+work)
    ∀ (ef : entry.tapes ≤ common+work) (xf : leave.tapes ≤ common+work)
      (eqs : entry.states ≤ Q) (xqs : leave.states ≤ Q) (word : Fin N → ZMod 2) (body : F → Pr F K Q prime U)
      (u : HS _ Q prime U) (whole : Stacks K prime),
      ∀ (poolFits : (conjugationDepth m+1)*13 ≤ work)
        (directory : Descriptor) (prefixes : ℕ → List (Fin (prime+4))) (archiveTail : List (Fin (prime+4))),
      let labels := List.range (LabelMask.records directory)
      let slots : Fin 7 ↪ Fin 58 := ⟨![45,46,2,47,48,44,49],by decide⟩
      let headers := (Fin.castAddEmb (n := 6) 1).trans slots
      let scanCaller := goodRecordScanPorts.trans slots
      let scan := (scanCaller.trans (Fin.castAddEmb 8)).trans caller
      let joined := recordLoaderBank record
      let dirSlots := goodRecordDirectoryPorts headers
      let dir := dirSlots.trans joined
      let pool := ((Fin.castLEEmb poolFits).trans (Fin.natAddEmb (host+31))).trans inner
      let pivot := goodRecordPivotPorts.trans joined
      let counters := goodRecordCounterPorts.trans joined
      let inputs := sourcePorts (m := m) (QueueLayout.formulaInputs.trans dir) id
      let ports := QueueLayout.normalizationPorts.trans pivot
      let a := QueueLayout.readPorts.trans (QueueLayout.directoryWork.trans dir)
      let digits := QueueLayout.digitPorts.trans (QueueLayout.directoryWork.trans dir)
      let prefixWidth := dir 12
      let zeros := dir 9
      let packedLabel := dir 10
      let clock := counters 0
      let count := counters 1
      let formula := fun i j : Fin m => numerator (matrixInput false) (matrixInput true) i j
      let detFormula := determinant (matrixInput (m := m) false)
      let generation := fun label => recordConjugationTime m w H (prefixes label).length
      let generate : Pr F K Q prime U := (.seq (readWithSuccessorClock clock (directoryMatrix m a digits prefixWidth zeros packedLabel)) (.seq (.seq (.seq (compile (readLeaf (leafBank inputs)) (registerBank pool) detFormula 0 (pivot 14)) (reusablePivotInverse prime pivot clock count))
        (.seq (packedConjugate pool inputs ports false true) (.seq (bclear (pivot 0)) (bclear (pivot 14))))) (bclear packedLabel)))
      let withZero := (Node.umulSym 1 (bitSymbol false) (dir 8) zeros (dir 4)).seq (generate.seq (bclear zeros))
      let field := fun i => caller ((headers i).castAdd 8)
      let slot := (((LeafCore.roleSlot io).castAdd 24).castAdd 31).castAdd work
      let r := recordRoundTripPorts slot
      let src := fun i : Fin 6 => caller ((i.natAdd 33).castLE (by decide : 39 ≤ 66))
      let dst := hdrPorts.trans inner
      let g := physicalLabel m (w+1)
      let G := fun label => g label*reduce M proj*(g label)⁻¹
      let liveBit := LabelStock.live m (w+1) 1
      let badBit := fun label => fallbackBit rankFits (reduce M proj) (g label)
      let φ := LabelRing.res prime (w+1) (by omega)
      let table := projectorResidual (finSumFinEquiv : (Fin m ⊕ Fin m) ≃ Fin (m+m))
        (reduce prime proj) (φ ∘ parent) (φ ∘ parentInv)
      let fallbackCode := fun j => residualSchedule (A := prime) (table (LabelStock.residue m (w+1) 1 j))
      let schedules := fun (pending : List ℕ) => pending.flatMap fun j =>
        if badBit j then fallbackCode j else []
      let ready := DirectoryReady v proj w W H J parent prefixes archiveTail schedules (K := (host+31)+work)
      let payload := RecordPayload (N := N) (r 0) source head
      let call := fun i : Fin d => packedCoordinateProgram (F := Empty) (U := U) io i.val i.val ef xf fits eqs xqs cap
      let cost := packedCoordinatesTime d N w (LeafCore.core io).tapes
        (packedLeafPush (F := Empty) (U := U) io Empty.elim) entry.tapes leave.tapes
      let budget := pivotSetupTime m d w M.size + cost
      let coordinate := (goodWeights prime d rankFits bank).seq (Prog.seqList ((List.finRange d).reverse.map call))
      let effect := fun label (word next : Fin N → ZMod 2) =>
        ∃ minor : ∀ k (hk : k < d), IsUnit (GoodForm.lead (k+1) (lt_of_lt_of_le hk rankFits) (G label)).det,
        let stage := GoodForm.stageAt (G label) d rankFits minor d le_rfl
        let pivot := fun i : Fin d => stage.M (i.castLE rankFits) (i.castLE rankFits)
        let weight := fun i : Fin d => parent (i.castLE rankFits)*pivot i
        let inv := fun i : Fin d => parentInv (i.castLE rankFits)*Ring.inverse (pivot i)
        ∀ a < v.beforeRows, ∀ row < v.rows, ∀ pre < v.beforeH, ∀ mid < v.between, ∀ post < v.afterD, ∀ x,
            ext next (addr a row pre mid post (Weighted.child d weight inv x)) = ext word (addr a row pre mid post x)
      let reverse := (Equiv.swap (0 : Fin 8) 1).toEmbedding.trans r
      let transfer := fun ports : Fin 8 ↪ Fin K => (stateLiftNormalize capacity (by decide)).seq
        (stateLiftPr capacity (by decide) Empty.elim (returnFromOrigin (P := Empty) ports))
      let marks := ([2,3,4,5,6,7] : List (Fin 8)).map r
      let loading := recordWeightLoadTime m w H M.size
      let conversion := recordMatrixLoadTime m H M.size
      let headerCost := descriptorHeaderCost v
      let raw := ((dimensionTime H 1 fields+(4*(fields*H+1)+6)+(10*J+12)+(6*(M^fields).size+6)) +
        (loading+(conversion+(budget+2*((218*N+1)*13+6)+3))))
      let tripCost := if 0 < d ∧ H = M.size ∧ J = W.size then min raw (budget+recordRoundTripRate m*N) else raw
      let runCost := fun label => generatedRecordTime m w H (prefixes label).length headerCost tripCost
      let prepareCounters := (swapExponent (leafCounterPorts aux)).seq
        (.act (installLeafCounters (aux.trans inner) arity d))
      let prepareHeaders := (Record.copyLeafHeaders src dst (caller 64) (caller 65) (List.finRange 6)).seq (.act (pushMarkers ((List.finRange 6).map dst)))
      let recordProgram : Pr F K Q prime U := (((((initFrames pool (pivot 4) (conjugationDepth m+1)).seq (withZero.seq (clearFrames pool (conjugationDepth m+1)))).seq prepareCounters |>.seq prepareHeaders).seq ((recordCounterSetup caller fields).seq ((recordInputProgram record m).seq ((recordMatrixProgram record m).seq ((.act (pushMarkers marks) : Pr F K Q prime U).seq
          ((transfer r).seq ((embProg inner Empty.elim coordinate).seq (transfer reverse)))))))).seq (readWithSuccessorClock (scan 1) (advanceDirectory m scan)))
      let privateTapes := (List.finRange K).filter fun i => decide (58 ≤ i.val)
      let initialClear := privateTapes.length*4+1
      ∀ c, (∀ f, mnProgPush (body f) ≤ c) →
      let charge := fun label => runCost label + (initialClear + 6*(max (mnProgPush recordProgram) c * runCost label))
      let binaryRun := budget + recordRoundTripRate m*N + (12*m*m+4)*(prefixes 0).length + generatedRecordRate m*N
      let binaryCharge := binaryRun + (initialClear + 6*(max (mnProgPush recordProgram) c * binaryRun))
      let mask := caller 57
      let mode := caller 56
      let modes := fun (js : List ℕ) => js.map (fun i => bitSymbol (a := prime) (badBit i))
      let skip := readWithSuccessorClock (scan 1) (advanceDirectory m scan)
      let skipCost := fun i => 1+(4*(prefixes i).length+4+(m*m*(4*(w+1)+4)+1)+1)
      let ordinaryStep := ∀ label labels word (u : HS K Q prime U) (S : Stacks K prime),
        ¬ (liveBit label = true ∧ badBit label = true) → ready S (label :: labels) → payload word S →
        ∃ z D n next, z.user = u.user ∧ n ≤ (if liveBit label then charge label else skipCost label) ∧
          Exec body (if liveBit label then recordProgram.seq (clearWorkTapes privateTapes) else skip)
            (mk u S) n (mk z D) ∧ ready D labels ∧
          (if liveBit label then effect label else Eq) word next ∧ payload next D ∧
          D.R mask = S.R mask ∧ D.R mode = S.R mode
      if single then ordinaryStep ∧ (
        ∀ (dimension : ℕ) (data : ScanData m dimension w W) (room : Record.size dimension+(rowSwapBlock.tapes+35+2) ≤ (host+31+work)+1),
        let placement := directoryOrdinaryBank room
        let archive := directoryMatrixTape room
        ∀ (outer : F → Pr F (66+((host+31+work)+1)) Q prime U)
          (calls : ∀ f, outer f = embProg placement id (body f))
          (label : ℕ) (labels : List ℕ) (word : Fin N → ZMod 2) (u : HS _ Q prime U) (S : Stacks _ prime),
          data.H = H → label < data.records → ¬ (liveBit label = true ∧ badBit label = true) →
          ready (embStk placement S) (label :: labels) → payload word (embStk placement S) →
          S.R archive = data.matrices label →
          let program := if liveBit label then recordProgram.seq (clearWorkTapes privateTapes) else skip
          let advance := dropWords (placement (caller 2)) archive (placement (caller 59)) ((dimension+1)*(dimension+1))
          ∃ z D n next, z.user = u.user ∧ n ≤ (if liveBit label then charge label else skipCost label) +
            ((dimension+1)*(dimension+1)*(4*H+4)+1) ∧
            Exec outer ((embProg placement id program).seq advance) (mk u S) n (mk z D) ∧
            ready (embStk placement D) labels ∧ (if liveBit label then effect label else Eq) word next ∧
            payload next (embStk placement D) ∧ D.R archive = data.matrices (label+1) ∧
            D.R (placement mask) = S.R (placement mask) ∧ D.R (placement mode) = S.R (placement mode)) ∧
        ∀ (dimension : ℕ) (shape : m+m = dimension+1) (data : ScanData m dimension w W)
          (room : Record.size dimension+(rowSwapBlock.tapes+35+2) ≤ (host+31+work)+1)
          (anchor : (anchorProgram dimension true).1+(anchorProgram dimension false).1+1 ≤ columnCapacity)
          (states : Q = columnCapacity) (fieldsEq : fields = m) (binary : data.H = H)
          (outer : F → Pr F (66+((host+31+work)+1)) columnCapacity prime U)
          (calls : ∀ f, outer f = embProg (directoryOrdinaryBank room) id (states ▸ body f))
          (push : ℕ) (bounded : ∀ f, mnProgPush (outer f) ≤ push)
          (u : HS _ columnCapacity prime U) (S : Stacks _ prime),
          ArchiveRun (J := J) shape v proj parent parentInv data room anchor outer push prefixes archiveTail rankFits
            source head (fieldsEq ▸ length) word (states ▸ recordProgram.seq (clearWorkTapes privateTapes))
            (states ▸ skip) (fun j => if liveBit j then charge j else skipCost j)
            (if 0 < d ∧ H = M.size ∧ J = W.size then min (charge 0) binaryCharge else charge 0)
            (fun j => if liveBit j then effect j else Eq) u S ∧
          ((36+2*m+1+(conjugationDepth m+1)*13)+3 ≤ (host+31+work)+1 →
          GeneratedArchiveRun (J := J) shape v proj parent parentInv data room anchor outer push prefixes archiveTail rankFits
            source head (fieldsEq ▸ length) word (states ▸ recordProgram.seq (clearWorkTapes privateTapes))
            (states ▸ skip) (fun j => if liveBit j then charge j else skipCost j)
            (if 0 < d ∧ H = M.size ∧ J = W.size then min (charge 0) binaryCharge else charge 0)
            (fun j => if liveBit j then effect j else Eq) u S)
      else
      ∀ (room : m*m+m*m ≤ (host+31)+work) (B : ℕ),
      let rs := residuePairs (m*m) room
      let parents := caller 50
      directory.beforeH = B*prime^(m*((w+1)*m)) →
      (∀ i : Fin K, 58 ≤ i.val → whole.R i = []) →
      directory.Positive → (whole.R (caller 29)).length = directory.beforeRows →
      (whole.R (caller 30)).length = directory.rows → (whole.R (caller 31)).length = directory.beforeH →
      whole.R parents = [] →
      whole.R mask = [] → whole.R mode = [] → whole.R (caller 54) = [] →
      let high := prime^w
      let initCounters : Pr F K Q prime U := (Node.expProg 0 prime (caller 28) (caller 45) (caller 58) (caller 59) (caller 60) (caller 61)).seq
        (Node.scanR (caller 58) (caller 59) (LabelCountBank.pushAll (rs.map Prod.fst)))
      let clean := {whole with L := fun i => if i ∈ privateTapes then [] else whole.L i,
                               R := fun i => if i ∈ privateTapes then [] else Function.update whole.R (caller 54) (schedules labels) i}
      ready clean labels →
      let setupCost := (26*high+4) + ((44*labels.length+13*(w+1)+16) + 3*((6+10*(m*m))*labels.length+4) +
        (2*(directory.beforeRows*directory.rows*B)+2)) +
        ((privateTapes.map fun i => 4*(whole.L i).length).sum + privateTapes.length*(2*high+4)+1)
      ∃ writer : Pr F K Q prime U, let prepare := (initCounters.seq writer).seq (clearWorkTapes privateTapes)
      ∃ z D n, z.user = u.user ∧ n ≤ setupCost ∧ Exec body prepare (mk u whole) n (mk z D) ∧
        ready D labels ∧ ordinaryStep ∧ D.L (r 0) = whole.L (r 0) ∧ D.R (r 0) = whole.R (r 0) ∧
        D.R (caller 48) = whole.R (caller 48) ∧ D.R mask = labels.map (fun j => bitSymbol (liveBit j)) ∧ D.R mode = modes labels ∧
        (∀ (dimension : ℕ) (archiveRoom : Record.size dimension+(rowSwapBlock.tapes+35+2) ≤ (host+31+work)+1),
          let placement := directoryOrdinaryBank archiveRoom
          let archive := directoryMatrixTape archiveRoom
          ∀ (outer : F → Pr F (66+((host+31+work)+1)) Q prime U)
            (calls : ∀ f, outer f = embProg placement id (body f)) (initial : HS _ Q prime U) (B : Stacks _ prime),
            embDn placement initial = u → embStk placement B = whole →
            ∃ y E, y.user = initial.user ∧ embStk placement E = D ∧ E.R archive = B.R archive ∧
              Exec outer (embProg placement id prepare) (mk initial B) n (mk y E) ∧
              (payload word clean → ∀ (data : ScanData m dimension w W) (shape : m+m = dimension+1)
                (anchor : (anchorProgram dimension true).1+(anchorProgram dimension false).1+1 ≤ columnCapacity)
                (states : Q = columnCapacity) (fieldsEq : fields = m)
                (extra : (36+2*m+1+(conjugationDepth m+1)*13)+3 ≤ (host+31+work)+1)
                (push : ℕ), (∀ f, mnProgPush (outer f) ≤ push) →
                data.H = H → data.records = LabelMask.records directory → B.R archive = [] →
                let scanBody : F → Pr F _ columnCapacity prime U := states ▸ outer
                let e := finSumFinEquiv.trans (finCongr shape)
                let action := fun j (x y : Fin N → ZMod 2) => if liveBit j && badBit j then
                  ∀ a k, y ((FlatCoordinateLayout.index ((projectorResidual e (reduce M proj) parent parentInv
                    (physicalLabel m (w+1) j)).mulVec a) k).cast (directoryPayloadLength e (fieldsEq ▸ length))) =
                    x ((FlatCoordinateLayout.index a k).cast (directoryPayloadLength e (fieldsEq ▸ length)))
                  else (if liveBit j then effect j else Eq) x y
                ∃ (archivePass : Pr F _ columnCapacity prime U), ∃ finish final steps next,
                  finish.user = initial.user ∧ ready (embStk placement final) [] ∧ payload next (embStk placement final) ∧
                  labels.foldl (fun history j y => ∃ x, history x ∧ action j x y) (· = word) next ∧
                  final.R archive = [] ∧ final.R (placement mask) = [] ∧ final.R (placement mode) = [] ∧
                  (H = M.size → J = W.size →
                    let baseline := (if 0 < d then min (charge 0) binaryCharge else charge 0) + N
                    let V := data.records*max (prefixes 0).length N
                    let suffix := (whole.R (caller 48)).drop (m*m*H)
                    let budget := directoryQueueInitRate m dimension*((1+m*m)*V+archiveTail.length+suffix.length)
                    let work := (List.finRange (66+(host+31+work+1))).filter fun i => decide (58 ≤ i.val ∧ i ≠ archive)
                    let p := max (mnProgPush archivePass) push
                    let setup := budget + ((12*m*m+4+directoryMatrixRate m dimension)*V+4) +
                      (4*work.length+1+work.length*(6*(p*budget)))
                    let labels := ∑ k ∈ Finset.range d, (k+1)*(m+1)
                    let rate := exceptionalVolumeRate U dimension m work.length
                      (max (mnProgPush (directoryExceptionalCore (P := F) (U := U) dimension archiveRoom anchor)) push) w
                    let left := (privateTapes.map fun i => 4*(whole.L i).length).sum
                    let controls := left + (140+30*(m*m)+6*privateTapes.length)*(data.records*N)
                    let overhead := controls+setup
                    let power := (v.width : ℝ)^M8.Machine.BudgetBound.tau / (d : ℝ)^M8.Machine.BudgetBound.tau
                    let ordinary := (1+6*(max (mnProgPush recordProgram) c : ℕ)) *
                        ((directoryCoordinateRateAt m d (LeafCore.core io).tapes
                          (packedLeafPush (F := Empty) (U := U) io Empty.elim) entry.tapes leave.tapes power +
                          (recordRoundTripRate m + generatedRecordRate m : ℕ))*N +
                          ((12*m*m+4)*(prefixes 0).length : ℕ)) + initialClear + N
                    let rare := exceptionalRateAt U dimension m work.length
                      (max (mnProgPush (directoryExceptionalCore (P := F) (U := U) dimension archiveRoom anchor)) push) power
                    let terminal := fun batchVolume : ℕ => (overhead : ℝ) + data.records*(ordinary+6) + 2 +
                      ((labels : ℝ)/prime)*rare*batchVolume
                    (0 < d → (baseline : ℝ) ≤ ordinary ∧ ((n+steps : ℕ) : ℝ) ≤ terminal (data.records*N) ∧
                      ∀ (ι : Type) (gap adapter : ι → ℕ) (time : List ι → Descriptor → ℕ)
                        (chain : List ι) (root : Descriptor),
                        (∀ i is parent, gap i ≤ parent.width → time (i :: is) parent ≤
                          time is (rankDescriptor prime (parent.width-gap i) (gap i) parent) +
                            adapter i*volume prime parent) →
                        (chain.map gap).sum ≤ root.width →
                        rankDescriptor prime (root.width-(chain.map gap).sum) (chain.map gap).sum root = directory →
                        time [] directory ≤ n+steps →
                        ∀ suffixWidth, directory.width = m*(w+1)+suffixWidth →
                        W = prime^(2*suffixWidth)*directory.between*directory.afterD →
                        (time chain root : ℝ) ≤ terminal (volume prime root) + (chain.map adapter).sum*volume prime root) ∧
                    n+steps ≤ overhead + (data.records*(baseline+6)+2 + (labels*data.records/prime)*(rate*N)) ∧
                      ((n+steps : ℕ) : ℝ) ≤ overhead + data.records*(baseline+6) + 2 +
                        ((labels : ℝ)/prime)*rate*(data.records*N)) ∧
                  Exec scanBody ((states ▸ embProg placement id prepare).seq archivePass)
                    (mk (states ▸ initial) B) (n+steps) (mk finish final))) ∧
      ∀ (_ : payload word clean) (fallback : Pr F K Q prime U) (badCost : ℕ → ℕ) (badEffect : ℕ → (Fin N → ZMod 2) → (Fin N → ZMod 2) → Prop),
      (∀ i is word (u : HS K Q prime U) (S : Stacks K prime), LabelStock.live m (w+1) 1 i = true → fallbackBit rankFits (reduce M proj) (g i) = true → ready S (i :: is) → payload word S →
        ∃ z D n next, z.user = u.user ∧ n ≤ badCost i ∧ Exec body fallback (mk u S) n (mk z D) ∧
          ready D is ∧ badEffect i word next ∧ payload next D ∧ D.R mask = S.R mask ∧ D.R mode = S.R mode) →
      let branchCost := fun i => if liveBit i then (if badBit i then badCost i else charge i) else skipCost i
      let action := fun i => if liveBit i then (if badBit i then badEffect i else effect i) else Eq
      let exceptional := ((∑ k ∈ Finset.range d, (k+1)*(m+1))*labels.length)/prime
      let priced := fun n => ∀ baseline parentBudget : ℕ,
        (charge 0 ≤ baseline ∨ (0 < d ∧ H = M.size ∧ J = W.size ∧ binaryCharge ≤ baseline)) →
        let ordinary := setupCost + labels.length*(baseline+6) + 2
        ordinary ≤ parentBudget →
        (0 < exceptional → ∀ j ∈ labels, liveBit j = true → badBit j = true →
          badCost j ≤ baseline + (parentBudget-ordinary)/exceptional) →
        n ≤ parentBudget
      ∃ z D n next, z.user = u.user ∧ n ≤ setupCost + ((labels.map fun i => branchCost i + 2 + 4).sum + 2) ∧
        priced n ∧ Exec body (((initCounters.seq writer).seq (clearWorkTapes privateTapes)).seq (classifiedScan mask mode (recordProgram.seq (clearWorkTapes privateTapes)) fallback skip)) (mk u whole) n (mk z D) ∧
        (ready D [] ∧ D.R mode = modes []) ∧ D.R mask = [] ∧ payload next D ∧
        labels.foldr (fun i rest x => ∃ y, action i x y ∧ rest y) (· = next) word

/-- Generate one live record's conjugated projector, restoring the formula pool. -/
noncomputable def directoryRecordWriter {F U : Type} {Q work : ℕ} (m common : ℕ)
    (poolFits : (conjugationDepth m+1)*13 ≤ work) : Pr F (66+(common+24+31+work)) Q prime U :=
  let host := common+24
  let record := (Fin.natAddEmb common (m := 24)).trans ((Fin.castAddEmb 31).trans (Fin.castAddEmb work))
  let inner := Fin.natAddEmb 66 (m := host+31+work)
  let caller := Fin.castAddEmb (n := 66) (host+31+work)
  let K := 66+(host+31+work)
  let slots : Fin 7 ↪ Fin 58 := ⟨![45,46,2,47,48,44,49],by decide⟩
  let headers := (Fin.castAddEmb (n := 6) 1).trans slots
  let joined := recordLoaderBank record
  let dirSlots := goodRecordDirectoryPorts headers
  let dir := dirSlots.trans joined
  let pool := ((Fin.castLEEmb poolFits).trans (Fin.natAddEmb (host+31))).trans inner
  let pivot := goodRecordPivotPorts.trans joined
  let counters := goodRecordCounterPorts.trans joined
  let inputs := sourcePorts (m := m) (QueueLayout.formulaInputs.trans dir) id
  let ports := QueueLayout.normalizationPorts.trans pivot
  let a := QueueLayout.readPorts.trans (QueueLayout.directoryWork.trans dir)
  let digits := QueueLayout.digitPorts.trans (QueueLayout.directoryWork.trans dir)
  let prefixWidth := dir 12
  let zeros := dir 9
  let packedLabel := dir 10
  let clock := counters 0
  let count := counters 1
  let detFormula := determinant (matrixInput (m := m) false)
  let generate : Pr F K Q prime U := (.seq (readWithSuccessorClock clock (directoryMatrix m a digits prefixWidth zeros packedLabel)) (.seq (.seq (.seq (compile (readLeaf (leafBank inputs)) (registerBank pool) detFormula 0 (pivot 14)) (reusablePivotInverse prime pivot clock count))
    (.seq (packedConjugate pool inputs ports false true) (.seq (bclear (pivot 0)) (bclear (pivot 14))))) (bclear packedLabel)))
  let withZero := (Node.umulSym 1 (bitSymbol false) (dir 8) zeros (dir 4)).seq (generate.seq (bclear zeros))
  (initFrames pool (pivot 4) (conjugationDepth m+1)).seq (withZero.seq (clearFrames pool (conjugationDepth m+1)))

def directoryRecordMatrixSlot (common work : ℕ) : Fin (66+(common+24+31+work)) :=
  ⟨66+(common+16),by omega⟩

/-- The directory's physical matrix writer on its own. All tapes except the
conjugated matrix output return to their input state. -/
theorem generatedRecordMatrix_exec {m w W H J Q common work : ℕ} {F U : Type}
    (v : Descriptor) (proj : Matrix (Fin m) (Fin m) ℚ) (parent : Fin m → ZMod (prime^(w+1)))
    (prefixes : ℕ → List (Fin (prime+4))) (archiveTail : List (Fin (prime+4))) (schedules : List ℕ → List (Fin (prime+4)))
    (hm : prime^(w+1) < 2^H) (poolFits : (conjugationDepth m+1)*13 ≤ work) :
    ∀ (body : F → Pr F (66+(common+24+31+work)) Q prime U) (u : HS _ Q prime U)
      (whole : Stacks _ prime) (label : ℕ) (labels : List ℕ),
      DirectoryReady v proj w W H J parent prefixes archiveTail schedules whole (label :: labels) →
      LabelStock.live m (w+1) 1 label = true →
      let g := physicalLabel m (w+1) label
      let G := g*reduce (prime^(w+1)) proj*g⁻¹
      let out := directoryRecordMatrixSlot common work
      ∃ y n, y.user = u.user ∧ n ≤ (conjugationDepth m+1)*(6*H+6)+1 +
        ((4*H+4)+(recordConjugationTime m w H (prefixes label).length+(2*H+2))+((conjugationDepth m+1)*(2*H+2)+1)) ∧
        Exec body (directoryRecordWriter m common poolFits) (mk u whole) n
          (mk y {whole with R := Function.update whole.R out (matrixWords prime H G ++ whole.R out)}) := by
  intro body u whole label labels start live g G out
  let M := prime^(w+1)
  let host := common+24
  let record := (Fin.natAddEmb common (m := 24)).trans ((Fin.castAddEmb 31).trans (Fin.castAddEmb work))
  let inner := Fin.natAddEmb 66 (m := host+31+work)
  let caller := Fin.castAddEmb (n := 66) (host+31+work)
  let K := 66+(host+31+work)
  let slots : Fin 7 ↪ Fin 58 := ⟨![45,46,2,47,48,44,49],by decide⟩
  let headers := (Fin.castAddEmb (n := 6) 1).trans slots
  let joined := recordLoaderBank record
  let dirSlots := goodRecordDirectoryPorts headers
  let dir := dirSlots.trans joined
  let pool := ((Fin.castLEEmb poolFits).trans (Fin.natAddEmb (host+31))).trans inner
  let pivot := goodRecordPivotPorts.trans joined
  let counters := goodRecordCounterPorts.trans joined
  let inputs := sourcePorts (m := m) (QueueLayout.formulaInputs.trans dir) id
  let ports := QueueLayout.normalizationPorts.trans pivot
  let a := QueueLayout.readPorts.trans (QueueLayout.directoryWork.trans dir)
  let digits := QueueLayout.digitPorts.trans (QueueLayout.directoryWork.trans dir)
  let prefixWidth := dir 12
  let zeros := dir 9
  let packedLabel := dir 10
  let clock := counters 0
  let count := counters 1
  let formula := fun i j : Fin m => numerator (matrixInput false) (matrixInput true) i j
  let detFormula := determinant (matrixInput (m := m) false)
  let generation := fun label => recordConjugationTime m w H (prefixes label).length
  let generate : Pr F K Q prime U := (.seq (readWithSuccessorClock clock (directoryMatrix m a digits prefixWidth zeros packedLabel)) (.seq (.seq (.seq (compile (readLeaf (leafBank inputs)) (registerBank pool) detFormula 0 (pivot 14)) (reusablePivotInverse prime pivot clock count))
    (.seq (packedConjugate pool inputs ports false true) (.seq (bclear (pivot 0)) (bclear (pivot 14))))) (bclear packedLabel)))
  let withZero := (Node.umulSym 1 (bitSymbol false) (dir 8) zeros (dir 4)).seq (generate.seq (bclear zeros))
  let field := fun i => caller ((headers i).castAdd 8)
  let ancestor := prefixes label
  let tail := labels.flatMap (LabelDirectory.entry prefixes m (w+1)) ++ archiveTail
  obtain ⟨dirInput,widths,privateBlank,_,projectorInput,base,_,_,_,one,ticks,_,_⟩ := start
  have prefixInput := widths label List.mem_cons_self
  have clockSlot : headers 0 = 45 := rfl
  have widthSlot : headers 2 = 2 := rfl
  have unitSlot : headers 5 = 44 := rfl
  have scratch (i : Fin 24) (_ : i ≠ 16) := (privateBlank (inner (record i)) (show 58 ≤ 66+(record i).val by omega)).2
  have poolBlank (j) : whole.R (pool j) = [] := (privateBlank _ (show 58 ≤ 66+(host+31+j.val) by omega)).2
  let mat := fun b : Bool => if b then reduce M proj else g
  have depthFits (i j : Fin m) : (formula i j).depth ≤ conjugationDepth m :=
    le_trans (Finset.le_sup (f := fun ij : Fin m × Fin m => (formula ij.1 ij.2).depth) (Finset.mem_univ (i,j)))
      (Nat.le_max_right _ _)
  have poolOff (i : Fin 82) (j) : joined i ≠ pool j := by
    refine Fin.addCases (m := 58) (n := 24) (motive := fun i => joined i ≠ pool j) ?_ ?_ i
    · intro k eq
      rw [show joined (k.castAdd 24) = caller (k.castAdd 8) from recordLoaderBank_caller record k] at eq
      have h := congrArg Fin.val eq
      change k.val = 66+(host+31+j.val) at h
      omega
    · intro k eq
      rw [show joined (k.natAdd 58) = inner (record k) from recordLoaderBank_private record k] at eq
      have h := congrArg Fin.val (inner.injective eq)
      change common+k.val = host+31+j.val at h
      dsimp only [host] at h
      omega
  have bp (i j) : dir i ≠ pool j := poolOff _ _
  have rp (i j) : pivot i ≠ pool j := poolOff _ _
  have cp (i j) : counters i ≠ pool j := poolOff _ _
  have br (i j) (h : i = 10 ∨ j ∈ ([0,1,12,14] : List (Fin 16))) : dir i ≠ pivot j := by
    apply joined.injective.ne
    by_cases hi : i = 10
    · subst i; exact (by decide : ∀ j, (75 : Fin 82) ≠ goodRecordPivotPorts j) j
    · have hj := h.resolve_left hi
      let scratchSlots : Fin 12 → Fin 24 := ![2,3,4,5,6,7,17,8,9,10,11,18]
      have allSlots (l : Fin (6+12)) :
          finSumFinEquiv (Sum.map headers scratchSlots (finSumFinEquiv.symm l)) ≠ goodRecordPivotPorts j := by
        induction l using Fin.addCases with
        | left k =>
          rw [finSumFinEquiv_symm_apply_castAdd]
          exact (by decide : ∀ k : Fin 58, ∀ j ∈ ([0,1,12,14] : List (Fin 16)), k.castAdd 24 ≠ goodRecordPivotPorts j) (headers k) j hj
        | right k =>
          rw [finSumFinEquiv_symm_apply_natAdd]
          exact (by decide : ∀ k : Fin 12, ∀ j ∈ ([0,1,12,14] : List (Fin 16)),
          ((![2,3,4,5,6,7,17,8,9,10,11,18] k : Fin 24).natAdd 58) ≠ goodRecordPivotPorts j) k j hj
      exact allSlots _
  have clockOff : packedLabel ≠ clock := joined.injective.ne (by decide : (75 : Fin 82) ≠ 45)
  have countOff : packedLabel ≠ count := joined.injective.ne (by decide : (75 : Fin 82) ≠ 73)
  have rc (i j) : pivot i ≠ counters j :=
    joined.injective.ne ((by decide : ∀ i j, goodRecordPivotPorts i ≠ goodRecordCounterPorts j) i j)
  have output : pivot 13 = inner (record 16) := recordLoaderBank_private record 16
  have copyPorts : [clock,count,pivot 2,pivot 3].Nodup := by
    simp [clock,count,counters.injective.eq_iff,pivot.injective.eq_iff,Ne.symm (rc _ _)]
  have atOutput : ports 3 = out := output
  have modulusWord : whole.R (pivot 4) = binSyms H M := by
    rw [show pivot 4 = caller 2 from recordLoaderBank_caller record 2]; exact base
  have unitWord : whole.R (pivot 15) = binSyms H (1 : ZMod M).val := by
    rw [show pivot 15 = caller 44 from recordLoaderBank_caller record 44]; exact one
  have clockWidth : (whole.R clock).length = w := by
    rw [show clock = caller 45 from recordLoaderBank_caller record 45]; exact ticks
  have regEmpty (i : Fin 24) (hi : i ≠ 16) : whole.R (joined (i.natAdd 58)) = [] := by
    rw [recordLoaderBank_private]; exact scratch i hi
  have dirEmpty (i : Fin 18) (hi : i ∈ [0,3,4,5,6,7,10,11,14,15]) : whole.R (dir i) = [] := by
    revert hi
    fin_cases i <;> simp <;> exact regEmpty _ (by decide)
  have header (i : Fin 6) : joined ((headers i).castAdd 24) = field i := recordLoaderBank_caller record (headers i)
  have directoryWord : whole.R (dir 2) = ancestor ++ (LabelDirectory.digits m (w+1) label).map RadixDigits.digitSymbol ++ tail := by
    change whole.R (joined ((headers 1).castAdd 24)) = _
    simpa only [ancestor,tail,List.flatMap_cons,LabelDirectory.entry,List.append_assoc] using
      (congrArg whole.R (header 1)).trans dirInput
  have prefixLen := (congrArg (fun i => (whole.R i).length) (header 3)).trans prefixInput
  have fieldClock : dir 1 = clock := by
    change joined ((headers 0).castAdd 24) = joined 45
    rw [clockSlot]; rfl
  have projector : ∃ suffix, whole.R (dir 16) = matrixWords prime H (reduce M proj) ++ suffix := by
    change ∃ suffix, whole.R (joined ((headers 4).castAdd 24)) = _
    rwa [header]
  have packedEmpty := dirEmpty 10 (by decide)
  have widthPort : dir 8 = caller 2 := by
    change joined ((headers 2).castAdd 24) = _
    rw [widthSlot]; exact recordLoaderBank_caller record 2
  have unitPort : dir 17 = caller 44 := by
    change joined ((headers 5).castAdd 24) = _
    rw [unitSlot]; exact recordLoaderBank_caller record 44
  have inputOne := (congrArg whole.R unitPort).trans one
  have digitWidth : (whole.R (digits 4)).length = H := by
    change (whole.R (dir 8)).length = H
    rw [widthPort,base,length_binSyms]
  have freeRead (i : Fin 7) (hi : i = 0 ∨ 3 ≤ i) : whole.R (a i) = [] :=
    dirEmpty _ ((by decide : ∀ i : Fin 7, i = 0 ∨ 3 ≤ i → QueueLayout.directoryWork (QueueLayout.readPorts i) ∈
      ([0,3,4,5,6,7,10,11,14,15] : List (Fin 18))) i hi)
  have freeDigit (i : Fin 6) (hi : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 5) : whole.R (digits i) = [] :=
    dirEmpty _ ((by decide : ∀ i : Fin 6, i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 5 → QueueLayout.directoryWork (QueueLayout.digitPorts i) ∈
      ([0,3,4,5,6,7,10,11,14,15] : List (Fin 18))) i hi)
  have pivotEmpty (i : Fin 16) (hi : i ≠ 4 ∧ i < 13 ∨ i = 14) : whole.R (pivot i) = [] := by
    obtain ⟨j,ne,eq⟩ := (by decide : ∀ i : Fin 16, i ≠ 4 ∧ i < 13 ∨ i = 14 →
      ∃ j : Fin 24, j ≠ 16 ∧ goodRecordPivotPorts i = j.natAdd 58) i hi
    change whole.R (joined (goodRecordPivotPorts i)) = []
    rw [eq]; exact regEmpty j ne
  let B : Stacks K prime := {whole with R := Function.update whole.R out (matrixWords prime H G ++ whole.R out)}
  obtain ⟨y,n,hy,hn,runWriter⟩ := withFrames_exec body pool (pivot 4) out (rp 4) (by change ∀ j, inner (record 16) ≠ pool j; rw [← output]; exact rp 13)
    withZero (matrixWords prime H G) ((4*H+4)+(generation label+(2*H+2))) u whole poolBlank (by
    intro v' E stable filled frames
    have widthE : (E.R (dir 8)).length = H := (congrArg List.length (stable _ (bp 8))).trans digitWidth
    let Z := {E with R := Function.update E.R zeros (binSyms (A := prime) H 0)}
    have zeroWord : Z.R zeros = binSyms H 0 := Function.update_self ..
    have dirKeep (i : Fin 18) (hi : i ≠ 9) : Z.R (dir i) = whole.R (dir i) :=
      (Function.update_of_ne (dir.injective.ne hi) _ _).trans (stable _ (bp i))
    apply (by
      simpa only [widthE] using withRecordZero_exec body (dir 8) zeros (dir 4) out
        (by change [dir 8,dir 9,dir 4].Nodup; simp) (joined.injective.ne (by decide : (74 : Fin 82) ≠ 76))
        generate (matrixWords prime H G) (generation label) v' E ((stable _ (bp 9)).trans (regEmpty 18 (by decide)))
        ((stable _ (bp 4)).trans (dirEmpty 4 (by decide))) : _ → _)
    intro vZero
    let R := Function.update Z.R packedLabel (matrixWords prime H g)
    have updated (i) (hi : ∀ j, i ≠ pool j) (nz : i ≠ zeros) (ne : packedLabel ≠ i) : R i = whole.R i :=
      (Function.update_of_ne ne.symm _ _).trans ((Function.update_of_ne nz _ _).trans (stable i hi))
    have pivotKept (i) := updated (pivot i) (rp i) (joined.injective.ne ((by decide : ∀ i, goodRecordPivotPorts i ≠ 76) i)) (br 10 i (Or.inl rfl))
    have keep (i : Fin 18) (hi : i ≠ 10) (nz : i ≠ 9) : R (dir i) = whole.R (dir i) :=
      (Function.update_of_ne (dir.injective.ne hi) _ _).trans (dirKeep i nz)
    let sources := QueueLayout.formulaInputs.trans dir
    have matrices (b : Bool) : ∃ suffix, R (sources (if id b then 7 else 2)) = matrixWords prime H (mat b) ++ suffix := by
      cases b
      · exact ⟨[],by simp [R,sources,QueueLayout.formulaInputs,packedLabel,mat]⟩
      · change ∃ suffix, R (dir 16) = matrixWords prime H (reduce M proj) ++ suffix
        rwa [keep 16 (by decide) (by decide)]
    have leaves := sourcePorts_ready sources id mat H R matrices
      ((congrArg List.length (keep 8 (by decide) (by decide))).trans digitWidth)
      (show R (dir 9) = _ from (Function.update_of_ne (dir.injective.ne (by decide : (9 : Fin 18) ≠ 10)) _ _).trans zeroWord) ((keep 17 (by decide) (by decide)).trans inputOne)
      (fun i hi => by
        have ok := (by decide : ∀ i ∈ ([0,4,5,6] : List (Fin 10)), ∃ j : Fin 7,
          (j = 0 ∨ 3 ≤ j) ∧ QueueLayout.formulaInputs i = QueueLayout.directoryWork (QueueLayout.readPorts j) ∧
          QueueLayout.formulaInputs i ≠ 10) i hi
        obtain ⟨j,hj,eq,ne⟩ := ok
        exact (keep _ ne ((by decide : ∀ i ∈ ([0,4,5,6] : List (Fin 10)), QueueLayout.formulaInputs i ≠ 9) i hi)).trans ((congrArg whole.R (congrArg dir eq)).trans (freeRead j hj)))
    have scratchPort : ∀ k : Fin 14, k = 1 ∨ 4 ≤ k ∧ k < 12 →
        QueueLayout.normalizationPorts k ≠ 4 ∧ QueueLayout.normalizationPorts k < 13 := by decide
    have posH : 0 < H := by
      have hp := pow_pos Networks.Shared50ModularControl.prime_prime.pos (w+1)
      by_contra! h
      rw [show H = 0 by omega,pow_zero] at hm
      omega
    have readMatrix := directoryMatrix_writes body a digits rfl
      (fun i j => ((by decide : ∀ i j, QueueLayout.readPorts i ≠ QueueLayout.digitPorts j ∨ i = 3 ∧ j = 0) i j).imp
        (fun h => (QueueLayout.directoryWork.trans dir).injective.ne h) id)
      prefixWidth zeros packedLabel (by change [dir 12,dir 0,dir 6].Nodup; simp)
      (by change [dir 12,dir 9,dir 10].Nodup; simp) (dir.injective.ne (by decide : (12 : Fin 18) ≠ 7))
      (fun i => dir.injective.ne ((by decide : ∀ i, QueueLayout.directoryWork (QueueLayout.readPorts i) ≠ 10) i))
      (fun i => dir.injective.ne ((by decide : ∀ i, QueueLayout.directoryWork (QueueLayout.digitPorts i) ≠ 10) i))
      (fun i => dir.injective.ne ((by decide : ∀ i, 9 ≠ QueueLayout.directoryWork (QueueLayout.digitPorts i)) i)) m (w+1) label H posH ancestor tail
    have read := readWithSuccessorClock_writes body clock packedLabel clockOff.symm _ _ _ _ readMatrix
    have keepRead (i : Fin 18) (hi : i ≠ 1) :
        Function.update Z.R clock (Node.tick :: Z.R clock) (dir i) = Z.R (dir i) := by
      rw [← fieldClock]; exact Function.update_of_ne (dir.injective.ne hi) _ _
    have zClock : (Z.R clock).length = w := by
      rw [← fieldClock]
      exact (congrArg List.length (dirKeep 1 (by decide))).trans (by rw [fieldClock]; exact clockWidth)
    have gen := physicalConjugationFromReader_writes body w label mat false true rfl live pivot clock count copyPorts
      (fun i => rc i 1) (rc 14 0).symm H hm pool inputs (fun _ _ j => bp _ j) ports
      (fun k => (rp 14 k).symm) (fun _ _ => br _ 14 (Or.inr (by decide))) (fun k => (rp 0 k).symm) (fun _ _ => br _ 0 (Or.inr (by decide)))
      (fun j => pivot.injective.ne ((by decide : ∀ j, QueueLayout.normalizationPorts j ≠ 14) j)) rfl
      (fun k _ _ => (rp _ k).symm) packedLabel (br 10 13 (Or.inl rfl)) _ _ _ read
      (fun _ _ j hj => br _ _ (Or.inr ((by decide : ∀ j : Fin 14, j = 1 ∨ j = 13 →
        QueueLayout.normalizationPorts j ∈ ([0,1,12,14] : List (Fin 16))) j hj)))
      depthFits (Nat.le_max_left _ _) vZero Z
      ⟨by
          exact ⟨(keepRead 2 (by decide)).trans ((dirKeep _ (by decide)).trans directoryWord),
            (congrArg List.length (keepRead 12 (by decide))).trans ((congrArg List.length (dirKeep _ (by decide))).trans prefixLen),
            by change ((Function.update Z.R clock (Node.tick :: Z.R clock)) (dir 1)).length = w+1
               rw [fieldClock,Function.update_self,List.length_cons,zClock],
            fun i hi => (keepRead _ ((by decide : ∀ i : Fin 7, i = 0 ∨ 3 ≤ i → QueueLayout.directoryWork (QueueLayout.readPorts i) ≠ 1) i hi)).trans
              ((dirKeep _ ((by decide : ∀ i : Fin 7, QueueLayout.directoryWork (QueueLayout.readPorts i) ≠ 9) i)).trans (freeRead i hi)),
            (congrArg List.length (keepRead 8 (by decide))).trans ((congrArg List.length (dirKeep _ (by decide))).trans digitWidth),
            fun i hi => (keepRead _ ((by decide : ∀ i : Fin 6, QueueLayout.directoryWork (QueueLayout.digitPorts i) ≠ 1) i)).trans
              ((dirKeep _ ((by decide : ∀ i : Fin 6, QueueLayout.directoryWork (QueueLayout.digitPorts i) ≠ 9) i)).trans (freeDigit i hi)),
            (keepRead 9 (by decide)).trans zeroWord⟩,
        (dirKeep _ (by decide)).trans packedEmpty,(congrArg List.length (updated clock (cp 0) (joined.injective.ne (by decide : (45 : Fin 82) ≠ 76)) clockOff)).trans clockWidth,
        (updated count (cp 1) (joined.injective.ne (by decide : (73 : Fin 82) ≠ 76)) countOff).trans (regEmpty 15 (by decide)),(pivotKept 14).trans (pivotEmpty 14 (by decide)),(pivotKept 15).trans unitWord,
        (pivotKept 4).trans modulusWord,fun i h l => (pivotKept i).trans (pivotEmpty i (Or.inl ⟨h,l⟩)),
        fun k hk => (Function.update_of_ne (bp 10 _).symm _ _).trans ((Function.update_of_ne (bp 9 _).symm _ _).trans ((filled k hk).trans modulusWord)),
        fun k hk i hi => (Function.update_of_ne (bp 10 _).symm _ _).trans ((Function.update_of_ne (bp 9 _).symm _ _).trans (frames k hk i hi)),leaves,
        (pivotKept 4).trans modulusWord,(pivotKept 12).trans (pivotEmpty 12 (by decide)),
        fun k hk => (pivotKept _).trans (pivotEmpty _ (Or.inl (scratchPort k hk)))⟩
    simpa only [generation,recordConjugationTime,generate,detFormula,atOutput,mat,G,Bool.false_eq_true,ite_false,ite_true] using gen)
  rw [modulusWord,length_binSyms] at hn
  exact ⟨y,n,hy,hn,runWriter⟩

/-- Execute the generated good or padding program from any ready record boundary. -/
theorem generatedOrdinaryRecord_exec [M8.Machine.Net] {T m work Q fields H J W : ℕ} {F U : Type}
    (v : Descriptor) (positive : v.Positive) (w : ℕ) (proj : Matrix (Fin m) (Fin m) ℚ)
    (width : v.width = proj.rank*(w+1)) (idem : proj*proj = proj)
    (factor : Factorization univ univ proj) (hd : ∀ a ∈ factorizationDenominators factor, a < prime)
    (rankFits : proj.rank ≤ m) (parent parentInv : Fin m → ZMod (prime^(w+1)))
    (reciprocal : ∀ i, parent i * parentInv i = 1)
    (io : Fin T) (arity : ℕ)
    (hm : prime^(w+1) < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (length : volume prime v = (prime^(w+1))^fields*((prime^(w+1))^fields*W))
    (capacity : 217 ≤ Q) (source : ℤ → Fin 4) (head : ℤ)
    (fits : LeafCore.small ≤ work) (cap : (LeafCore.core io).states ≤ Q) :
    GeneratedRecordSpec (F := F) (U := U) v positive w proj width idem factor hd rankFits parent parentInv
      reciprocal io arity hm hw hW length capacity source head fits cap true := by
  unfold GeneratedRecordSpec
  intro d common host M N entry leave record bank commonPorts aux hdrPorts logical addr inner caller K ef xf eqs xqs initialWord
    body initialUser initialState poolFits directory prefixes archiveTail allLabels slots headers scanCaller scan joined dirSlots dir pool pivot counters inputs ports a digits prefixWidth zeros
    packedLabel clock count formula detFormula generationBill generate withZero field slot r src dst gs matrices liveBit badBit φ table fallbackCode schedules ready payload
    call cost budget coordinate effects reverse transfer marks loading conversion headerCost raw tripCost runBills prepareCounters prepareHeaders recordProgram
    privateTapes initialClear c bodyBound charge binaryRun binaryCharge mask mode modes skip skipCost ordinaryStep
  have clockSlot : headers 0 = 45 := rfl
  have widthSlot : headers 2 = 2 := rfl
  have unitSlot : headers 5 = 44 := rfl
  have scanOff : ∀ i : Fin 6, i < 4 → scanCaller i ≠ 24 := by decide
  have projOff : headers 4 ≠ 24 := by decide
  have dirOff : ∀ j ∈ ([28,53,55] : List (Fin 58)), j ≠ scanCaller 2 := by decide
  have srcOff (i) : src i ≠ scan 2 := by
    intro eq; have h := congrArg Fin.val eq; change 33+i.val = 46 at h; omega
  suffices step : ordinaryStep by
    refine ⟨step,?_,?_⟩
    · intro dimension data room placement archive outer calls label labels word u S binary inside ordinary start input queue
        program advance
      obtain ⟨v,D,n,next,user,time,run,done,effect,output,maskKeep,modeKeep⟩ :=
        step label labels word (embDn placement u) (embStk placement S) ordinary start input
      have clock : (D.R (caller 2)).length = data.H := by
        rw [done.2.2.2.2.2.1,length_binSyms,binary]
      have blank : D.R (caller 59) = [] := (done.2.2.1 _ (by decide : 58 ≤ 59)).2
      obtain ⟨z,B,hz,bank,tail,_,exec⟩ := data.advanceEmbeddedRecord_exec label inside placement archive
        (Fin.succAbove_ne _) (caller 2) (caller 59) (caller.injective.ne (by decide)) id body outer calls
        program u S v D n run clock blank queue
      have cell (i : Fin K) : B.R (placement i) = D.R i := congrArg (fun C => Stacks.R C i) bank
      rw [binary] at exec
      exact ⟨z,B,_,next,hz.trans user,Nat.add_le_add_right time _,exec,by rw [bank]; exact done,effect,
        by rw [bank]; exact output,tail,(cell mask).trans maskKeep,(cell mode).trans modeKeep⟩
    · intro dimension shape data room anchor states fieldsEq binary outer calls push bounded u S
      subst Q
      subst fields
      subst H
      let ceiling := if 0 < d ∧ data.H = M.size ∧ J = W.size then min (charge 0) binaryCharge else charge 0
      suffices scanned : ∀ y D, ArchiveRun (J := J) shape v proj parent parentInv data room anchor outer push
          prefixes archiveTail rankFits source head length initialWord (recordProgram.seq (clearWorkTapes privateTapes))
          skip (fun j => if liveBit j then charge j else skipCost j) ceiling (fun j => if liveBit j then effects j else Eq) y D by
        exact ⟨scanned u S,fun extra => generatedArchive_exec shape v proj parent parentInv data room anchor outer push
          prefixes archiveTail rankFits source head length initialWord (recordProgram.seq (clearWorkTapes privateTapes))
          skip _ ceiling _ u S extra hm reciprocal scanned⟩
      intro y D
      apply DirectoryReady.runArchive shape v proj idem (by
        simpa using admissible_of_lt Networks.Shared50ModularControl.prime_prime (fun k (h : k ∈ denominators proj) => hd k (by simp [factorizationDenominators,h])) 1) parent parentInv reciprocal data hm hw hW room anchor outer push bounded prefixes archiveTail
        factor hd rankFits source head length initialWord y D body calls (recordProgram.seq (clearWorkTapes privateTapes))
        skip (fun j => if liveBit j then charge j else skipCost j) _ (fun j => if liveBit j then effects j else Eq)
      · dsimp only [ceiling]
        intro j widthEq
        have same : charge j = charge 0 := by simp only [charge,runBills,widthEq]
        have cheap : skipCost j ≤ charge j := (Nat.le_add_left _ _).trans (Nat.le_add_right (runBills j) _)
        have prefixBound : 4*(prefixes j).length ≤ skipCost j := by dsimp only [skipCost]; omega
        apply (ordinaryCharge_le (liveBit j) prefixBound cheap same).trans
        split
        · next active =>
            exact le_min le_rfl (generatedCharge_binary_le m w d W _ raw budget initialClear
              (max (mnProgPush recordProgram) c) data.H J v positive width active)
        · exact le_rfl
      · have port : r 0 = caller 24 := recordRoundTripPorts_other slot 0 (by decide)
        simpa only [ordinaryStep,payload,port] using step
  intro label labels word u whole ordinary start input
  by_cases live : liveBit label = true
  case neg =>
    have pad := Bool.eq_false_iff.mpr live
    have noCode : badBit label = false := by
      dsimp only [badBit,gs]
      rw [fallbackBit_eq (by omega : 0 < w+1),show LabelStock.live m (w+1) 1 label = false from pad]
      rfl
    obtain ⟨dir,widths,privateBlank,scratch,projector,base,unit,trailing,headersIn,one,ticks,archive,queue⟩ := start
    let tail := labels.flatMap (LabelDirectory.entry prefixes m (w+1)) ++ archiveTail
    obtain ⟨z,user,advance⟩ := advanceDirectoryRecord_exec body scan m w label prefixes labels archiveTail u whole dir
      (widths label List.mem_cons_self) ticks scratch
    let D := {whole with R := Function.update whole.R (scan 2) tail}
    have keep (j : Fin 66) (hj : j ≠ 46) : D.R (caller j) = whole.R (caller j) :=
      Function.update_of_ne (caller.injective.ne hj) _ _
    have rdy : ready D labels := by
      refine ⟨(show D.R (field 1) = tail from Function.update_self (scan 2) tail whole.R),fun j hj => (congrArg List.length (keep 47 (by decide))).trans
        (widths j (List.mem_cons_of_mem _ hj)),?_,(keep 49 (by decide)).trans scratch,?_,
        (keep 2 (by decide)).trans base,(keep 28 (by decide)).trans unit,(keep 53 (by decide)).trans trailing,
        fun i => (Function.update_of_ne (srcOff i) _ _).trans (headersIn i),(keep 44 (by decide)).trans one,
        (congrArg List.length (keep 45 (by decide))).trans ticks,(keep 55 (by decide)).trans archive,
        (keep 54 (by decide)).trans (by simpa only [schedules,List.flatMap_cons,noCode,Bool.false_eq_true,ite_false,List.nil_append] using queue)⟩
      · intro i hi
        exact ⟨(privateBlank i hi).1,(Function.update_of_ne (by intro eq; subst i; change 58 ≤ 46 at hi; omega) _ _).trans (privateBlank i hi).2⟩
      · obtain ⟨xs,h⟩ := projector; exact ⟨xs,(keep 48 (by decide)).trans h⟩
    have pay : payload word D := by
      intro k
      have port := recordRoundTripPorts_other slot 0 (by decide)
      change readAt _ (whole.L (r 0)) (D.R (r 0)) _ = _
      rw [show r 0 = caller 24 from port,keep 24 (by decide)]
      simpa only [show r 0 = caller 24 from port] using input k
    simp only [pad,Bool.false_eq_true,ite_false]
    exact ⟨z,D,_,word,user,le_rfl,advance,rdy,rfl,pay,keep 57 (by decide),keep 56 (by decide)⟩
  have good : badBit label = false := Bool.eq_false_iff.mpr (fun h => ordinary ⟨live,h⟩)
  simp only [live,good,Bool.false_eq_true,ite_false,ite_true]
  let g := gs label
  let G := matrices label
  let ancestor := prefixes label
  let tail := labels.flatMap (LabelDirectory.entry prefixes m (w+1)) ++ archiveTail
  let generation := generationBill label
  let runCost := runBills label
  obtain ⟨dirInput,widths,privateBlank,scanBlank,projectorInput,base,unit,trailing,sourceWords,one,ticks,archive,queue⟩ := start
  have prefixInput := widths label List.mem_cons_self
  let commonTape := fun k : Fin common => (((k.castAdd 24).castAdd 31).castAdd work)
  let roles := SharedBank.empty T prime
  let node := SharedBank.empty 1 prime
  let scalar := SharedBank.empty 1 prime
  let st := SharedBank.empty 2 prime
  let f := fun _ : ℤ => (blank : Fin (prime+4))
  let p := (0 : ℤ)
  let initialBank := CommonBank.bank roles (Routines.hdr v) f p node scalar (Family.leafC (w+1) arity d d) st
  let S := embStk inner whole
  have freeNode : Family.NodeFree node := fun _ _ => rfl
  have innerBlank (j) := privateBlank (inner j) (show 58 ≤ 66+j.val by omega)
  have spare (i : Fin 66) (hi : 58 ≤ i.val) := privateBlank (caller i) hi
  have hdrBlank (i) := innerBlank (hdrPorts i)
  have auxBlank (i) := innerBlank (aux i)
  have sharedBlank (z : ℤ) : readAt blank (whole.L (r 1)) (whole.R (r 1)) z = blank := by
    rw [show r 1 = inner slot from recordRoundTripPorts_shared slot,(innerBlank slot).1,(innerBlank slot).2,
      readAt_nil_left,wordTape_nil]
  have workBlank (k : Fin work) := innerBlank (k.natAdd (host+31))
  have poolBlank (j) : whole.R (pool j) = [] := (workBlank ((Fin.castLEEmb poolFits) j)).2
  have free : ∀ (k : Fin work) x,
      readAt blank (S.L (k.natAdd (host+31))) (S.R (k.natAdd (host+31))) x = blank := by
    intro k x
    change readAt _ (whole.L _) (whole.R _) _ = _
    rw [(workBlank k).1, (workBlank k).2,readAt_nil_left,wordTape_nil]
  have empty (k : Fin 31) := innerBlank ((k.natAdd host).castAdd work)
  have scratch (i : Fin 24) (_ : i ≠ 16) := (innerBlank (record i)).2
  let out := inner (record 16)
  let B : Stacks K prime := {whole with R := Function.update whole.R out (matrixWords prime H G ++ whole.R out)}
  obtain ⟨y,n,hy,hn,runWriter⟩ := generatedRecordMatrix_exec (common := common) v proj parent prefixes archiveTail
    schedules hm poolFits body u whole label labels
    ⟨dirInput,widths,privateBlank,scanBlank,projectorInput,base,unit,trailing,sourceWords,one,ticks,archive,queue⟩ live
  have callerOff (i : Fin 66) : caller i ≠ out := by
    intro eq
    have h := congrArg Fin.val eq
    change i.val = 66+(record 16).val at h
    omega
  have preserved (i : Fin 66) : B.R (caller i) = whole.R (caller i) := Function.update_of_ne (callerOff i) _ _
  have privateOff (j) (h : j.val < common ∨ host ≤ j.val) : inner j ≠ out := by
    intro eq
    have hit := congrArg Fin.val (inner.injective eq)
    change j.val = common+16 at hit
    dsimp only [host] at h
    omega
  have privateKept (j) (h : j.val < common ∨ host ≤ j.val) : B.R (inner j) = whole.R (inner j) :=
    Function.update_of_ne (privateOff j h) _ _
  have first : r 0 = caller 24 := recordRoundTripPorts_other slot 0 (by decide)
  have shared : inner slot = r 1 := (recordRoundTripPorts_shared slot).symm
  let auxPort := aux.trans inner
  have commonKeep (i : Fin common) : B.R (inner (commonTape i)) = whole.R (inner (commonTape i)) :=
    privateKept _ (Or.inl i.isLt)
  have auxEmpty (i : Fin 24) : B.L (auxPort i) = [] ∧ B.R (auxPort i) = [] :=
    ⟨(auxBlank i).1,(commonKeep (CommonBank.auxSlot i)).trans (auxBlank i).2⟩
  obtain ⟨counterUser,E,costC,hUser,hCost,prep,auxRep,auxKeep⟩ :=
    prepareLeafCounters_exec body auxPort (leafCounterPorts aux) rfl arity d w y B
      ((congrArg List.length (preserved 45)).trans ticks)
      (by intro i hi; cases i using Fin.cases with
          | zero => exact (hi rfl).elim
          | succ j => exact (auxEmpty (j.castLE (by decide))).2) auxEmpty
  have callerApart (i : Fin 66) (j) : caller i ≠ dst j := by
    intro eq; have h := congrArg Fin.val eq
    change i.val = 66+(hdrPorts j).val at h; omega
  have srcApart (i j) : src i ≠ dst j := callerApart _ _
  have callerE (i : Fin 66) := auxKeep (caller i) (by
    intro j eq; have h := congrArg Fin.val eq
    change 66+(aux j).val = i.val at h; omega)
  have hdrNe (i j) : CommonBank.auxSlot (t := T) i ≠ CommonBank.headerSlot j := by
    intro eq; have h := congrArg Fin.val eq
    rw [CommonBank.auxSlot_val, CommonBank.headerSlot_val] at h
    have := j.isLt
    omega
  have dstE (j) := auxKeep (dst j) (fun i eq => hdrNe i j (commonPorts.injective (inner.injective eq)))
  have wordsE (i) : E.R (src i) = (Routines.hdr v i).map bitSymbol :=
    (callerE _).2.trans ((preserved _).trans (sourceWords i))
  obtain ⟨headerUser,C,hHeaders,install,hdrRep,hdrKeep⟩ := prepareRecordHeaders_exec body v src dst
    (caller 64) (caller 65) srcApart (by
      intro i
      simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or]
      exact ⟨⟨srcApart i i,by intro eq; have h := congrArg Fin.val eq; change 33+i.val = 64 at h; omega,
        by intro eq; have h := congrArg Fin.val eq; change 33+i.val = 65 at h; omega⟩,
        ⟨(callerApart 64 i).symm,(callerApart 65 i).symm⟩,caller.injective.ne (by decide),by simp⟩)
    counterUser E wordsE (fun j => ⟨(dstE j).1.trans (hdrBlank j).1,
      (dstE j).2.trans ((commonKeep (CommonBank.headerSlot j)).trans (hdrBlank j).2)⟩)
    ((callerE 64).2.trans ((preserved 64).trans (spare 64 (by decide)).2))
    ((callerE 65).2.trans ((preserved 65).trans (spare 65 (by decide)).2))
  simp only [wordsE,List.length_map] at install
  have keep (j) (ha : ∀ i, auxPort i ≠ j) (hh : ∀ i, dst i ≠ j) :=
    And.intro ((hdrKeep j hh).1.trans (auxKeep j ha).1) ((hdrKeep j hh).2.trans (auxKeep j ha).2)
  have callerFrame (i : Fin 66) := And.intro
    ((hdrKeep _ (fun j => (callerApart i j).symm)).1.trans (callerE i).1)
    ((hdrKeep _ (fun j => (callerApart i j).symm)).2.trans (callerE i).2)
  have commonOff (k : Fin common) (j) (hj : common ≤ j.val) : inner (commonTape k) ≠ inner j := by
    intro eq; have h := congrArg Fin.val (inner.injective eq)
    change k.val = j.val at h; omega
  have outsideCommon (j) (hj : common ≤ j.val) := keep (inner j) (fun _ => commonOff _ j hj) (fun _ => commonOff _ j hj)
  have other (k : Fin common) (ha : ∀ i, CommonBank.auxSlot i ≠ k) (hh : ∀ i, CommonBank.headerSlot i ≠ k) :=
    keep (inner (commonTape k)) (fun i eq => ha i (commonPorts.injective (inner.injective eq)))
      (fun i eq => hh i (commonPorts.injective (inner.injective eq)))
  have roleKeep := other (LeafCore.roleSlot io) (by
    intro i eq; have h := congrArg Fin.val eq
    rw [CommonBank.auxSlot_val] at h
    change T+12+i.val = io.val at h; omega) (by
    intro i eq; have h := congrArg Fin.val eq
    rw [CommonBank.headerSlot_val] at h
    change T+1+i.val = io.val at h; omega)
  obtain ⟨z,D,t,ys,hz,⟨ht,htVolume⟩,run,act,read,frame⟩ := goodRecordRoundTrip_exec
    v positive w proj width idem factor hd label live rankFits parent parentInv reciprocal io roles f p node scalar
    arity st freeNode hm hw hW length capacity source head fits cap ef xf eqs xqs word body headerUser C (whole.R out)
    ((callerFrame 2).2.trans ((preserved 2).trans base)) ((callerFrame 28).2.trans ((preserved 28).trans unit))
    ((callerFrame 53).2.trans ((preserved 53).trans trailing))
    (fun i hi => ⟨(callerFrame i).1.trans (spare i hi).1,(callerFrame i).2.trans ((preserved i).trans (spare i hi).2)⟩)
    (by intro z; change readAt _ (C.L (r 0)) (C.R (r 0)) _ = _
        rw [first,(callerFrame 24).1,(callerFrame 24).2,preserved]; simpa only [first] using input z)
    (by intro z; change readAt _ (C.L (r 1)) (C.R (r 1)) _ = _
        rw [← shared,show C.L (inner slot) = B.L (inner slot) from roleKeep.1,
          show C.R (inner slot) = B.R (inner slot) from roleKeep.2,privateKept _ (Or.inl (LeafCore.roleSlot io).isLt)]
        simpa only [← shared] using sharedBlank z)
    (by intro k x
        change initialBank.tape k x = readAt _ (C.L (inner (commonTape k))) (C.R (inner (commonTape k))) _
        by_cases h : ∃ i, CommonBank.auxSlot i = k
        · obtain ⟨i,rfl⟩ := h
          have atAux := CommonBank.bank_aux roles (Routines.hdr v) f p node scalar (Family.leafC (w+1) arity d d) st i
          change _ = readAt _ _ _ (x-initialBank.head _)
          rw [show initialBank.head _ = _ from atAux.1, show initialBank.tape _ = _ from atAux.2]
          have kept := hdrKeep (auxPort i) (fun j eq => hdrNe i j (commonPorts.injective (inner.injective eq.symm)))
          change _ = readAt _ (C.L (auxPort i)) (C.R (auxPort i)) _
          rw [kept.1,kept.2]
          exact auxRep i x
        · by_cases hh : ∃ i, CommonBank.headerSlot i = k
          · obtain ⟨i,rfl⟩ := hh
            have facts := CommonBank.bank_header roles (Routines.hdr v) f p node scalar (Family.leafC (w+1) arity d d) st i
            rw [show initialBank.head _ = _ from facts.1,show initialBank.tape _ = _ from facts.2]
            exact hdrRep i x
          · have off := other k (fun i eq => h ⟨i,eq⟩) (fun i eq => hh ⟨i,eq⟩)
            rw [off.1,off.2,commonKeep,show B.L _ = [] from (innerBlank (commonTape k)).1,
              (innerBlank (commonTape k)).2,readAt_nil_left,wordTape_nil]
            exact emptyCommonTape _ _ k (fun i eq => h ⟨i,eq⟩) (fun i eq => hh ⟨i,eq⟩) x)
    (by intro k x
        let j := k.natAdd (host+31)
        have hi : host ≤ j.val := by simp [j]; omega
        change readAt _ (C.L (inner j)) (C.R (inner j)) _ = _
        rw [(outsideCommon j (by dsimp [host] at hi; omega)).1,(outsideCommon j (by dsimp [host] at hi; omega)).2,
          privateKept _ (Or.inr hi)]
        exact free k x)
    (fun k => by
      let j := (k.natAdd host).castAdd work
      have hi : host ≤ j.val := by simp [j]
      have off := outsideCommon j (by dsimp [host] at hi; omega)
      exact ⟨off.1.trans (empty k).1,off.2.trans ((privateKept j (Or.inr hi)).trans (empty k).2)⟩)
    good (by change C.R out = _
             rw [show C.R out = B.R out from (outsideCommon (record 16) (by change common ≤ common+16; omega)).2]
             simp [B,G,matrices,gs,M])
    ((callerFrame 44).2.trans ((preserved 44).trans one))
    ((congrArg List.length (callerFrame 45).2).trans ((congrArg List.length (preserved 45)).trans ticks))
    ((callerFrame 55).2.trans ((preserved 55).trans archive))
    (by intro i hi
        exact (outsideCommon (record i) (by change common ≤ common+i.val; omega)).2.trans
          ((Function.update_of_ne (inner.injective.ne (record.injective.ne hi)) _ _).trans (scratch i hi)))
  have keptCaller (j : Fin 58) (ne : j ≠ 24) :=
    (frame j ne).2.trans ((callerFrame _).2.trans (preserved _))
  have keptScan (i : Fin 6) (hi : i < 4) : D.R (scan i) = whole.R (scan i) :=
    keptCaller _ (scanOff i hi)
  obtain ⟨last,user,advance⟩ := advanceDirectoryRecord_exec body scan m w label prefixes labels archiveTail z D
    ((keptScan 2 (by decide)).trans dirInput)
    ((congrArg List.length (keptScan 0 (by decide))).trans prefixInput)
    ((congrArg List.length (keptScan 1 (by decide))).trans (show (whole.R (field 0)).length = w by
      change (whole.R (caller ((headers 0).castAdd 8))).length = _
      rw [clockSlot]; exact ticks))
    ((keptScan 3 (by decide)).trans scanBlank)
  let finalBank := {D with R := Function.update D.R (scan 2) tail}
  have step : Exec body recordProgram (mk u whole) _ (mk last finalBank) :=
    Exec.seq (Exec.seq (Exec.seq (Exec.seq runWriter prep) install) run) advance
  have bound : (n+costC+headerCost)+t+(1+(4*ancestor.length+4+(m*m*(4*(w+1)+4)+1)+1)) ≤ runCost := by
    apply Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add_right (Nat.add_le_add hn hCost) _) _) _
    change t ≤ tripCost
    dsimp only [tripCost]
    split
    · rename_i binary
      exact le_min ht (htVolume binary.1 binary.2.1 binary.2.2)
    · exact ht
  have distinct : privateTapes.Nodup := (List.nodup_finRange K).filter _
  obtain ⟨finish,userFinish,clear⟩ := clearWorkTapes_exec body privateTapes distinct last finalBank
  have charge := recordCleanup_cost_le privateTapes distinct step (le_max_left (mnProgPush recordProgram) c)
    (fun f => (bodyBound f).trans (le_max_right _ _))
  have privateMem (i : Fin K) : i ∈ privateTapes ↔ 58 ≤ i.val := by simp [privateTapes]
  have init : (privateTapes.map fun i => 4*(whole.L i).length+2*(whole.R i).length+4) =
      privateTapes.map (fun _ => 4) := by
    apply List.map_congr_left
    intro i hi
    simp [privateBlank i ((privateMem i).mp hi)]
  simp only [init,List.map_const',List.sum_replicate_nat] at charge
  have callerOut (j : Fin 58) : caller (j.castAdd 8) ∉ privateTapes := by
    rw [privateMem]; exact Nat.not_le_of_lt j.isLt
  have payloadOut : r 0 ∉ privateTapes := by rw [first]; exact callerOut 24
  have finalFrame (j : Fin 58) (ne : j ≠ 24) (nd : j ≠ scanCaller 2) :
      let port := caller (j.castAdd 8)
      (if port ∈ privateTapes then [] else finalBank.L port) = whole.L port ∧
        (if port ∈ privateTapes then [] else finalBank.R port) = whole.R port := by
    have off : caller (j.castAdd 8) ≠ scan 2 := caller.injective.ne ((Fin.castAddEmb 8).injective.ne nd)
    simp only [ite_eq_right (callerOut j)]
    exact ⟨(frame j ne).1.trans (callerFrame _).1,(Function.update_of_ne off _ _).trans (keptCaller j ne)⟩
  have hdrFrame (i : Fin 6) (hp : headers i ≠ 24) (hd : i ≠ 1) :=
    (finalFrame (headers i) hp (headers.injective.ne hd)).2
  obtain ⟨minor,next,rfl,action⟩ := act
  refine ⟨finish,_,_,next,userFinish.trans (user.trans (hz.trans (hHeaders.trans (hUser.trans hy)))),Nat.add_le_add bound
    (charge.trans (Nat.add_le_add_left (Nat.mul_le_mul_left 6 (Nat.mul_le_mul_left _ bound)) _)),
    Exec.seq step clear,?_,⟨minor,action⟩,?_,(finalFrame 57 (by decide) (by decide)).2,(finalFrame 56 (by decide) (by decide)).2⟩
  · refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · change (if scan 2 ∈ privateTapes then [] else finalBank.R (scan 2)) = tail
      simp [show scan 2 ∉ privateTapes from callerOut _,finalBank]
    · intro j hj
      exact (congrArg List.length (hdrFrame 3 (scanOff 0 (by decide)) (by decide))).trans
        (widths j (List.mem_cons_of_mem _ hj))
    · intro i hi; simp [(privateMem i).mpr hi]
    · exact (finalFrame (scanCaller 3) (scanOff 3 (by decide)) (scanCaller.injective.ne (by decide))).2.trans scanBlank
    · obtain ⟨xs,h⟩ := projectorInput
      exact ⟨xs,(hdrFrame 4 projOff (by decide)).trans h⟩
    · have h := hdrFrame 2 (by rw [widthSlot]; decide) (by decide)
      rw [widthSlot] at h; exact h.trans base
    · exact (finalFrame 28 (by decide) (dirOff 28 (by decide))).2.trans unit
    · exact (finalFrame 53 (by decide) (dirOff 53 (by decide))).2.trans trailing
    · intro i
      let j : Fin 58 := (i.natAdd 33).castLE (by decide : 39 ≤ 58)
      have ne : j ≠ 24 := by intro eq; have h := congrArg Fin.val eq; change 33+i.val = 24 at h; omega
      exact (finalFrame j ne (fun eq => srcOff i (congrArg (fun k : Fin 58 => caller (k.castAdd 8)) eq))).2.trans (sourceWords i)
    · have h := hdrFrame 5 (by rw [unitSlot]; decide) (by decide)
      rw [unitSlot] at h; exact h.trans one
    · have h := hdrFrame 0 (by rw [clockSlot]; decide) (by decide)
      rw [clockSlot] at h; exact (congrArg List.length h).trans ticks
    · exact (finalFrame 55 (by decide) (dirOff 55 (by decide))).2.trans archive
    · exact (show _ = whole.R (caller 54) from (finalFrame 54 (by decide) (by decide)).2).trans (by simpa only [schedules,List.flatMap_cons,good,Bool.false_eq_true,ite_false,List.nil_append] using queue)
  · have off : r 0 ≠ scan 2 := by
      rw [first]
      exact caller.injective.ne ((Fin.castAddEmb 8).injective.ne (scanOff 2 (by decide)).symm)
    simpa only [payload,RecordPayload,ite_eq_right payloadOut,finalBank,Function.update_of_ne off] using read

/-- Generate the directory masks and exceptional queue using only the incoming
dimension counters and precision clock. All temporary right stacks are cleared. -/
theorem directoryControls_exec {m d k Q extra w Bcount : ℕ} {F U : Type}
    (body : F → Pr F (66+extra) Q prime U) (rankFits : d ≤ m)
    (request : Matrix (Fin m) (Fin m) (ZMod prime))
    (table : Matrix (Fin m) (Fin m) (ZMod prime) → Matrix (Fin k) (Fin k) (ZMod prime))
    (proj : LabelPadding.Label m (w+1)) (reduction : (LabelRing.res prime (w+1) (by omega)).mapMatrix proj = request)
    (directory : Descriptor) (dirPositive : directory.Positive) (shape : directory.beforeH = Bcount*prime^(m*((w+1)*m)))
    (room : m*m+m*m ≤ extra) (initialUser : HS (66+extra) Q prime U) (initialState : Stacks (66+extra) prime) :
    let K := 66+extra
    let caller := Fin.castAddEmb (n := 66) extra
    let mask := caller 57
    let mode := caller 56
    let parents := caller 50
    let rs := residuePairs (m*m) room
    let high := prime^w
    let allLabels := List.range (LabelMask.records directory)
    let schedules := fun xs : List ℕ => xs.flatMap fun j =>
      if fallbackBit rankFits proj (physicalLabel m (w+1) j) then residualSchedule (A := prime) (table (LabelStock.residue m (w+1) 1 j)) else []
    let liveWords := allLabels.map fun j => bitSymbol (a := prime) (LabelStock.live m (w+1) 1 j)
    let badWords := allLabels.map fun j => bitSymbol (a := prime) (fallbackBit rankFits proj (physicalLabel m (w+1) j))
    let privateTapes := (List.finRange K).filter fun i => 58 ≤ i.val
    let clean := {initialState with
      L := fun i => if i ∈ privateTapes then [] else initialState.L i
      R := fun i => if i ∈ privateTapes then [] else Function.update initialState.R (caller 54) (schedules allLabels) i}
    (∀ i : Fin K, 58 ≤ i.val → initialState.R i = []) →
    (initialState.R (caller 28)).length = 1 → (initialState.R (caller 45)).length = w →
    (initialState.R (caller 29)).length = directory.beforeRows → (initialState.R (caller 30)).length = directory.rows →
    (initialState.R (caller 31)).length = directory.beforeH → initialState.R parents = [] →
    initialState.R mask = [] → initialState.R mode = [] → initialState.R (caller 54) = [] →
    let initCounters : Pr F K Q prime U := (Node.expProg 0 prime (caller 28) (caller 45) (caller 58) (caller 59) (caller 60) (caller 61)).seq
      (Node.scanR (caller 58) (caller 59) (LabelCountBank.pushAll (rs.map Prod.fst)))
    ∃ writer z n, z.user = initialUser.user ∧ n ≤ (26*high+4) +
      ((44*allLabels.length+13*(w+1)+16)+3*((6+10*(m*m))*allLabels.length+4)+(2*(directory.beforeRows*directory.rows*Bcount)+2)) +
      ((privateTapes.map fun i => 4*(initialState.L i).length).sum+privateTapes.length*(2*high+4)+1) ∧
      Exec body ((initCounters.seq writer).seq (clearWorkTapes privateTapes)) (mk initialUser initialState) n
        (mk z {clean with R := Function.update (Function.update clean.R mask liveWords) mode badWords}) := by
  intro K caller mask mode parents rs high allLabels schedules liveWords badWords privateTapes clean freePrivate single clockLen
    brSize rowsSize beforeHSize parentsFree freeMask freeMode freeQueue initCounters
  have apart : mask ≠ mode := caller.injective.ne (by decide)
  obtain ⟨sizeRs,slotsUnique,rsPrivate⟩ := residuePairs_layout room
  let saved := caller 62
  have callerOutside (j : Fin 66) : caller j ∉ LabelTraversal.slots rs := by
    intro mem; have h := rsPrivate _ mem; change 66 ≤ j.val at h; omega
  have layout (j : Fin 66) (hp : j ≠ 50) (hs : j ≠ 62) :
      (parents :: saved :: (LabelTraversal.slots rs ++ [caller j])).Nodup := by
    simp [parents,saved,List.nodup_append',callerOutside,slotsUnique,rs,
      caller.injective.eq_iff,hp.symm,hs.symm]
  have maskRegs := layout 57 (by decide) (by decide)
  have modeRegs := layout 56 (by decide) (by decide)
  let R := LabelCountBank.fill (rs.map Prod.fst) high
    (Function.update initialState.R (caller 58) (List.replicate high Node.tick))
  have cleanup := counterCleanup_le initialState privateTapes (rs.map Prod.fst) (caller 58) high
    (by intro h; obtain ⟨p,hp,eq⟩ := List.mem_map.mp h
        exact callerOutside 58 (List.mem_flatMap.mpr ⟨p,hp,by simp [← eq]⟩))
    (fun i hi => freePrivate i (by simpa [privateTapes] using hi))
  have fillKeep (i) (outside : i ∉ LabelTraversal.slots rs) (off : i ≠ caller 58) : R i = initialState.R i := by
    have nf : i ∉ rs.map Prod.fst := by
      intro h; obtain ⟨p,hp,rfl⟩ := List.mem_map.mp h
      exact outside (List.mem_flatMap.mpr ⟨p,hp,by simp⟩)
    simp [R,LabelCountBank.fill,nf,off]
  have callerKeep (j : Fin 66) (hj : j ≠ 58) := fillKeep _ (callerOutside j) (caller.injective.ne hj)
  have nd := (List.nodup_append.mp maskRegs.tail.tail).1
  obtain ⟨radix,z₀,t₀,user₀,time₀,prepare⟩ := LabelCountBank.prepareClock_exec body rs
    (caller 28) (caller 45) (caller 58) (caller 59) (caller 60) (caller 61)
    ((by decide : ([28,45,58,59,60,61] : List (Fin 66)).Nodup).map caller.injective)
    (by simp [List.nodup_cons,callerOutside,caller.injective.eq_iff,nd]) initialUser initialState single
    (by intro i hi
        rcases List.mem_append.mp hi with h | h
        · simp only [List.mem_cons,List.not_mem_nil,or_false] at h
          rcases h with rfl | rfl | rfl | rfl <;> apply freePrivate <;> simp [caller]
        · exact freePrivate _ (by have := rsPrivate _ h; omega))
  rw [clockLen] at radix time₀ prepare
  let filled := {initialState with R := R}
  let queued := {filled with R := Function.update filled.R (caller 54) (schedules allLabels)}
  have cleanEq : {queued with L := fun i => if i ∈ privateTapes then [] else filled.L i,
                              R := fun i => if i ∈ privateTapes then [] else queued.R i} = clean := by
    apply Stacks.ext <;> try rfl
    funext i
    by_cases h : i ∈ privateTapes
    · simp [h,clean]
    · have lt : i.val < 58 := by simpa [privateTapes] using h
      have off : i ≠ caller 58 := by intro eq; subst i; change 58 < 58 at lt; omega
      by_cases q : i = caller 54
      · subst i
        simp only [clean,queued,ite_eq_right h,Function.update_self]
      simp [h,clean,queued,q,filled,fillKeep i (fun mem => by have := rsPrivate i mem; omega) off]
  let dim := parentCountPorts.trans caller
  obtain ⟨writer,generateMasks⟩ := countedRecordControls_exec body rankFits
    request table rs sizeRs dim (caller 54) mask mode saved apart (caller.injective.ne (by decide)) (caller.injective.ne (by decide)) (layout 54 (by decide) (by decide)) maskRegs modeRegs
  obtain ⟨y,l,hy,hl,write⟩ := generateMasks directory w Bcount proj reduction dirPositive shape z₀ filled
    radix ((callerKeep 62 (by decide)).trans (freePrivate _ (by change 58 ≤ 62; decide)))
    ((congrArg List.length (callerKeep 29 (by decide))).trans brSize)
    ((congrArg List.length (callerKeep 30 (by decide))).trans rowsSize)
    ((congrArg List.length (callerKeep 31 (by decide))).trans beforeHSize)
    ((congrArg List.length (callerKeep 45 (by decide))).trans clockLen)
    (by intro k hk
        have tmp (j : Fin 66) (hj : 58 < j.val) := (callerKeep j (by intro eq; subst j; omega)).trans
          (freePrivate (caller j) (show 58 ≤ j.val by omega))
        change filled.R (caller (parentCountPorts k)) = []
        rcases parentCountPorts_scratch k hk with h | h
        · rw [h]; exact (callerKeep 50 (by decide)).trans parentsFree
        · exact tmp _ h)
    ((callerKeep 54 (by decide)).trans freeQueue)
    ((callerKeep 57 (by decide)).trans freeMask) ((callerKeep 56 (by decide)).trans freeMode)
  obtain ⟨z,hz,clearMasks⟩ := clearAfterMasks_exec body mask mode privateTapes ((List.nodup_finRange K).filter _)
    (by simp [privateTapes,mask,caller]) (by simp [privateTapes,mode,caller]) liveWords badWords y queued
  let setBits := fun (D : Stacks K prime) => {D with R := Function.update (Function.update D.R mask liveWords) mode badWords}
  change Exec body _ _ _ (mk z (setBits {queued with L := fun i => if i ∈ privateTapes then [] else filled.L i,
                                                     R := fun i => if i ∈ privateTapes then [] else queued.R i})) at clearMasks
  have queueCost : (privateTapes.map fun i => 4*(queued.L i).length+2*(queued.R i).length+4) =
      privateTapes.map (fun i => 4*(initialState.L i).length+2*(R i).length+4) := by
    apply List.map_congr_left
    intro i hi
    have lo : 58 ≤ i.val := by simpa [privateTapes] using hi
    have off : i ≠ caller 54 := by intro eq; subst i; change 58 ≤ 54 at lo; omega
    simp [queued,filled,off]
  rw [cleanEq,queueCost] at clearMasks
  exact ⟨writer,z,_,hz.trans (hy.trans user₀),Nat.add_le_add (Nat.add_le_add time₀ hl) (Nat.add_le_add_right cleanup 1),
    Exec.seq (Exec.seq prepare write) clearMasks⟩

/-- Generate the selector masks and execute all records in directory order. -/
theorem generatedRecordScan_exec [M8.Machine.Net] {T m work Q fields H J W : ℕ} {F U : Type}
    (v : Descriptor) (positive : v.Positive) (w : ℕ) (proj : Matrix (Fin m) (Fin m) ℚ)
    (width : v.width = proj.rank*(w+1)) (idem : proj*proj = proj)
    (factor : Factorization univ univ proj) (hd : ∀ a ∈ factorizationDenominators factor, a < prime)
    (rankFits : proj.rank ≤ m) (parent parentInv : Fin m → ZMod (prime^(w+1)))
    (reciprocal : ∀ i, parent i * parentInv i = 1)
    (io : Fin T) (arity : ℕ)
    (hm : prime^(w+1) < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (length : volume prime v = (prime^(w+1))^fields*((prime^(w+1))^fields*W))
    (capacity : 217 ≤ Q) (source : ℤ → Fin 4) (head : ℤ)
    (fits : LeafCore.small ≤ work) (cap : (LeafCore.core io).states ≤ Q) :
    GeneratedRecordSpec (F := F) (U := U) v positive w proj width idem factor hd rankFits parent parentInv
      reciprocal io arity hm hw hW length capacity source head fits cap false := by
  unfold GeneratedRecordSpec
  intro d common host M N entry leave record bank commonPorts aux hdrPorts logical addr inner caller K ef xf eqs xqs initialWord
    body initialUser initialState poolFits directory prefixes archiveTail allLabels slots headers scanCaller scan joined dirSlots dir pool pivot counters inputs ports a digits prefixWidth zeros
    packedLabel clock count formula detFormula generationBill generate withZero field slot r src dst gs matrices liveBit badBit φ table fallbackCode schedules ready payload
    call cost budget coordinate effects reverse transfer marks loading conversion headerCost raw tripCost runBills prepareCounters prepareHeaders recordProgram
    privateTapes initialClear c bodyBound charge binaryRun binaryCharge mask mode modes skip skipCost ordinaryStep
  have ordinary := generatedOrdinaryRecord_exec v positive w proj width idem factor hd rankFits
    parent parentInv reciprocal io arity hm hw hW length capacity source head fits cap ef xf eqs xqs
    initialWord body initialUser initialState poolFits directory prefixes archiveTail c bodyBound
  have step : ordinaryStep := ordinary.1
  intro room Bcount rs parents shape freePrivate dirPositive brSize rowsSize beforeHSize parentsFree freeMask freeMode freeQueue high initCounters clean initialReady setupCost
  have release (port : Fin 66) (lo : 56 ≤ port.val) (hi : port.val ≤ 57)
      (is : List ℕ) (word : Fin N → ZMod 2) (S : Stacks K prime) (xs : List (Fin (prime+4)))
      (h : ready S is) (p : payload word S) :
      let B := {S with R := Function.update S.R (caller port) xs}
      ready B is ∧ payload word B := by
    refine ⟨DirectoryReady.updateSelector port lo hi xs h,?_⟩
    have right := Function.update_of_ne (caller.injective.ne (show (24 : Fin 66) ≠ port by
      intro eq; subst port; contradiction)) xs S.R
    intro z
    change readAt _ _ (Function.update S.R (caller port) xs (r 0)) _ = _
    rw [show r 0 = caller 24 from recordRoundTripPorts_other slot 0 (by decide),right]
    simpa only [show r 0 = caller 24 from recordRoundTripPorts_other slot 0 (by decide)] using p z
  let liveWords := allLabels.map fun i => bitSymbol (a := prime) (liveBit i)
  let badWords := modes allLabels
  have apart : mask ≠ mode := caller.injective.ne (by decide)
  have rawCaller (j : Fin 58) (off : j.castAdd 8 ≠ (54 : Fin 66)) : clean.R (caller (j.castAdd 8)) = initialState.R (caller (j.castAdd 8)) := by
    have lt : (caller (j.castAdd 8)).val < 58 := j.isLt
    simp [clean,privateTapes,lt.not_ge,Function.update_of_ne (caller.injective.ne off)]
  obtain ⟨_,_,_,_,_,_,unitWord,_,_,_,ticks,_⟩ := And.intro initialReady.1 initialReady.2
  have single : (initialState.R (caller 28)).length = 1 := by
    exact (congrArg List.length (rawCaller 28 (by decide))).symm.trans ((congrArg List.length unitWord).trans (length_binSyms ..))
  have clockLen : (initialState.R (caller 45)).length = w := (congrArg List.length (rawCaller 45 (by decide))).symm.trans ticks
  obtain ⟨writer,z,setupTime,userSetup,setupBound,setupRun⟩ := directoryControls_exec body rankFits
    ((LabelRing.res prime (w+1) (by omega)).mapMatrix (reduce M proj)) table (reduce M proj) rfl
    directory dirPositive shape room initialUser initialState freePrivate single clockLen brSize rowsSize beforeHSize
    parentsFree freeMask freeMode freeQueue
  let liveState := {clean with R := Function.update clean.R mask liveWords}
  let startState := {liveState with R := Function.update liveState.R mode badWords}
  have r₁ : ready liveState allLabels := DirectoryReady.updateSelector 57 (by decide) (by decide) _ initialReady
  have r₂ : ready startState allLabels := DirectoryReady.updateSelector 56 (by decide) (by decide) _ r₁
  have payloadPort : r 0 = caller 24 := recordRoundTripPorts_other slot 0 (by decide)
  have cellL : startState.L (r 0) = initialState.L (r 0) := by
    simp [startState,liveState,clean,privateTapes,payloadPort,caller]
  have cellR : startState.R (r 0) = initialState.R (r 0) := by
    rw [payloadPort]
    simp [startState,liveState,clean,privateTapes,mask,mode,caller,Function.update_of_ne]
    exact Function.update_of_ne (caller.injective.ne (by decide : (24 : Fin 66) ≠ 54)) _ _
  have payloadKept (h : payload initialWord clean) : payload initialWord startState :=
    (release 56 (by decide) (by decide) _ _ liveState badWords r₁
      (release 57 (by decide) (by decide) _ _ clean liveWords initialReady h).2).2
  have bits : startState.R mask = liveWords := (Function.update_of_ne apart badWords liveState.R).trans
    (Function.update_self mask liveWords clean.R)
  have initialModes : startState.R mode = badWords := Function.update_self mode badWords liveState.R
  change Exec body ((initCounters.seq writer).seq (clearWorkTapes privateTapes))
    (mk initialUser initialState) setupTime (mk z startState) at setupRun
  change setupTime ≤ setupCost at setupBound
  have projectorKept : startState.R (caller 48) = initialState.R (caller 48) := by
    have outside : caller 48 ∉ privateTapes := by simp [privateTapes,caller]
    have ne (j : Fin 66) (hj : (48 : Fin 66) ≠ j) := caller.injective.ne hj
    simp only [startState,liveState,mode,mask,clean,Function.update_of_ne (ne 56 (by decide)),
      Function.update_of_ne (ne 57 (by decide)),ite_eq_right outside,Function.update_of_ne (ne 54 (by decide))]
  refine ⟨writer,z,startState,_,userSetup,setupBound,setupRun,r₂,step,cellL,cellR,projectorKept,bits,initialModes,?_,?_⟩
  · intro dimension archiveRoom placement archive outer calls v B control bank
    obtain ⟨y,E,run,_,user,localBank,frame⟩ := exec_emb placement.injective calls setupRun v control B bank
    have same := user.trans (userSetup.trans (congrArg HS.user control).symm)
    have kept := (frame archive (Fin.succAbove_ne _)).2
    refine ⟨y,E,same,localBank,kept,run,?_⟩
    intro initialPayload data dim anchor states fieldsEq extra push bounded binary count empty scanBody e action
    subst Q
    subst fields
    subst H
    have archiveRun := (ordinary.2.2 dimension dim data archiveRoom anchor rfl rfl rfl outer calls push bounded y E).2 extra
    have port : r 0 = caller 24 := recordRoundTripPorts_other slot 0 (by decide)
    have readyStart : ready (embStk placement E) allLabels := localBank ▸ r₂
    have payloadStart : payload initialWord (embStk placement E) := localBank ▸ payloadKept initialPayload
    have liveStart := (congrArg (fun A => Stacks.R A mask) localBank).trans bits
    have modeStart := (congrArg (fun A => Stacks.R A mode) localBank).trans initialModes
    obtain ⟨build,finish,final,h,t,next,hu,done,history,emptyArchive,emptyLive,emptyBad,_,_,volumeTime,_,scan⟩ := archiveRun
      (by constructor
          · simpa only [List.drop_zero,count] using readyStart
          · simpa only [payload,port] using payloadStart)
      (kept.trans empty)
      (by rw [← directoryOrdinaryBank_caller archiveRoom 57,count]; exact liveStart)
      (by rw [← directoryOrdinaryBank_caller archiveRoom 56,count]; exact modeStart)
    refine ⟨_,finish,final,h+t,next,hu.trans same,?_,?_,?_,emptyArchive,emptyLive,emptyBad,?_,Exec.seq run scan⟩
    · simpa only [List.drop_length,List.length_range,List.drop_eq_nil_of_le (List.length_range.le)] using done.1
    · simpa only [payload,port] using done.2
    · simpa only [count] using history
    · intro precision weight baseline V suffix archiveBudget scratch p setup labels rate left controls overhead power ordinaryRate rare terminal
      have ceiling : (if 0 < d ∧ data.H = M.size ∧ J = W.size then min (charge 0) binaryCharge else charge 0) + N ≤ baseline := by
        simp only [precision,weight,true_and,and_true,baseline,le_refl]
      have recordsPos : 0 < data.records := by
        rw [count,LabelMask.records]
        exact Nat.mul_pos (Nat.mul_pos dirPositive.1 dirPositive.2.1) dirPositive.2.2.1
      have parentsCount : data.records = (directory.beforeRows*directory.rows*Bcount)*M^(m*m) := by
        rw [count,LabelMask.records,shape]
        dsimp only [M]
        rw [← pow_mul]
        ring_nf
      have writerPush : mnProgPush build ≤ p := (le_max_left ..).trans (le_max_left ..)
      have bodyPush (f) : mnProgPush (outer f) ≤ p := (bounded f).trans (le_max_right ..)
      have placed (j : Fin 66) : placement (caller j) = j.castAdd (host+31+work+1) := directoryOrdinaryBank_caller archiveRoom j
      have widthEq := readyStart.2.1 0 (show 0 ∈ allLabels by simpa [allLabels,← count] using recordsPos)
      change (E.R (placement (caller 47))).length = (prefixes 0).length at widthEq
      rw [placed] at widthEq
      have total := (volumeTime p writerPush bodyPush precision hW recordsPos).2 _ baseline parentsCount weight ceiling
      have projectorEq : E.R ((48 : Fin 66).castAdd (host+31+work+1)) = initialState.R (caller 48) := by
        rw [← placed]
        change (embStk placement E).R (caller 48) = _
        rw [localBank]
        exact projectorKept
      have posM : 0 < M := pow_pos Networks.Shared50ModularControl.prime_prime.pos _
      have radix : M ≤ N := by
        dsimp only [N]
        rw [← directoryPayloadLength e length,pow_succ]
        exact (Nat.le_mul_of_pos_left _ (pow_pos posM dimension)).trans (Nat.le_mul_of_pos_right _ hW)
      have boxCount := (Nat.le_mul_of_pos_right (directory.beforeRows*directory.rows*Bcount)
        (pow_pos posM (m*m))).trans_eq parentsCount.symm
      have controlCost := maskSetup_volume_le m w data.records (directory.beforeRows*directory.rows*Bcount)
        privateTapes.length left (data.records*N) (radix.trans (Nat.le_mul_of_pos_left _ recordsPos))
        (Nat.le_mul_of_pos_right _ (posM.trans_le radix)) boxCount
      rw [count] at controlCost
      have maskBound : _ ≤ controls := setupBound.trans (by simpa only [controls,setupCost,high,count,allLabels,List.length_range,left] using controlCost)
      have normalize (k : ℕ) (bound : k ≤ controls) :
          k+(h+t) ≤ overhead + (data.records*(baseline+6)+2 + (labels*data.records/prime)*(rate*N)) := by
        dsimp only [overhead,setup,archiveBudget,suffix,V]
        rw [← projectorEq,← widthEq,Nat.add_assoc controls]
        exact Nat.add_le_add bound total
      have bill := normalize _ maskBound
      have full := exceptionalBatchCost_le _ _ _ _ _ _ _ bill
      refine ⟨?_,bill,full⟩
      intro active
      have split : ((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau = power := atomPower_eq _ d w active width
      have ordinaryBound : (baseline : ℝ) ≤ ordinaryRate := by
        have coordinates := directoryCoordinateTime_le m d w N (LeafCore.core io).tapes
          (packedLeafPush (F := Empty) (U := U) io Empty.elim) entry.tapes leave.tapes radix
        change (budget : ℝ) ≤ _ at coordinates
        have baseBound : baseline ≤ binaryCharge+N := by
          dsimp only [baseline]; rw [if_pos active]; exact Nat.add_le_add_right (min_le_right ..) _
        apply (Nat.cast_le (α := ℝ)).mpr baseBound |>.trans
        dsimp only [binaryCharge,binaryRun]
        dsimp only [ordinaryRate]
        rw [split] at coordinates
        push_cast
        have scaled := mul_le_mul_of_nonneg_left coordinates (Nat.cast_nonneg (α := ℝ) (max (mnProgPush recordProgram) c))
        push_cast at scaled
        nlinarith only [coordinates,scaled]
      have rareBound : (rate : ℝ) ≤ rare := by
        dsimp only [rare]
        rw [← split]
        exact exceptionalVolumeRate_le ..
      have terminalBound := full.trans (batchRate_mono overhead data.records labels N ordinaryBound rareBound)
      refine ⟨ordinaryBound,by simpa only [terminal,Nat.cast_mul] using terminalBound,?_⟩
      intro ι gap adapter time chain root descend fit endpoint base suffixWidth splitWidth spectators
      have batchVolume : data.records*N = volume prime root := by
        rw [← rankDescriptor_volume (M := prime) root (Nat.sub_add_cancel fit).symm, endpoint]
        dsimp only [N]
        rw [length,count,spectators]
        simp only [LabelMask.records,volume,splitWidth,pow_add,pow_mul,Nat.mul_comm m (w+1),two_mul suffixWidth]
        ring
      have nested := rankDescriptor_chain_time gap adapter time descend chain root fit
      rw [endpoint] at nested
      have elapsed := nested.trans (Nat.add_le_add_right base _)
      exact (Nat.cast_le (α := ℝ)).mpr elapsed |>.trans (by
        rw [Nat.cast_add,Nat.cast_mul]
        apply add_le_add _ (le_refl _)
        rw [← batchVolume]
        simpa only [terminal,Nat.cast_mul] using terminalBound)
  intro initialPayload fallback badCost badEffect bad branchCost action exceptional priced
  suffices scanRun : ∃ finish D n next, finish.user = z.user ∧
      n ≤ (allLabels.map fun i => branchCost i+2+4).sum+2 ∧
      Exec body (classifiedScan mask mode (recordProgram.seq (clearWorkTapes privateTapes)) fallback skip)
        (mk z startState) n (mk finish D) ∧ (ready D [] ∧ D.R mode = modes []) ∧ D.R mask = [] ∧ payload next D ∧
      allLabels.foldr (fun i rest x => ∃ y, action i x y ∧ rest y) (· = next) initialWord by
    obtain ⟨finish,D,n,next,user,time,run,post⟩ := scanRun
    refine ⟨finish,D,_,next,user.trans userSetup,Nat.add_le_add setupBound time,?_,
      Exec.seq setupRun run,post⟩
    intro baseline parentBudget choice ordinary fitsParent fallbackFits
    obtain ⟨extra,allowance,fitsRecord⟩ := fallbackAllowance allLabels badCost
      (fun j => liveBit j = true ∧ badBit j = true) exceptional baseline (parentBudget-ordinary)
      (fun pos j hj h => fallbackFits pos j hj h.1 h.2)
    have base : charge 0 ≤ baseline := by
      rcases choice with direct | ⟨active,binary,trailingBits,limit⟩
      · exact direct
      exact (generatedCharge_binary_le m w d W _ raw budget initialClear (max (mnProgPush recordProgram) c)
        H J v positive width ⟨active,binary,trailingBits⟩).trans limit
    have sameWidth (j : ℕ) (hj : j ∈ allLabels) : (prefixes j).length = (prefixes 0).length := by
      have first : 0 ∈ allLabels := List.mem_range.mpr (Nat.zero_lt_of_lt (List.mem_range.mp hj))
      exact (initialReady.2.1 j hj).symm.trans (initialReady.2.1 0 first)
    have sameCharge (j : ℕ) (hj : j ∈ allLabels) : charge j = charge 0 := by
      simp only [charge,runBills,sameWidth j hj]
    have skipBound (j : ℕ) (hj : j ∈ allLabels) : skipCost j ≤ charge 0 := by
      rw [← sameCharge j hj]
      exact (Nat.le_add_left _ _).trans (Nat.le_add_right (runBills j) _)

    obtain ⟨g₀,unit,generic⟩ := LabelProjector.residue_witness (w := w+1) (by omega) proj idem factor hd rankFits
    have total := Nat.add_le_add setupBound
      (time.trans (directoryDispatchCost_le w d Bcount rankFits (reduce M proj) directory shape charge skipCost badCost
        baseline extra g₀ unit generic (fun j hj _ _ => (sameCharge j hj).le.trans base) (fun j hj _ => (skipBound j hj).trans base)
        (fun j hj live badLabel => fitsRecord j hj ⟨live,badLabel⟩)))
    change _ ≤ setupCost + (allLabels.length*(baseline+6) + exceptional*extra + 2) at total
    dsimp only [ordinary] at fitsParent allowance
    omega
  apply classifiedPayloadScan_exec body mask mode (caller.injective.ne (by decide)) _ fallback skip liveBit badBit
    branchCost (fun is D => ready D is) payload action _ _ allLabels initialWord z startState
    r₂ (payloadKept initialPayload) bits initialModes
  · intro k hk
    rcases hk with rfl | rfl
    · exact release 57 (by decide) (by decide)
    · exact release 56 (by decide) (by decide)
  · intro label labels word u whole start input
    let ok := fun price program (effect : (Fin N → ZMod 2) → (Fin N → ZMod 2) → Prop) =>
      ∃ z D n next, z.user = u.user ∧ n ≤ price ∧ Exec body program (mk u whole) n (mk z D) ∧
        ready D labels ∧ effect word next ∧ payload next D ∧ D.R mask = whole.R mask ∧ D.R mode = whole.R mode
    exact classifiedStep ok (liveBit label) (badBit label) (charge label) (badCost label) (skipCost label)
      _ fallback skip (effects label) (badEffect label) Eq
      (fun h => step label labels word u whole h start input)
      (fun live fail => bad label labels word u whole live fail start input)

end IntegerMultBounds.MathlibTM2.Cover.Fallback
