module

public import IntegerMultBounds.MathlibTM2.M6.BitStageDimensions
public import IntegerMultBounds.MathlibTM2.Cover.FallbackControlDigit

/-! Recover the number of blocks from the label count and the row count. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
variable {T Q A : ℕ} {P U : Type}

def stageBlockCount (r : Fin 11 ↪ Fin T) : Pr P T Q A U :=
  .seq (divide true r) (Routing.binaryCanonicalProgram (r 2) (r 3))

/-- The bit-length product in schoolbook division is linear in the dividend
when the divisor is a positive factor of it. -/
theorem stageBlockCountTime_le (B N : ℕ) (hb : 0 < B) (hn : 0 < N) :
    (B*N).size*(12*N.size+39)+22*N.size+44 ≤ 153*(B*N) := by
  let L := B*N
  have pos : 0 < L := Nat.mul_pos hb hn
  have s : L.size ≤ L := Nat.size_le.mpr Nat.lt_two_pow_self
  have n : N.size ≤ L.size := Nat.size_le_size (Nat.le_mul_of_pos_left _ hb)
  have sq : L.size*L.size ≤ 4*L := by simpa only [pow_two] using size_square_le L pos
  have cross := (Nat.mul_le_mul_left L.size n).trans sq
  change L.size*(12*N.size+39)+22*N.size+44 ≤ 153*L
  nlinarith only [cross,n,s,pos]

theorem stageBlockCount_exec (body : P → Pr P T Q A U) (r : Fin 11 ↪ Fin T)
    (B N : ℕ) (hn : 0 < N) (u : HS T Q A U) (S : Stacks T A)
    (labels : S.R (r 0) = binSyms (B*N).size (B*N))
    (rows : S.R (r 1) = binSyms N.size N)
    (free : ∀ i : Fin 11, 2 ≤ i → i < 10 → S.R (r i) = []) :
    ∃ z t, z.user = u.user ∧ t ≤ (B*N).size*(12*N.size+39)+22*N.size+44 ∧
      Exec body (stageBlockCount r) (mk u S) t
        (mk z {S with R := Function.update S.R (r 2) (binSyms B.size B)}) := by
  obtain ⟨y,k,user,price,quot⟩ := divide_exec body true r _ _ _ _ (Nat.lt_size_self _) (Nat.lt_size_self _)
    hn u S labels rows free
  simp only [ite_true,Nat.mul_div_cancel _ hn] at quot price
  let F := {S with R := Function.update S.R (r 2) (binSyms (B*N).size B)}
  have fits := (Nat.le_mul_of_pos_right B hn).trans_lt (Nat.lt_size_self _)
  obtain ⟨bs,z,canonical,value,_,same,trim⟩ := Routing.binaryCanonical_exec body (r 2) (r 3)
    (r.injective.ne (by decide)) _ B fits y F (Function.update_self ..)
    ((Function.update_of_ne (r.injective.ne (by decide : (3 : Fin 11) ≠ 2)) _ _).trans (free 3 (by decide) (by decide)))
  have eq := BinaryCanonicalData.value_injective bs _ canonical (FlatCoordinateSchedule.bits_canonical B)
    (value.trans (FlatCoordinateSchedule.bits_value _).symm)
  rw [eq,canonicalBits_symbols] at trim
  refine ⟨z,k+(4*(B*N).size+6),same.trans user,?_,?_⟩
  · nlinarith only [price]
  · simpa only [F,stageBlockCount,Function.update_idem] using Exec.seq quot trim

/-- Register 14 holds the label count from the parent. The divisor is the
same row count used by the scan and stays in register 1 after division. -/
def stageDivisionPorts : Fin 11 ↪ Fin 15 := ⟨![14,1,5,7,8,9,10,11,12,13,0],by decide⟩

theorem stageRowsAndBlocks_exec (body : P → Pr P T Q Shared50ModularControl.prime U)
    (r : Fin 15 ↪ Fin T) (w B : ℕ) (hb : 0 < B)
    (u : HS T Q Shared50ModularControl.prime U) (S : Stacks T Shared50ModularControl.prime) :
    let M := Shared50ModularControl.prime^w
    let N := Shared50ModularControl.prime^(64*(w*64))
    let bank := (Fin.castAddEmb 1 (n := 14)).trans r
    S.R (r 6) = binSyms M.size M → S.R (r 4) = binSyms 1 1 →
    S.R (r 14) = binSyms (B*N).size (B*N) →
    (∀ j : Fin 15, j.val ∈ [1,5,7,8,9,10,11,12,13] → S.R (r j) = []) →
    ∃ z t, z.user = u.user ∧ t ≤ stagePowerTime M 1 4096+153*(B*N) ∧
      Exec body (.seq (swapPrefix ((stagePowerPorts 1).trans bank) (stageDegrees 1))
        (stageBlockCount (stageDivisionPorts.trans r))) (mk u S) t
        (mk z {S with R := Function.update (Function.update S.R (r 1) (binSyms N.size N)) (r 5) (binSyms B.size B)}) := by
  intro M N bank base unit labels free
  have one : S.R (r 4) = binSyms (Nat.size 1) 1 := by rwa [Nat.size_one]
  obtain ⟨v,k,user,paid,row⟩ := stagePower_exec body bank 1 M 1 u S base one (free 1 (by decide))
    (fun i hi => free (i.castAdd 1) ((by decide : ∀ i : Fin 14, 7 ≤ i.val →
      (i.castAdd 1).val ∈ [1,5,7,8,9,10,11,12,13]) i hi))
  have eq : M^(stageDegrees 1)*1 = N := stagePowerValues w B 1 1
  rw [eq] at row
  let F := {S with R := Function.update S.R (r 1) (binSyms N.size N)}
  have keep (j : Fin 15) (h : j ≠ 1) : F.R (r j) = S.R (r j) := Function.update_of_ne (r.injective.ne h) _ _
  have hn : 0 < N := pow_pos Shared50ModularControl.prime_prime.pos _
  obtain ⟨z,m,same,cost,blocks⟩ := stageBlockCount_exec body (stageDivisionPorts.trans r) B N hn v F
    ((keep 14 (by decide)).trans labels) (Function.update_self ..) (fun i lo hi => by
      obtain ⟨ne,mem⟩ := (by decide : ∀ i : Fin 11, 2 ≤ i → i < 10 → stageDivisionPorts i ≠ 1 ∧
        (stageDivisionPorts i).val ∈ [1,5,7,8,9,10,11,12,13]) i lo hi
      exact (keep _ ne).trans (free _ mem))
  exact ⟨z,k+m,same.trans user,Nat.add_le_add paid (cost.trans (stageBlockCountTime_le B N hb hn)),
    Exec.seq row blocks⟩

/-- Use the freshly computed row count for exact division before forming the
block counter. Its canonical word is retained for the target scan. -/
noncomputable def stageHeadersFromLabels (r : Fin 15 ↪ Fin T) : Pr P T Q A U :=
  let bank := (Fin.castAddEmb 1 (n := 14)).trans r
  let power := fun i => swapPrefix ((stagePowerPorts i).trans bank) (stageDegrees i)
  let dst := (Fin.castAddEmb 12 (n := 3)).trans r
  .seq (.seq (power 1) (stageBlockCount (stageDivisionPorts.trans r)))
    (.seq (power 0) (.seq (power 2) (.act (pushMarkers ((List.finRange 3).map dst)))))

theorem stageHeadersFromLabels_exec (body : P → Pr P T Q Shared50ModularControl.prime U)
    (r : Fin 15 ↪ Fin T) (w B W : ℕ) (hb : 0 < B)
    (u : HS T Q Shared50ModularControl.prime U) (S : Stacks T Shared50ModularControl.prime) :
    let M := Shared50ModularControl.prime^w
    let N := Shared50ModularControl.prime^(64*(w*64))
    let values := (![M^112*W,N,M^16*B] : Fin 3 → ℕ)
    let dst := (Fin.castAddEmb 12 (n := 3)).trans r
    S.R (r 6) = binSyms M.size M → S.R (r 4) = binSyms 1 1 →
    S.R (r 3) = binSyms W.size W → S.R (r 14) = binSyms (B*N).size (B*N) →
    (∀ i, S.L (dst i) = []) →
    (∀ j : Fin 15, j.val ∈ [0,1,2,5,7,8,9,10,11,12,13] → S.R (r j) = []) →
    ∃ z F t, z.user = u.user ∧
      t ≤ stagePowerTime M W 112 + stagePowerTime M 1 4096 + stagePowerTime M B 16 + 153*(B*N)+1 ∧
      Exec body (stageHeadersFromLabels r)
        (mk u S) t (mk z F) ∧
      (∀ i, F.L (dst i) = [separator] ∧ F.R (dst i) = binSyms (values i).size (values i)) ∧
      ∀ j, j ≠ r 5 → (∀ i, dst i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro M N values dst base unit tailWord labels left free
  let bank := (Fin.castAddEmb 1 (n := 14)).trans r
  let word := fun a : ℕ => binSyms (A := Shared50ModularControl.prime) a.size a
  obtain ⟨v,k,user,paid,rows⟩ := stageRowsAndBlocks_exec body r w B hb u S base unit labels (fun j hj =>
    free j ((by decide : ∀ j : Fin 15, j.val ∈ [1,5,7,8,9,10,11,12,13] →
      j.val ∈ [0,1,2,5,7,8,9,10,11,12,13]) j hj))
  let A := {S with R := Function.update (Function.update S.R (r 1) (word N)) (r 5) (word B)}
  have keep (j) (h : j ≠ r 1) (h' : j ≠ r 5) : A.R j = S.R j :=
    (Function.update_of_ne h' _ _).trans (Function.update_of_ne h _ _)
  have old (i : Fin 15) (h : i ≠ 1) (h' : i ≠ 5) := keep _ (r.injective.ne h) (r.injective.ne h')
  have fresh (i : Fin 14) (hi : 7 ≤ i.val) : A.R (bank i) = [] := by
    obtain ⟨ne,ne',mem⟩ := (by decide : ∀ i : Fin 14, 7 ≤ i.val → i.castAdd 1 ≠ 1 ∧
      i.castAdd 1 ≠ 5 ∧ i.val ∈ [0,1,2,5,7,8,9,10,11,12,13]) i hi
    exact (old _ ne ne').trans (free _ mem)
  have radix := (old 6 (by decide) (by decide)).trans base
  obtain ⟨v',m,same,price,width⟩ := stagePower_exec body bank 0 M W v A radix
    ((old 3 (by decide) (by decide)).trans tailWord)
    ((old 0 (by decide) (by decide)).trans (free 0 (by decide))) fresh
  let C := {A with R := Function.update A.R (r 0) (word (M^112*W))}
  have kept (i : Fin 15) (h : i ≠ 0) : C.R (r i) = A.R (r i) :=
    Function.update_of_ne (r.injective.ne h) _ _
  obtain ⟨z,n,last,cost,blocks⟩ := stagePower_exec body bank 2 M B v' C
    ((kept 6 (by decide)).trans radix) ((kept 5 (by decide)).trans (Function.update_self ..))
    ((kept 2 (by decide)).trans ((old 2 (by decide) (by decide)).trans (free 2 (by decide))))
    (fun i hi => (kept (i.castAdd 1) (by intro eq; have h := congrArg Fin.val eq; change i.val = 0 at h; omega)).trans (fresh i hi))
  let F := {C with R := Function.update C.R (r 2) (word (M^16*B))}
  have mark := Exec.act (body := body) (pushMarkers ((List.finRange 3).map dst)) (mk z F)
  rw [pushMarkers_run _ ((List.nodup_finRange 3).map dst.injective)] at mark
  refine ⟨z,_,k+(m+(n+1)),last.trans (same.trans user),?_,Exec.seq rows (Exec.seq width (Exec.seq blocks mark)),?_,?_⟩
  · change k ≤ stagePowerTime M 1 4096+153*(B*N) at paid
    change m ≤ stagePowerTime M W 112 at price
    change n ≤ stagePowerTime M B 16 at cost
    omega
  · intro i
    refine ⟨by simp [F,C,A,left,List.mem_finRange],?_⟩
    change F.R (dst i) = _
    fin_cases i
    · change F.R (r 0) = _
      simp [F,C,word,values,r.injective.eq_iff]
    · change F.R (r 1) = _
      simp [F,C,A,word,values,r.injective.eq_iff]
    · exact Function.update_self ..
  · intro j blockOff outside
    refine ⟨by simp [F,C,A,outside],?_⟩
    exact (Function.update_of_ne (outside 2).symm _ _).trans
      ((Function.update_of_ne (outside 0).symm _ _).trans (keep j (outside 1).symm blockOff))

/-- Read the parent label word, radix and unit in place. The exterior product
is already in the shared register 10. Registers 0–2 receive the scan headers. -/
def stageHeaderLayout : Fin 15 ↪ Fin 41 ⊕ Fin 14 :=
  ⟨![.inr 0,.inr 1,.inr 2,.inr 10,.inl 34,.inr 12,.inl 8,.inr 3,.inr 4,.inr 5,
    .inr 6,.inr 7,.inr 8,.inr 9,.inl 2],by decide⟩

def stageHeaderBank {J G : ℕ} (frame : Fin 41 ↪ Fin J) : Fin 15 ↪ Fin (J+14+G) :=
  ((stageHeaderLayout.trans (frame.sumMap (Function.Embedding.refl _))).trans
    finSumFinEquiv.toEmbedding).trans (Fin.castAddEmb G)

private theorem threePrices (f : Fin 3 → ℕ) :
    ((List.finRange 3).map f).sum = f 0+(f 1+f 2) := by
  change f 0+(f 1+(f 2+0)) = _
  rw [Nat.add_zero]

theorem stageHeaderBank_exec {J G : ℕ} (body : P → Pr P (J+14+G) Q Shared50ModularControl.prime U)
    (frame : Fin 41 ↪ Fin J) (w B W : ℕ) (hb : 0 < B)
    (u : HS (J+14+G) Q Shared50ModularControl.prime U) (S : Stacks (J+14+G) Shared50ModularControl.prime) :
    let reg := fun i : Fin 14 => (i.natAdd J).castAdd G
    let parent := fun i => ((frame i).castAdd 14).castAdd G
    let M := Shared50ModularControl.prime^w
    let N := Shared50ModularControl.prime^(64*(w*64))
    let seed := (![W,1,B] : Fin 3 → ℕ)
    let values := (![M^112*W,N,M^16*B] : Fin 3 → ℕ)
    S.R (parent 8) = binSyms M.size M → S.R (parent 34) = binSyms 1 1 →
    S.R (reg 10) = binSyms W.size W → S.R (parent 2) = binSyms (B*N).size (B*N) →
    S.R (reg 12) = [] →
    (∀ i : Fin 3, S.L (reg (i.castAdd 11)) = [] ∧ S.R (reg (i.castAdd 11)) = []) →
    (∀ j : Fin 7, S.R (reg ((j.natAdd 3).castAdd 4)) = []) →
    ∃ z F t, z.user = u.user ∧
      t ≤ ((List.finRange 3).map (fun i => stagePowerTime M (seed i) (stageDegrees i))).sum+2+153*(B*N) ∧
      Exec body (stageHeadersFromLabels (stageHeaderBank frame)) (mk u S) t (mk z F) ∧
      (∀ i : Fin 3, F.L (reg (i.castAdd 11)) = [separator] ∧
        F.R (reg (i.castAdd 11)) = binSyms (values i).size (values i)) ∧
      ∀ j, reg 12 ≠ j → (∀ i : Fin 3, reg (i.castAdd 11) ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro reg parent M N seed values radix unit tail labels blockFree hdr scratch
  obtain ⟨z,F,t,user,paid,exec,ready,keep⟩ := stageHeadersFromLabels_exec body (stageHeaderBank frame) w B W hb u S
    radix unit tail labels (fun i => by fin_cases i <;> first | exact (hdr 0).1 | exact (hdr 1).1 | exact (hdr 2).1)
    (fun j hj => by
      fin_cases j <;> simp at hj
      all_goals first | exact (hdr 0).2 | exact (hdr 1).2 | exact (hdr 2).2 | exact blockFree | (first | exact scratch 0 | exact scratch 1 | exact scratch 2 | exact scratch 3 | exact scratch 4 | exact scratch 5 | exact scratch 6))
  refine ⟨z,F,t,user,?_,exec,?_,?_⟩
  · rw [threePrices]
    change t ≤ stagePowerTime M W 112+(stagePowerTime M 1 4096+stagePowerTime M B 16)+2+153*(B*N)
    change t ≤ stagePowerTime M W 112+stagePowerTime M 1 4096+stagePowerTime M B 16+153*(B*N)+1 at paid
    omega
  · intro i
    fin_cases i <;> first | exact ready 0 | exact ready 1 | exact ready 2
  · intro j blockOff outside
    exact keep j blockOff.symm (fun i => by fin_cases i <;> first | exact outside 0 | exact outside 1 | exact outside 2)

end IntegerMultBounds.MathlibTM2.M6.BitNode
