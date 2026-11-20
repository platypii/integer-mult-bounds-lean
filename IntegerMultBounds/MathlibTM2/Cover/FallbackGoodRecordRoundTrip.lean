module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodCoordinates
public import IntegerMultBounds.MathlibTM2.Cover.FallbackRecordVolumeHeaders

/-! Stage the caller word, run the weighted coordinate loop, and return the result. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open M8.RevMachine RecursiveInterchangeLayout Matrix Finset IntegerMultBounds.Swap.LowerTriangular
  IntegerMultBounds.Swap.Modular
local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨pow_ne_zero _ Networks.Shared50ModularControl.prime_prime.ne_zero⟩

/-- Archive input and matrix conversion on a record with padded and binary field widths. -/
def recordWeightLoadTime (m w H bits : ℕ) :=
  ((6*(m*H)+6)+((10*H+12)+(m*(10*bits+8*(H-bits)+12)+1+(2*(m*bits)+2))))+
    ((10*bits+10)+(6*w+6))

def recordMatrixLoadTime (m H bits : ℕ) :=
  (m*m)*(10*bits+8*(H-bits)+12)+1+(2*(m*m*bits)+2)

/-- Every archive field costs at most a constant per payload cell when
the field widths and clock fit the volume. -/
theorem recordLoadTime_le (m w H bits V : ℕ) (pos : 0 < V) (clock : w ≤ V)
    (field : H ≤ V) (binary : bits ≤ V) :
    recordWeightLoadTime m w H bits + recordMatrixLoadTime m H bits ≤
      (recordWeightLoadTime m 1 2 1 + recordMatrixLoadTime m 2 1)*V := by
  unfold recordWeightLoadTime recordMatrixLoadTime
  have pad := (Nat.sub_le H bits).trans field
  grw [pad,binary,field,clock]
  have one : 1 ≤ V := pos
  have linear := Nat.le_mul_of_pos_right m pos
  have square := Nat.le_mul_of_pos_right (m*m) pos
  nlinarith only [one,linear,square]

/-- At binary archive width the modulus itself covers both the clock and
the field length. -/
theorem recordLoadTime_binary_le (m w V : ℕ) (radix : prime^(w+1) ≤ V) :
    let bits := (prime^(w+1)).size
    recordWeightLoadTime m w bits bits + recordMatrixLoadTime m bits bits ≤
      (recordWeightLoadTime m 1 2 1 + recordMatrixLoadTime m 2 1)*V := by
  intro bits
  have hp := Networks.Shared50ModularControl.prime_prime
  have size : bits ≤ V := (Nat.size_le.mpr Nat.lt_two_pow_self).trans radix
  have clock : w ≤ V := (Nat.le_succ w).trans ((Nat.lt_two_pow_self.le).trans
    ((Nat.pow_le_pow_left hp.two_le (w+1)).trans radix))
  exact recordLoadTime_le _ _ _ _ _ ((pow_pos hp.pos _).trans_le radix) clock size size

def recordRoundTripRate (m : ℕ) :=
  recordWeightLoadTime m 1 2 1 + recordMatrixLoadTime m 2 1 + 6000

/-- Binary counters and both payload moves cost a constant per payload cell,
uniformly in the number of fields. -/
theorem recordRoundTripCost_le (m w fields W V budget : ℕ) (positive : 0 < W)
    (radix : prime^(w+1) ≤ V) (volumeEq : V = (prime^(w+1))^fields*((prime^(w+1))^fields*W)) :
    let M := prime^(w+1)
    let H := M.size
    (dimensionTime H 1 fields+(4*(fields*H+1)+6)+(10*W.size+12)+(6*(M^fields).size+6)) +
      (recordWeightLoadTime m w H H+(recordMatrixLoadTime m H H+(budget+2*((218*V+1)*13+6)+3))) ≤
      budget + recordRoundTripRate m*V := by
  intro M H
  let P := M^fields
  have two : 2 ≤ M := le_trans Networks.Shared50ModularControl.prime_prime.two_le
    (Nat.le_self_pow (by omega : w+1 ≠ 0) prime)
  have bits : H ≤ M := Nat.size_le.mpr Nat.lt_two_pow_self
  have count (n : ℕ) : n*M ≤ M^n := by
    induction n with
    | zero => simp
    | succ n ih =>
      cases n with
      | zero => simp
      | succ n =>
        have hm : M ≤ M^(n+1) := Nat.le_self_pow (by omega) M
        rw [Nat.succ_mul,pow_succ]
        exact (Nat.add_le_add ih hm).trans (by simpa [Nat.mul_two] using Nat.mul_le_mul_left (M^(n+1)) two)
  have fh : fields*H ≤ P := (Nat.mul_le_mul_left _ bits).trans (count fields)
  have fp : fields ≤ P := (Nat.le_mul_of_pos_right fields (by omega : 0 < M)).trans (count fields)
  have pp : 0 < P := pow_pos (by omega : 0 < M) _
  have square : P*P ≤ V := by rw [volumeEq]; exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ positive)
  have pv : P ≤ V := (Nat.le_mul_of_pos_right _ pp).trans square
  have tail : W.size ≤ V := by
    apply (Nat.size_le.mpr Nat.lt_two_pow_self).trans
    rw [volumeEq]; exact (Nat.le_mul_of_pos_left _ pp).trans (Nat.le_mul_of_pos_left _ pp)
  have plen : P.size ≤ V := (Nat.size_le.mpr Nat.lt_two_pow_self).trans pv
  have posV := pp.trans_le pv
  have dim := dimensionTime_le H 1 fields
  have quad := (Nat.mul_le_mul fh fh).trans square
  have mixed := (Nat.mul_le_mul fp fh).trans square
  have counter : dimensionTime H 1 fields ≤ 130*V := by
    nlinarith only [dim,quad,mixed,fh.trans pv,fp.trans pv,posV]
  have load := recordLoadTime_binary_le m w V radix
  change recordWeightLoadTime m w H H + recordMatrixLoadTime m H H ≤ _ at load
  change _ + (4*(fields*H+1)+6) + (10*W.size+12) + (6*P.size+6) + _ ≤ _
  rw [recordRoundTripRate,Nat.add_mul (recordWeightLoadTime m 1 2 1 + recordMatrixLoadTime m 2 1) 6000 V]
  omega

theorem goodRecordRoundTrip_exec [M8.Machine.Net] {T m work Q fields H J W : ℕ} {F U : Type}
    (v : Descriptor) (positive : v.Positive) (w : ℕ) (proj : Matrix (Fin m) (Fin m) ℚ)
    (width : v.width = proj.rank*(w+1)) (idem : proj*proj = proj)
    (factor : Factorization univ univ proj) (hd : ∀ a ∈ factorizationDenominators factor, a < prime)
    (label : ℕ) (live : LabelStock.live m (w+1) 1 label = true)
    (rankFits : proj.rank ≤ m) (parent parentInv : Fin m → ZMod (prime^(w+1)))
    (reciprocal : ∀ i, parent i * parentInv i = 1)
    (io : Fin T) (roles : Tapes T prime)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime)
    (arity : ℕ) (st : Tapes 2 prime) (freeNode : Family.NodeFree node)
    (hm : prime^(w+1) < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (length : volume prime v = (prime^(w+1))^fields*((prime^(w+1))^fields*W))
    (capacity : 217 ≤ Q) (source : ℤ → Fin 4) (head : ℤ)
    (fits : LeafCore.small ≤ work) (cap : (LeafCore.core io).states ≤ Q) :
    let d := proj.rank
    let common := CommonBank.count T
    let host := common+24
    let M := prime^(w+1)
    let N := volume prime v
    let entry : Graph.Block common prime := Blocks.seqB LeafRoutines.offsets (Blocks.seqB Blocks.push LeafRoutines.view)
    let leave : Graph.Block common prime := Blocks.seqB Blocks.restore LeafRoutines.advance
    let record := (Fin.natAddEmb common (m := 24)).trans ((Fin.castAddEmb 31).trans (Fin.castAddEmb work))
    let bank := (Fin.castLEEmb (by decide : 23 ≤ 24)).trans record
    let g := physicalLabel m (w+1) label
    let G := g*reduce M proj*g⁻¹
    let rep := fun count roles' (D : Stacks ((host+31)+work) prime) =>
      RepT (CommonBank.bank roles' (Routines.hdr v) f p node scalar (Family.leafC (w+1) arity d count) st)
        (fun k => D.L (((k.castAdd 24).castAdd 31).castAdd work))
        (fun k => D.R (((k.castAdd 24).castAdd 31).castAdd work))
    let clean := fun (D : Stacks ((host+31)+work) prime) => ∀ (k : Fin work) x,
      readAt blank (D.L (k.natAdd (host+31))) (D.R (k.natAdd (host+31))) x = blank
    let logical := {v with width := d}
    let addr := fun a row pre mid post (x : IntegerMultBounds.Swap.Shear.State (Fin d) (ZMod M)) =>
      index M logical a row pre (FlatCoordinateLayout.rank x.1).val mid (FlatCoordinateLayout.rank x.2).val post
    let inner := Fin.natAddEmb 66 (m := (host+31)+work)
    let caller := Fin.castAddEmb (n := 66) ((host+31)+work)
    let K := 66+((host+31)+work)
    ∀ (ef : entry.tapes ≤ common+work) (xf : leave.tapes ≤ common+work)
      (eqs : entry.states ≤ Q) (xqs : leave.states ≤ Q) (word : Fin N → ZMod 2) (body : F → Pr F K Q prime U)
      (u : HS _ Q prime U) (whole : Stacks K prime) (tail : List (Fin (prime+4))),
      let slot := (((LeafCore.roleSlot io).castAdd 24).castAdd 31).castAdd work
      let r := recordRoundTripPorts slot
      let S := embStk inner whole
      whole.R (caller 2) = binSyms H M → whole.R (caller 28) = binSyms 1 1 →
      whole.R (caller 53) = binSyms J W →
      (∀ i : Fin 66, 58 ≤ i.val → whole.L (caller i) = [] ∧ whole.R (caller i) = []) →
      (∀ z, readAt blank (whole.L (r 0)) (whole.R (r 0)) (z-head) =
        RadixToBinary.binaryEncoding.encode (putWord source head ((List.ofFn word).map SparseRoleCircuit.encode) z)) →
      (∀ z, readAt blank (whole.L (r 1)) (whole.R (r 1)) z = blank) →
      rep d roles S → clean S →
      (∀ k : Fin 31, S.L ((k.natAdd host).castAdd work) = [] ∧ S.R ((k.natAdd host).castAdd work) = []) →
      fallbackBit rankFits (reduce M proj) g = false →
      S.R (record 16) = matrixWords prime H G ++ tail →
      whole.R (caller 44) = binSyms H (1 : ZMod M).val → (whole.R (caller 45)).length = w →
      whole.R (caller 55) = (List.ofFn fun i => binSyms H (parent i).val).flatten →
      (∀ i : Fin 24, i ≠ 16 → S.R (record i) = []) →
      let call := fun i : Fin d => packedCoordinateProgram (F := Empty) (U := U) io i.val i.val ef xf fits eqs xqs cap
      let cost := packedCoordinatesTime d N w (LeafCore.core io).tapes
        (packedLeafPush (F := Empty) (U := U) io Empty.elim) entry.tapes leave.tapes
      let budget := pivotSetupTime m d w M.size + cost
      let coordinate := (goodWeights prime d rankFits bank).seq (Prog.seqList ((List.finRange d).reverse.map call))
      let effect := fun ys : List (ZMod 2) =>
        ∃ minor : ∀ k (hk : k < d), IsUnit (GoodForm.lead (k+1) (lt_of_lt_of_le hk rankFits) G).det,
        let stage := GoodForm.stageAt G d rankFits minor d le_rfl
        let pivot := fun i : Fin d => stage.M (i.castLE rankFits) (i.castLE rankFits)
        let weight := fun i : Fin d => parent (i.castLE rankFits)*pivot i
        let inv := fun i : Fin d => parentInv (i.castLE rankFits)*Ring.inverse (pivot i)
        ∃ next : Fin N → ZMod 2, ys = List.ofFn next ∧
          ∀ a < v.beforeRows, ∀ row < v.rows, ∀ pre < v.beforeH, ∀ mid < v.between, ∀ post < v.afterD, ∀ x,
            ext next (addr a row pre mid post (Weighted.child d weight inv x)) = ext word (addr a row pre mid post x)
      let reverse := (Equiv.swap (0 : Fin 8) 1).toEmbedding.trans r
      let transfer := fun ports : Fin 8 ↪ Fin K => (stateLiftNormalize capacity (by decide)).seq
        (stateLiftPr capacity (by decide) Empty.elim (returnFromOrigin (P := Empty) ports))
      let marks := ([2,3,4,5,6,7] : List (Fin 8)).map r
      let loading := recordWeightLoadTime m w H M.size
      let conversion := recordMatrixLoadTime m H M.size
      ∃ z D t ys, z.user = u.user ∧ t ≤ (dimensionTime H 1 fields+(4*(fields*H+1)+6)+(10*J+12)+(6*(M^fields).size+6)) +
        (loading+(conversion+(budget+2*((218*N+1)*13+6)+3))) ∧
        Exec body ((recordCounterSetup caller fields).seq ((recordInputProgram record m).seq ((recordMatrixProgram record m).seq ((.act (pushMarkers marks) : Pr F K Q prime U).seq
          ((transfer r).seq ((embProg inner Empty.elim coordinate).seq (transfer reverse))))))) (mk u whole) t (mk z D) ∧
        effect ys ∧ (∀ k, readAt blank (D.L (r 0)) (D.R (r 0)) (k-head) =
          RadixToBinary.binaryEncoding.encode (putWord source head (ys.map SparseRoleCircuit.encode) k)) ∧
        ∀ j : Fin 58, j ≠ 24 → let port := caller (j.castAdd 8)
          D.L port = whole.L port ∧ D.R port = whole.R port := by
  intro d common host M N entry leave record bank g G rep clean logical addr inner caller K ef xf eqs xqs word
    body u whole tail slot r S base unit trailing spare input blank initial free empty good matrix
    one ticks archive scratch call cost budget coordinate effect reverse transfer marks loading conversion
  let packed := (List.ofFn fun i => binSyms (A := prime) M.size (parent i).val).flatten
  obtain ⟨a,A,c,ha,hc,setup,left,controls,off⟩ := recordCounterSetup_exec body caller fields H J M W
    hm hw u whole base unit trailing spare
  have disjoint (i : Fin 66) (j) : caller i ≠ inner j := by
    intro eq
    have h := congrArg Fin.val eq
    change i.val = 66+j.val at h
    omega
  have kept (i) := off (inner i) (disjoint 59 i) (disjoint 61 i) (disjoint 63 i)
  have raw (i : Fin 6) := controls i
  have port (i : Fin 6) : r (Fin.natAdd 2 i) = caller ((i.natAdd 58).castAdd 2) := by
    rw [recordRoundTripPorts_other slot _ ((by decide : ∀ j : Fin 6, Fin.natAdd 2 j ≠ (1 : Fin 8)) i)]
    exact congrArg caller ((by decide : ∀ j : Fin 6,
      (![24,0,58,59,60,61,62,63] (Fin.natAdd 2 j) : Fin 66) = (j.natAdd 58).castAdd 2) i)
  have first : r 0 = caller 24 := recordRoundTripPorts_other slot 0 (by decide)
  have shared : inner slot = r 1 := (recordRoundTripPorts_shared slot).symm
  have volumeEq : N = M^fields*(M^fields*W) := length
  have pos : 0 < M^fields := pow_pos (pow_pos Networks.Shared50ModularControl.prime_prime.pos _) _
  have callerKept (j : Fin 58) : A.R (caller (j.castAdd 8)) = whole.R (caller (j.castAdd 8)) := by
    apply off
    all_goals apply caller.injective.ne; intro eq; have h := congrArg Fin.val eq; simp at h; omega
  have inputEmpty (i : Fin 24) (hi : i ∈ [0,1,2,3,4,18,20,22,23]) :
      A.R (inner (record i)) = [] := by
    rw [kept]
    have ne := (by decide : ∀ i ∈ ([0,1,2,3,4,18,20,22,23] : List (Fin 24)), i ≠ 15 ∧ i ≠ 16) i hi
    exact scratch i ne.2
  obtain ⟨b,hb,load⟩ := recordInputProgram_exec body record H hm parent a A
    ((callerKept 2).trans base) ((callerKept 44).trans one) ((callerKept 55).trans archive) inputEmpty
  let reg := record.trans inner
  let P : Stacks K prime := {A with R := Function.update (Function.update (Function.update (Function.update A.R
    (reg 2) (binSyms M.size M)) (reg 23) packed) (reg 20) (binSyms M.size (1 : ZMod M).val)) (reg 22) (A.R (caller 45))}
  have preg (i : Fin 24) (h : i ≠ 2 ∧ i ≠ 20 ∧ i ≠ 22 ∧ i ≠ 23) :
      P.R (reg i) = S.R (record i) := by
    calc
      _ = A.R (reg i) := by simp [P,reg.injective.eq_iff,h.1,h.2.1,h.2.2.1,h.2.2.2]
      _ = _ := kept (record i)
  have pcaller (j : Fin 66) : P.R (caller j) = A.R (caller j) := by
    have h (i) : caller j ≠ reg i := disjoint j (record i)
    simp [P,h]
  obtain ⟨c',hmat,convert⟩ := recordMatrixProgram_exec body record H hm G tail b P
    ((pcaller 2).trans ((callerKept 2).trans base)) (by change P.R (reg 2) = _; simp [P,reg.injective.eq_iff,M])
    ((preg 16 (by decide)).trans matrix)
    (by intro i hi
        have h := (by decide : ∀ i ∈ ([0,1,3,4,15] : List (Fin 24)),
          (i ≠ 2 ∧ i ≠ 20 ∧ i ≠ 22 ∧ i ≠ 23) ∧ i ≠ 16) i hi
        exact (preg i h.1).trans (scratch i h.2))
  let B : Stacks K prime := {P with R := Function.update (Function.update P.R (reg 16) tail) (reg 15) (matrixWords prime M.size G)}
  have unchanged (j) (h : ∀ i, reg i ≠ j) : B.R j = A.R j := by
    simp [B,P,(h 2).symm,(h 20).symm,(h 22).symm,(h 23).symm,(h 15).symm,(h 16).symm]
  have outerRight (j) := unchanged (caller j) (fun i => (disjoint j (record i)).symm)
  have away (j) (h : ∀ i, record i ≠ j) := (unchanged (inner j) (fun i => inner.injective.ne (h i))).trans (kept j)
  have before (j) (h : j.val < common ∨ host ≤ j.val) : ∀ i, record i ≠ j := by
    intro i eq
    have hit := congrArg Fin.val eq
    change common+i.val = j.val at hit
    dsimp only [host] at h
    omega
  have slotRight := away slot (before slot (Or.inl (LeafCore.roleSlot io).isLt))
  let start := embStk inner B
  have initB : rep d roles start := by
    intro k x
    change _ = readAt _ (A.L _) (B.R (inner (((k.castAdd 24).castAdd 31).castAdd work))) _
    rw [left,away _ (before _ (Or.inl k.isLt))]
    exact initial k x
  have freeB : clean start := by
    intro k x
    change readAt _ (A.L _) (B.R (inner (k.natAdd (host+31)))) _ = _
    rw [left,away _ (before _ (Or.inr (by simp; omega)))]
    exact free k x
  have spareB (k : Fin 31) := away ((k.natAdd host).castAdd work) (before _ (Or.inr (by simp)))
  have transferRun := stagedLeafRoundTrip_exec pos pos hW capacity body r (embProg inner Empty.elim coordinate)
    c' B source head (List.ofFn word) (List.length_ofFn.trans length) effect budget (fun j => ∀ i, inner i ≠ j)
    (by rw [first,outerRight]; rw [show B.L = whole.L from left,off _ (caller.injective.ne (by decide)) (caller.injective.ne (by decide))
          (caller.injective.ne (by decide))]; simpa only [first] using input)
    (by rw [← shared,show B.L = whole.L from left,slotRight]; simpa only [← shared] using blank)
    (by intro i; rw [port]; exact ⟨(raw i).1,(outerRight _).trans (raw i).2⟩)
  suffices process : _ by
    obtain ⟨z,D,t,ys,hz,ht,run,act,read,frame⟩ := transferRun process
    have loadCost : ((6*(A.R (caller 55)).length+6)+((10*H+12)+(m*(10*M.size+8*(H-M.size)+12)+1+(2*packed.length+2))))+((10*M.size+10)+(6*(A.R (caller 45)).length+6)) ≤ loading := by
      dsimp only [loading,recordWeightLoadTime]
      rw [show A.R (caller 55) = whole.R (caller 55) from callerKept 55,
        show A.R (caller 45) = whole.R (caller 45) from callerKept 45,archive,ticks]
      simp [packed,List.length_flatten,List.map_ofFn,Function.comp_def,length_binSyms,List.ofFn_const]
    refine ⟨z,D,_,ys,hz.trans (hmat.trans (hb.trans ha)),?_,Exec.seq setup (Exec.seq load (Exec.seq convert run)),act,read,?_⟩
    · have length_matrixWords (b : ℕ) : (matrixWords prime b G).length = m*m*b := by
        simp [matrixWords,List.length_flatten,List.map_ofFn,Function.comp_def,length_binSyms,List.ofFn_const,Nat.mul_assoc]
      apply Nat.add_le_add hc (Nat.add_le_add loadCost _)
      simpa only [conversion,recordMatrixLoadTime,length_matrixWords,← volumeEq] using Nat.add_le_add_left ht ((m*m)*(10*M.size+8*(H-M.size)+12)+1+(2*(matrixWords prime M.size G).length+2))
    intro j ne
    have outside (i : Fin 8) : r i ≠ caller (j.castAdd 8) := by
      by_cases h : i = 1
      · subst i; rw [← shared]; exact (disjoint _ _).symm
      · rw [recordRoundTripPorts_other slot i h]
        apply caller.injective.ne
        exact (by decide : ∀ (i : Fin 8) (j : Fin 58), i ≠ 1 → j ≠ 24 →
          (![24,0,58,59,60,61,62,63] i : Fin 66) ≠ j.castAdd 8) i j h ne
    have preserved := frame _ (fun i => (disjoint _ i).symm) outside
    have unused (i : Fin 66) (hi : 58 ≤ i.val) : caller i ≠ caller (j.castAdd 8) := by
      apply caller.injective.ne
      intro eq
      have h := congrArg Fin.val eq
      change i.val = j.val at h
      omega
    exact ⟨preserved.1.trans (congrFun left _),preserved.2.trans ((outerRight _).trans (off _ (unused _ (by decide))
      (unused _ (by decide)) (unused _ (by decide))))⟩
  apply stagedCoordinateChild_exec body inner r slot shared (recordRoundTripPorts_apart slot) coordinate B
    (List.ofFn word) effect budget
  intro y E read frame
  obtain ⟨z,D,t,user,time,exec,minor,next,_,_,_,out,_,action⟩ := stagedGoodRecordCoordinates_exec
    v positive w proj width idem factor hd label live rankFits parent parentInv reciprocal io roles f p node scalar
    arity st freeNode fits cap ef xf eqs xqs word Empty.elim y start E [] [] initB frame read freeB
    (fun k => ⟨(congrFun left _).trans (empty k).1,(spareB k).trans (empty k).2⟩) good
    (by change B.R (reg 15) = _; simp [B,G,g,M])
    (by change B.R (reg 2) = _; simp [B,P,reg.injective.eq_iff,M])
    (by change B.R (reg 20) = _; simp [B,P,reg.injective.eq_iff,M])
    (by change (B.R (reg 22)).length = _; simp [B,P,reg.injective.eq_iff]; exact (congrArg List.length (callerKept 45)).trans ticks)
    (by intro i hi
        let room : 23 ≤ 24 := Nat.le_succ 23
        let j := i.castLE room
        have h := (by dsimp only [room]; decide : ∀ i : Fin 23, (i < 15 ∧ i ≠ 2) ∨ (17 ≤ i ∧ i ≤ 19) ∨ i = 21 →
          let j := i.castLE room
          (j ≠ 2 ∧ j ≠ 20 ∧ j ≠ 22 ∧ j ≠ 23) ∧ j ≠ 15 ∧ j ≠ 16) i hi
        change B.R (reg j) = _
        have ne15 : j ≠ 15 := h.2.1
        have ne16 : j ≠ 16 := h.2.2
        rw [show B.R (reg j) = P.R (reg j) by simp [B,reg.injective.eq_iff,ne15,ne16]]
        exact (preg j h.1).trans (scratch j h.2.2))
    (by change B.R (reg 23) = _; simp [B,P,reg.injective.eq_iff,packed,M])
  exact ⟨z,D,t,List.ofFn next,user,time,exec,by simp [N],⟨minor,next,rfl,action⟩,out⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
