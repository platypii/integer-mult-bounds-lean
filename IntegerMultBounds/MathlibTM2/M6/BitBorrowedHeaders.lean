module

public import IntegerMultBounds.MathlibTM2.M6.BitHelperParentSeeds

/-! Prepare adjacent digit exchanges with the borrowed label inside the trailing record. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Shared50ModularControl (prime)
open FlatCoordinateSchedule (bits)

def borrowedArchiveBank (i : Fin 127) : Fin 12 ↪ Fin 268 where
  toFun k := ⟨if k.val = 3 then 14+2*i.val else if k.val = 4 then 15+2*i.val
    else if k.val = 2 then 13 else k.val,by split_ifs <;> omega⟩
  inj' := by intro k l eq; apply Fin.ext; have h := congrArg Fin.val eq; dsimp at h; split_ifs at h <;> omega

/-- Register 13 already contains the product of the label count and the
trailing length. Use it as the suffix for every swap and register 1 as the gap. -/
theorem borrowedArchive_exec {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (bank : Fin 268 ↪ Fin T) (w L W : ℕ) (u : HS T Q prime U) (S : Stacks T prime)
    (seed : ∀ k, S.R (bank k) = helperArchiveSeed w L W k) :
    let ports := fun i => (borrowedArchiveBank i).trans bank
    let headers := fun i => helperHeaderPorts i (bank 1) (bank 3) (bank 1) (ports i 3) (ports i 4)
    ∃ z F t, z.user = u.user ∧ Exec body (helperHeaderSweep ports (List.finRange 127)) (mk u S) t (mk z F) ∧
      t ≤ ((List.finRange 127).map (helperHeaderTime w 1 (L*W))).sum+1 ∧ F.L = S.L ∧
      (∀ i j, F.R (headers i j) = (Routines.hdr (helperAdjacentView w 1 (L*W) i) j).map bitSymbol) ∧
      ∀ p, (∀ k, bank k ≠ p) → F.R p = S.R p := by
  intro ports headers
  have apart (i j : Fin 127) (hne : i ≠ j) (k : Fin 12) :
      ports j k ≠ ports i 3 ∧ ports j k ≠ ports i 4 := by
    have ne : i.val ≠ j.val := fun h => hne (Fin.ext h)
    constructor <;> intro eq <;> have h := congrArg Fin.val (bank.injective eq)
    all_goals simp only [borrowedArchiveBank,Function.Embedding.coeFn_mk] at h; split_ifs at h <;> omega
  obtain ⟨z,F,t,user,run,time,left,filled,off⟩ := helperHeaderSweep_exec body ports apart
    w 1 (L*W) (List.finRange 127) (List.nodup_finRange _) u S (by
      intro i _
      simp only [ports,Function.Embedding.trans_apply,seed,ite_self,one_mul]
      refine ⟨rfl,rfl,rfl,?_⟩
      intro k hk
      simp only [borrowedArchiveBank,Function.Embedding.coeFn_mk,helperArchiveSeed]
      split_ifs <;> first | rfl | omega)
  have retained (k : Fin 268) (low : k.val < 14) : F.R (bank k) = helperArchiveSeed w L W k := by
    rw [← seed]
    apply off
    intro i _
    constructor <;> intro eq <;> have h := congrArg Fin.val (bank.injective eq)
    all_goals simp [borrowedArchiveBank] at h; omega
  refine ⟨z,F,t,user,run,time,left,?_,fun p hp => off p (fun i _ => ⟨(hp _).symm,(hp _).symm⟩)⟩
  intro i j
  have unit : F.R (bank 1) = (bits 1).map bitSymbol := by rw [retained 1 (by decide),canonicalBits_symbols]; rfl
  have width : F.R (bank 3) = (bits w).map bitSymbol := by rw [retained 3 (by decide)]; rfl
  obtain ⟨pre,post⟩ := filled i (List.mem_finRange i)
  fin_cases j <;> first | exact unit | exact width | exact pre | exact post | skip
  simpa [headers,helperHeaderPorts,helperAdjacentView,Routines.hdr,RecursiveDimensionBank.values] using unit

def borrowedHeaders (T : ℕ) (i : Fin 127) : Fin 6 → Fin (T+273) :=
  let bank := parentArchive T
  helperHeaderPorts i (bank 1) (bank 3) (bank 1) (bank (borrowedArchiveBank i 3)) (bank (borrowedArchiveBank i 4))

/-- Adjacent exchanges at positions 1 and 14 already store the modulus
and the 112-digit spectator suffix needed by every recursive worker. -/
theorem loadWorkerDimensions_exec {T Q : ℕ} {P U : Type}
    (body : P → Pr P T Q prime U) (bank : Fin 35 ↪ Fin T) (headers : Fin 127 → Fin 6 → Fin T)
    (apart : ∀ i j k, headers i j ≠ bank k) (w W : ℕ)
    (u : HS T Q prime U) (S : Stacks T prime) :
    let src : Fin 3 → Fin T := ![headers 1 2,headers 14 5,headers 0 0]
    let dst : Fin 3 ↪ Fin 35 := ⟨![2,27,28],by decide⟩
    let M := prime^(w+1)
    let suffix := M^112*W
    (∀ i j, S.R (headers i j) =
      (Routines.hdr (helperAdjacentView (w+1) 1 W i) j).map bitSymbol) →
    (∀ j ∈ ([0,1,2,27,28] : List (Fin 35)), S.R (bank j) = []) →
    ∃ z F t, z.user = u.user ∧
      Exec body (Record.copyLeafHeaders src (dst.trans bank)
        (bank 0) (bank 1) (List.finRange 3)) (mk u S) t (mk z F) ∧
      t = 6*(M.size+suffix.size)+25 ∧ F.L = S.L ∧
      (∀ j, (∀ i, bank i ≠ j) → F.R j = S.R j) ∧
      F.R (bank 2) = binSyms M.size M ∧ F.R (bank 27) = binSyms suffix.size suffix ∧
      F.R (bank 28) = binSyms 1 1 ∧
      ∀ j, (∀ i, dst i ≠ j) → F.R (bank j) = S.R (bank j) := by
  intro src dst M suffix ready free
  have separate (i : Fin 3) (k) : src i ≠ bank k := by
    fin_cases i <;> exact apart _ _ _
  have ports (i : Fin 3) : [src i,bank (dst i),bank 0,bank 1].Nodup :=
    List.nodup_cons.mpr ⟨by simp [separate],((by decide : ∀ i, [dst i,0,1].Nodup) i).map bank.injective⟩
  obtain ⟨z,F,user,run,left,loaded,off⟩ := Record.copyLeafHeaders_exec body
    src (dst.trans bank) (bank 0) (bank 1) (fun i j => separate i (dst j)) ports
    (List.finRange 3) (List.nodup_finRange _) u S (free 0 (by decide)) (free 1 (by decide))
    (fun i _ => free (dst i) ((by decide : ∀ i, dst i ∈ ([0,1,2,27,28] : List (Fin 35))) i))
  have base : S.R (src 0) = binSyms M.size M := by
    rw [show src 0 = headers 1 2 from rfl,ready]
    simpa [Routines.hdr,RecursiveDimensionBank.values,helperAdjacentView,M] using canonicalBits_symbols (A := prime) M
  have width : S.R (src 1) = binSyms suffix.size suffix := by
    rw [show src 1 = headers 14 5 from rfl,ready]
    simpa [Routines.hdr,RecursiveDimensionBank.values,helperAdjacentView,suffix,M] using canonicalBits_symbols (A := prime) suffix
  have unit : S.R (src 2) = binSyms 1 1 := by
    rw [show src 2 = headers 0 0 from rfl,ready]
    exact canonicalBits_symbols 1
  refine ⟨z,F,_,user,run,?_,left,fun j outside => off _ (fun i _ => outside (dst i)),
    (loaded 0 (List.mem_finRange _)).trans base,(loaded 1 (List.mem_finRange _)).trans width,
    (loaded 2 (List.mem_finRange _)).trans unit,fun j h => off _ (fun i _ => bank.injective.ne (h i))⟩
  change (6*(S.R (src 0)).length+6)+((6*(S.R (src 1)).length+6)+
    ((6*(S.R (src 2)).length+6)+0))+1 = _
  rw [base,width,unit]
  simp only [length_binSyms]
  omega

/-- Initialize the five dimension and control registers of a recursive
worker directly from the shared archive, preserving its payload and every other register. -/
theorem prepareWorkerControls_exec {T Q : ℕ} {P U : Type}
    (body : P → Pr P T Q prime U) (bank : Fin 35 ↪ Fin T) (headers : Fin 127 → Fin 6 → Fin T)
    (apart : ∀ i j k, headers i j ≠ bank k) :
    ∃ code, ∀ w W : ℕ, let M := prime^(w+1)
    let suffix := M^112*W
    ∀ (u : HS T Q prime U) (S : Stacks T prime),
    (∀ i j, S.R (headers i j) =
      (Routines.hdr (helperAdjacentView (w+1) 1 W i) j).map bitSymbol) →
    (∀ j ∈ ([0,1,2,3,27,28,32,33] : List (Fin 35)), S.R (bank j) = []) →
    ∃ z F t, z.user = u.user ∧ Exec body code (mk u S) t (mk z F) ∧
      t ≤ 14*M.size+6*suffix.size+6*(w+1)+11*(w+1).size+50 ∧ F.L = S.L ∧
      (∀ j, (∀ i, bank i ≠ j) → F.R j = S.R j) ∧
      F.R (bank 2) = binSyms M.size M ∧ F.R (bank 27) = binSyms suffix.size suffix ∧
      F.R (bank 28) = binSyms 1 1 ∧ F.R (bank 32) = binSyms M.size 1 ∧
      F.R (bank 33) = List.replicate w Node.tick ∧
      ∀ i : Fin 35, i ∉ [2,27,28,32,33] → F.R (bank i) = S.R (bank i) := by
  let width := headers 0 3
  let src : Fin 3 → Fin T := ![headers 1 2,headers 14 5,headers 0 0]
  let dst : Fin 3 ↪ Fin 35 := ⟨![2,27,28],by decide⟩
  refine ⟨.seq (Record.copyLeafHeaders src (dst.trans bank) (bank 0) (bank 1)
    (List.finRange 3)) (.seq (toBinary (bank 28) (bank 2) (bank 32) (bank 0) (bank 1) (bank 3))
    (.seq (toUnary width (bank 33) (bank 0) (bank 1) (bank 3)) (.act (.pop (.rt (bank 33)) (fun v _ => v) .done)))),?_⟩
  intro w W M suffix u S ready free
  obtain ⟨v,D,m,user,load,price,left,keep,base,tail,one,off⟩ := loadWorkerDimensions_exec body bank headers apart w W u S ready
    (fun j hj => free j ((by decide : ∀ j : Fin 35, j ∈ [0,1,2,27,28] → j ∈ [0,1,2,3,27,28,32,33]) j hj))
  have bits : D.R width = binSyms (w+1).size (w+1) := by
    rw [keep width (fun k => (apart 0 3 k).symm),ready]
    exact canonicalBits_symbols _
  obtain ⟨z,n,same,bill,controls⟩ := copyRecordControls_exec body bank width (apart 0 3) w v D base one bits
    (fun i hi => (off i (by
      have disj : ∀ k : Fin 35, k ∈ [0,1,3,32,33] → ∀ j, dst j ≠ k := by decide
      exact disj i hi)).trans (free i ((by decide : ∀ i : Fin 35, i ∈ [0,1,3,32,33] → i ∈ [0,1,2,3,27,28,32,33]) i hi)))
  refine ⟨z,_,m+n,same.trans user,Exec.seq load controls,by dsimp only [suffix,M]; omega,left,?_,?_,?_,?_,?_,?_,?_⟩
  · intro j outside
    simpa [Function.update_of_ne (outside 32).symm,Function.update_of_ne (outside 33).symm] using keep j outside
  · simpa [bank.injective.eq_iff] using base
  · simpa [bank.injective.eq_iff] using tail
  · simpa [bank.injective.eq_iff] using one
  · simp [bank.injective.eq_iff,M]
  · simp
  · intro i hi
    simp only [List.mem_cons,not_or] at hi
    change Function.update (Function.update D.R (bank 32) (binSyms M.size 1)) (bank 33) (List.replicate w Node.tick) (bank i) = S.R (bank i)
    rw [Function.update_of_ne (bank.injective.ne hi.2.2.2.2.1),Function.update_of_ne (bank.injective.ne hi.2.2.2.1)]
    apply off
    intro j
    fin_cases j <;> first | exact Ne.symm hi.1 | exact Ne.symm hi.2.1 | exact Ne.symm hi.2.2.1

/-- The archive initializer supplies exactly the sixteen-digit record contract
of scheduled MOVE and COPY. Both the live payload and saved record survive. -/
theorem prepareWorkerRecord_exec {T Q : ℕ} {P U : Type}
    (body : P → Pr P T Q prime U) (bank : Fin 35 ↪ Fin T) (headers : Fin 127 → Fin 6 → Fin T)
    (apart : ∀ i j k, headers i j ≠ bank k) :
    ∃ code, ∀ w W : ℕ, let M := prime^(w+1)
    let suffix := M^112*W
    ∀ (x : Fin (M^16*suffix) → ZMod 2) (u : HS T Q prime U) (S : Stacks T prime),
    (∀ i j, S.R (headers i j) =
      (Routines.hdr (helperAdjacentView (w+1) 1 W i) j).map bitSymbol) →
    (∀ i : Fin 35, i ≠ 24 → i ≠ 34 → S.L (bank i) = [] ∧ S.R (bank i) = []) →
    (∀ z, readAt blank (S.L (bank 24)) (S.R (bank 24)) z = RadixToBinary.binaryEncoding.encode
      (putWord (fun _ => blank) 0 (List.ofFn (SparseRoleCircuit.encode ∘ x)) z)) →
    ∃ z F t, z.user = u.user ∧ Exec body code (mk u S) t (mk z F) ∧
      t ≤ 14*M.size+6*suffix.size+6*(w+1)+11*(w+1).size+50 ∧
      RecordReady (b := prime) (w := w) (d := 16) (W := suffix) bank M.size suffix.size (S.R (bank 34))
        SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0 x F ∧
      F.L = S.L ∧ ∀ j, (∀ i, bank i ≠ j) → F.R j = S.R j := by
  obtain ⟨code,run⟩ := prepareWorkerControls_exec body bank headers apart
  refine ⟨code,?_⟩
  intro w W M suffix x u S ready empty payload
  obtain ⟨z,F,t,user,exec,bill,left,keep,base,tail,one,padded,clock,off⟩ := run w W u S ready
    (fun i hi => by
      have h := (by decide : ∀ i : Fin 35, i ∈ [0,1,2,3,27,28,32,33] → i ≠ 24 ∧ i ≠ 34) i hi
      exact (empty i h.1 h.2).2)
  have modulus : (1 : ZMod M).val = 1 := ZMod.val_one'' (Nat.ne_of_gt
    (Shared50ModularControl.prime_prime.one_lt.trans_le (Nat.le_self_pow (by omega : w+1 ≠ 0) prime)))
  refine ⟨z,F,t,user,exec,bill,⟨base,tail,one,?_,?_,off 34 (by decide),?_,?_,?_⟩,left,keep⟩
  · simpa only [modulus] using padded
  · rw [clock,List.length_replicate]
  · intro i hi
    have h := (by decide : ∀ i ∈ shearWork, i ∉ ([2,27,28,32,33] : List (Fin 35)) ∧ i ≠ 24 ∧ i ≠ 34) i hi
    rw [left,off i h.1]
    exact empty i h.2.1 h.2.2
  · have h : F.R (bank 24) = S.R (bank 24) := off 24 (by decide)
    simpa only [left,h,sub_zero] using payload
  · intro j
    have h : F.R (bank 25) = [] := (off 25 (by decide)).trans (empty 25 (by decide) (by decide)).2
    simp [left,h,empty 25 (by decide) (by decide),readAt]
    rfl

/-- The setup bank shares the archive suffix with the stage. Its own source
registers precede the stage, whose worker tapes and leaf scratch are disjoint. -/
def archiveSetupPlacement (R T L : ℕ) : Fin (R+273) ↪ Fin (R+((T+273)+L)) :=
  (finSumFinEquiv.symm.toEmbedding.trans ((Function.Embedding.refl (Fin R)).sumMap
    ((Fin.natAddEmb T (m := 273)).trans (Fin.castAddEmb L)))).trans finSumFinEquiv.toEmbedding

theorem archiveSetupPlacement_header (R T L : ℕ) (i : Fin 127) (j : Fin 6) :
    archiveSetupPlacement R T L (borrowedHeaders R i j) =
      ((borrowedHeaders T i j).castAdd L).natAdd R := by
  have atArchive (a : Fin 268) : archiveSetupPlacement R T L (parentArchive R a) =
      ((parentArchive T a).castAdd L).natAdd R := by
    simp [archiveSetupPlacement,parentArchive,Function.Embedding.sumMap]
  fin_cases j <;> first | exact atArchive _ | simpa [borrowedHeaders,helperHeaderPorts] using atArchive 1

theorem archiveSetupPlacement_frame {R T L : ℕ} (i : Fin (R+273)) :
    (∀ k : Fin T, archiveSetupPlacement R T L i ≠ ((k.castAdd 273).castAdd L).natAdd R) ∧
    ∀ k : Fin L, archiveSetupPlacement R T L i ≠ (k.natAdd (T+273)).natAdd R := by
  induction i using Fin.addCases with
  | left i =>
    simp [archiveSetupPlacement,Function.Embedding.sumMap]
    constructor <;> intro k eq <;> have e := congrArg Fin.val eq <;> simp at e <;> omega
  | right j =>
    simp [archiveSetupPlacement,Function.Embedding.sumMap]
    constructor <;> intro k eq <;> have e := congrArg Fin.val eq <;> simp at e <;> omega

/-- Lift a completed archive setup onto the sweep host. The stage sees the
prepared words at its own header ports, with worker and scratch stacks preserved. -/
theorem archiveSetupPlacement_exec {R T L Q : ℕ} {P H U : Type} {ι : P → H}
    (body : P → Pr P (R+273) Q prime U)
    (host : H → Pr H (R+((T+273)+L)) Q prime U)
    (calls : ∀ f, host (ι f) = embProg (archiveSetupPlacement R T L) ι (body f))
    (code : Pr P (R+273) Q prime U) (u : HS _ Q prime U) (S : Stacks _ prime)
    (words : Fin 127 → Fin 6 → List (Fin (prime+4))) :
    let e := archiveSetupPlacement R T L
    ∀ v D t, Exec body code (mk (embDn e u) (embStk e S)) t (mk v D) →
    (∀ i j, D.R (borrowedHeaders R i j) = words i j) →
    ∃ z F, Exec host (embProg e ι code) (mk u S) t (mk z F) ∧ z.user = v.user ∧
      (∀ i j, F.R (((borrowedHeaders T i j).castAdd L).natAdd R) = words i j) ∧
      (∀ k : Fin T, let p := ((k.castAdd 273).castAdd L).natAdd R
        F.L p = S.L p ∧ F.R p = S.R p) ∧
      ∀ k : Fin L, let p := (k.natAdd (T+273)).natAdd R
        F.L p = S.L p ∧ F.R p = S.R p := by
  intro e v D t run ready
  obtain ⟨z,F,exec,_,user,view,off⟩ := exec_emb (ι := ι) e.injective calls run u rfl S rfl
  refine ⟨z,F,exec,user,?_,fun k => off _ (fun i => (archiveSetupPlacement_frame i).1 k),
    fun k => off _ (fun i => (archiveSetupPlacement_frame i).2 k)⟩
  intro i j
  rw [← archiveSetupPlacement_header]
  exact (congrArg (fun X : Stacks (R+273) prime => X.R (borrowedHeaders R i j)) view).trans (ready i j)

theorem borrowedHeaders_apart {T : ℕ} (i : Fin 127) (j : Fin 6) (k : Fin T) :
    borrowedHeaders T i j ≠ k.castAdd 273 := by
  have apart (a : Fin 268) : parentArchive T a ≠ k.castAdd 273 := by
    intro eq
    have h := congrArg Fin.val eq
    change T+a.val = k.val at h
    omega
  fin_cases j <;> simpa [borrowedHeaders,helperHeaderPorts] using apart _

theorem prepareBorrowedHeaders_exec {T Q : ℕ} {P U : Type} (body : P → Pr P (T+273) Q prime U) (hdr : Fin 6 → Fin T)
    (regs : Fin 35 ↪ Fin T) (v : RecursiveInterchangeLayout.Descriptor) (w : ℕ)
    (pos : v.Positive) (u : HS (T+273) Q prime U) (S : Stacks (T+273) prime) :
    let W := v.beforeRows*v.rows*v.between*v.afterD
    let M := prime^(w+1)
    let V := M^128*(v.beforeH*W)
    let read := fun (k : Fin T) => S.R (k.castAdd 273)
    read (regs 2) = binSyms M.size M → read (regs 28) = binSyms 1 1 →
    (read (regs 33)).length = w →
    (∀ i, read (hdr i) = (M8.RevMachine.Routines.hdr v i).map bitSymbol) →
    (∀ j : Fin 273, S.L (j.natAdd T) = [] ∧ S.R (j.natAdd T) = []) →
    ∃ z F t, z.user = u.user ∧ Exec body (.seq (prepareHelperSeeds hdr regs) (helperHeaderSweep (fun i => (borrowedArchiveBank i).trans (parentArchive T)) (List.finRange 127))) (mk u S) t (mk z F) ∧
      t ≤ 152402000*V ∧
      (∀ i j, F.R (borrowedHeaders T i j) =
        (M8.RevMachine.Routines.hdr (helperAdjacentView (w+1) 1 (v.beforeH*W) i) j).map bitSymbol) ∧
      F.L = S.L ∧ ∀ k : Fin T, F.R (k.castAdd 273) = read k := by
  intro W M V read base unit clock words free
  obtain ⟨y,D,m,same,seed,charge,filled,dl,dr⟩ := prepareHelperSeeds_linear body hdr regs v w pos u S base unit clock words free
  obtain ⟨z,F,n,user,sweep,price,fl,ready,off⟩ := borrowedArchive_exec body (parentArchive T) (w+1) v.beforeH W y D filled
  have wp : 0 < W := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos pos.1 pos.2.1) pos.2.2.2.1) pos.2.2.2.2
  have bounded := price.trans (helperArchiveTime_le (w+1) 1 (v.beforeH*W) Nat.zero_lt_one (Nat.mul_pos pos.2.2.1 wp))
  refine ⟨z,F,m+n,user.trans same,Exec.seq seed sweep,?_,ready,fl.trans dl,?_⟩
  · simp only [one_mul] at bounded
    change n ≤ (127*1200000+1)*V at bounded
    change m ≤ 1999*V at charge
    omega
  · intro k
    apply (off _ ?_).trans (dr k)
    intro j e
    have h := congrArg Fin.val e
    change T+j.val = k.val at h
    omega

/-- Divide the parent row header once for all nine stages. The divider
returns its private tapes empty and the other five headers unchanged. -/
theorem prepareRoleRows_hoare (node : RecursiveInterchangeLayout.Descriptor) (rows : ℕ)
    (split : node.rows = 142080*rows) (live : 0 < rows) :
    let role := { node with rows := rows }
    HoareTime (RecursiveRowsNodeHeaders.program (q := prime) 142080)
      (fun S => S = RecursiveChildQuotients.input (Routines.hdr node))
      (fun S => S = RecursiveChildQuotients.input (Routines.hdr role))
      ((RecursiveRowsQuotient.constant 142080+30)*node.rows) := by
  intro role
  let hs := Routines.hdr node
  obtain ⟨rs,canonical,value,len,run⟩ :=
    RecursiveRowsNodeHeaders.constructs_hoare (q := prime) 142080 (by decide) hs
  have words := Routines.hdr_headers node
  have rowValue : Counter.value (hs 1) = node.rows := words.1 1
  have reduced := RecursiveRowsNodeHeaders.headers_correct node hs rs 142080 words canonical
    (value.trans (congrArg (· /142080) rowValue))
  have desc : RecursiveInterchangeLayout.role node 142080 = role := by
    simp [RecursiveInterchangeLayout.role,role,split]
  rw [desc] at reduced
  rw [Routines.hdr_eq reduced] at run
  exact run.consequence (fun _ h => h) (fun _ h => h)
    (RecursiveRowsNodeHeaders.cost_linear _ _ _ _ (by omega) (words.2 1) rowValue.le len)

/-- Install the reduced row header on a placed divider bank. Owner tapes
and the registers used by the archive builder can lie outside that bank. -/
theorem prepareRoleRows_exec {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (slots : Fin 38 ↪ Fin T) :
    let machine := RecursiveRowsNodeHeaders.program (q := prime) 142080
    let positive := Nat.zero_lt_of_lt machine.start.isLt
    ∀ (capacity : _ ≤ Q) (node : RecursiveInterchangeLayout.Descriptor) (rows : ℕ),
    node.rows = 142080*rows → 0 < rows →
    ∀ (u : HS T Q prime U) (S : Stacks T prime),
    RepT (RecursiveChildQuotients.input (Routines.hdr node)) (embStk slots S).L (embStk slots S).R →
    ∃ z F t, z.user = u.user ∧ t ≤ 1+((RecursiveRowsQuotient.constant 142080+30)*node.rows*43+6) ∧
      Exec body (statePlacedNormalized slots capacity positive Empty.elim (foreign machine))
        (mk u S) t (mk z F) ∧
      RepT (RecursiveChildQuotients.input (Routines.hdr { node with rows := rows }))
        (embStk slots F).L (embStk slots F).R ∧
      ∀ j, (∀ i, slots i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro machine positive capacity node rows split live u S rep
  obtain ⟨v,D,_,rfl,next,user,_,_,_,m,time,run⟩ := foreign_exec (P := Empty) Empty.elim
    machine (prepareRoleRows_hoare node rows split live) (stateLiftDown positive (embDn slots u))
    (embStk slots S) _ rfl rep
  obtain ⟨z,_,same,placed⟩ := statePlaced_exec_normalized slots slots.injective capacity positive
    Empty.elim (body' := body) (fun e => nomatch e) u S run
  exact ⟨z,_,_,same.trans user,Nat.add_le_add_left time 1,placed,
    by rwa [embStk_ovr slots.injective],fun j off => embOvr_off _ _ off⟩

/-- The six physical header ports returned by the divider satisfy the
read condition of the descriptor copying routine, including its end markers. -/
theorem roleRows_reads {T : ℕ} (slots : Fin 38 ↪ Fin T)
    (hs : Fin 6 → List Bool) (S : Stacks T prime)
    (rep : RepT (RecursiveChildQuotients.input hs) (embStk slots S).L (embStk slots S).R)
    (i : Fin 6) :
    let src := slots (⟨3+i.val,by omega⟩ : Fin 38)
    ∀ z, readAt blank (S.L src) (S.R src) (z-1) = RadixZeroFill.encodedBinary (hs i) z := by
  intro src z
  have h := (rep (⟨3+i.val,by omega⟩ : Fin 38) z).symm
  fin_cases i <;> exact h.trans (congrFun (BinaryDescriptorStackRoundtrip.descriptor_encoded _) z)

/-- Divide the row count and materialize the six canonical role words in
the source registers of the header archive. -/
theorem loadRoleHeaders_exec {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (slots : Fin 38 ↪ Fin T) (dst : Fin 6 ↪ Fin T) (tmp : Fin T)
    (apart : ∀ i j, slots i ≠ dst j) (scratch : ∀ i, slots i ≠ tmp)
    (fresh : ∀ j, tmp ≠ dst j) :
    let machine := RecursiveRowsNodeHeaders.program (q := prime) 142080
    let positive := Nat.zero_lt_of_lt machine.start.isLt
    let src := fun i : Fin 6 => slots (⟨3+i.val,by omega⟩ : Fin 38)
    ∀ (capacity : _ ≤ Q) (node : RecursiveInterchangeLayout.Descriptor) (rows : ℕ),
    node.rows = 142080*rows → 0 < rows →
    let hs := Routines.hdr { node with rows := rows }
    ∀ (u : HS T Q prime U) (S : Stacks T prime),
    RepT (RecursiveChildQuotients.input (Routines.hdr node)) (embStk slots S).L (embStk slots S).R →
    S.L tmp = [] → S.R tmp = [] → (∀ i, S.R (dst i) = []) →
    ∃ z F t, z.user = u.user ∧
      Exec body (.seq (statePlacedNormalized slots capacity positive Empty.elim (foreign machine))
        (loadDimensions src dst tmp (List.finRange 6))) (mk u S) t (mk z F) ∧
      t ≤ (RecursiveRowsQuotient.constant 142080+30)*node.rows*43+
        ((List.finRange 6).map (fun i => 8*(hs i).length+8)).sum+8 ∧
      (∀ i, F.R (dst i) = (hs i).map bitSymbol) ∧
      ∀ j, (∀ i, slots i ≠ j) → (∀ i, dst i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro machine positive src capacity node rows split live hs u S rep left right empty
  obtain ⟨v,D,m,user,price,divide,words,off⟩ :=
    prepareRoleRows_exec body slots capacity node rows split live u S rep
  have ports (i : Fin 6) : [src i,tmp,dst i].Nodup := by
    simp [src,scratch,apart,fresh]
  obtain ⟨z,F,same,load,keep,filled,frame⟩ := loadDimensions_exec body src dst tmp hs
    (fun i j => apart _ _) ports _ (List.nodup_finRange 6) v D (roleRows_reads slots hs D words)
    ⟨(off tmp scratch).1.trans left,(off tmp scratch).2.trans right⟩
    (fun i _ => (off _ (fun k => apart k i)).2.trans (empty i))
  refine ⟨z,F,_,same.trans user,Exec.seq divide load,by omega,fun i => filled i (List.mem_finRange i),?_⟩
  intro j outside untouched
  exact ⟨(congrFun keep j).trans (off j outside).1,
    (frame j (fun i _ => untouched i)).trans (off j outside).2⟩

/-- With the row register reduced to one role's row count, the archive
contains precisely the trailing dimensions used by the scheduled packer. -/
theorem prepareRoleHeaders_exec {T Q : ℕ} {P U : Type}
    (body : P → Pr P (T+273) Q prime U) (hdr : Fin 6 → Fin T) (regs : Fin 35 ↪ Fin T)
    (node : RecursiveInterchangeLayout.Descriptor) (w B rows : ℕ)
    (label : node.beforeH = B*prime^(64*((w+1)*64))) :
    let role := { node with rows := rows }
    let K := node.beforeRows*rows*node.between*node.afterD
    let W := B*prime^(64*((w+1)*64))*K
    let M := prime^(w+1)
    ∀ (_ : role.Positive) (u : HS (T+273) Q prime U) (S : Stacks (T+273) prime),
    let read := fun (k : Fin T) => S.R (k.castAdd 273)
    read (regs 2) = binSyms M.size M → read (regs 28) = binSyms 1 1 →
    (read (regs 33)).length = w →
    (∀ i, read (hdr i) = (M8.RevMachine.Routines.hdr role i).map bitSymbol) →
    (∀ j : Fin 273, S.L (j.natAdd T) = [] ∧ S.R (j.natAdd T) = []) →
    ∃ z F t, z.user = u.user ∧
      Exec body (.seq (prepareHelperSeeds hdr regs) (helperHeaderSweep
        (fun i => (borrowedArchiveBank i).trans (parentArchive T)) (List.finRange 127)))
        (mk u S) t (mk z F) ∧
      t ≤ 152402000*(M^16*((M^112*B)*prime^(64*((w+1)*64))*K)) ∧
      (∀ i j, F.R (borrowedHeaders T i j) =
        (M8.RevMachine.Routines.hdr (helperAdjacentView (w+1) 1 W i) j).map bitSymbol) ∧
      F.L = S.L ∧ ∀ k : Fin T, F.R (k.castAdd 273) = read k := by
  intro role K W M pos u S read base unit clock words free
  obtain ⟨z,F,t,user,run,price,ready,left,keep⟩ :=
    prepareBorrowedHeaders_exec body hdr regs role w pos u S base unit clock words free
  have suffix : role.beforeH*K = W := congrArg (· * K) label
  refine ⟨z,F,t,user,run,?_,?_,left,keep⟩
  · change t ≤ 152402000*(M^128*(role.beforeH*K)) at price
    rw [suffix] at price
    convert price using 1
    dsimp [W]
    ring
  · simpa only [← suffix] using ready

private theorem archiveCost_le (C rows V copies m n : ℕ) (live : 0 < V)
    (rowBound : rows ≤ V) (headerBound : copies ≤ 6*(24*V))
    (load : m ≤ C*(142080*rows)*43+copies+8) (build : n ≤ 152402000*V) :
    m+n ≤ (C*142080*43+152402152)*V := by
  have divCost := Nat.mul_le_mul_left (C*142080*43) rowBound
  rw [show C*(142080*rows)*43 = C*142080*43*rows by ring] at load
  rw [Nat.add_mul]
  omega

/-- Prepare the entire exchange archive on the host from full parent headers. -/
theorem parentRoleArchive_exec {P U : Type} {T Q : ℕ} (body : P → Pr P (T+273) Q prime U)
    (slots : Fin 38 ↪ Fin T) (hdr : Fin 6 ↪ Fin T) (tmp : Fin T) (regs : Fin 35 ↪ Fin T)
    (apart : ∀ i j, slots i ≠ hdr j) (scratch : ∀ i, slots i ≠ tmp) (fresh : ∀ j, tmp ≠ hdr j)
    (regSlots : ∀ i j, slots i ≠ regs j) (regHdr : ∀ i j, hdr i ≠ regs j)
    (capacity : (fun {q : ℕ} (_ : Program 38 q prime) => q) (RecursiveRowsNodeHeaders.program 142080) ≤ Q)
    : ∃ prog : Pr P (T+273) Q prime U, ∀ (node : RecursiveInterchangeLayout.Descriptor) (w B rows : ℕ),
    node.width = 64*(w+1) → node.rows = 142080*rows → node.beforeH = B*prime^(64*((w+1)*64)) →
    let role := { node with rows := rows }
    let K := node.beforeRows*rows*node.between*node.afterD
    let W := B*prime^(64*((w+1)*64))*K
    let M := prime^(w+1)
    ∀ (_ : role.Positive) (u : HS (T+273) Q prime U) (S : Stacks (T+273) prime),
    let bank := Fin.castAddEmb 273 (n := T)
    let read := fun i => S.R (bank i)
    RepT (RecursiveChildQuotients.input (Routines.hdr node)) (embStk (slots.trans bank) S).L
      (embStk (slots.trans bank) S).R →
    S.L (bank tmp) = [] → read tmp = [] → (∀ i, read (hdr i) = []) →
    read (regs 2) = binSyms M.size M → read (regs 28) = binSyms 1 1 →
    (read (regs 33)).length = w →
    (∀ j : Fin 273, S.L (j.natAdd T) = [] ∧ S.R (j.natAdd T) = []) →
    ∃ z F t, z.user = u.user ∧ Exec body prog (mk u S) t (mk z F) ∧
      t ≤ ((RecursiveRowsQuotient.constant 142080+30)*142080*43+152402152)*
        (M^16*((M^112*B)*prime^(64*((w+1)*64))*K)) ∧
      (∀ i j, F.R (borrowedHeaders T i j) =
        (Routines.hdr (helperAdjacentView (w+1) 1 W i) j).map bitSymbol) ∧
      ∀ k, (∀ i, slots i ≠ k) → (∀ i, hdr i ≠ k) →
        F.L (bank k) = S.L (bank k) ∧ F.R (bank k) = read k := by
  let bank := Fin.castAddEmb 273 (n := T)
  have load := loadRoleHeaders_exec body (slots.trans bank) (hdr.trans bank) (bank tmp)
    (fun i j => bank.injective.ne (apart i j)) (fun i => bank.injective.ne (scratch i))
    (fun j => bank.injective.ne (fresh j)) capacity
  let machine := RecursiveRowsNodeHeaders.program (q := prime) 142080
  let src := fun i : Fin 6 => bank (slots (⟨3+i.val,by omega⟩ : Fin 38))
  refine ⟨.seq (.seq (statePlacedNormalized (slots.trans bank) capacity
    (Nat.zero_lt_of_lt machine.start.isLt) Empty.elim (foreign machine))
    (loadDimensions src (hdr.trans bank) (bank tmp) (List.finRange 6)))
    (.seq (prepareHelperSeeds hdr regs) (helperHeaderSweep
      (fun i => (borrowedArchiveBank i).trans (parentArchive T)) (List.finRange 127))),?_⟩
  intro node w B rows width split label role K W M pos u S _ read rep tl tr empty base unit clock free
  obtain ⟨v,D,m,same,divide,price,filled,off⟩ := load node rows split pos.2.1 u S rep tl tr empty
  have keep k (a : ∀ i, slots i ≠ k) (b : ∀ i, hdr i ≠ k) :=
    off (bank k) (fun i => bank.injective.ne (a i)) (fun i => bank.injective.ne (b i))
  have retained j := (keep (regs j) (fun i => regSlots i j) (fun i => regHdr i j)).2
  have high (i : Fin T) (j : Fin 273) : bank i ≠ j.natAdd T := by
    intro eq
    have e := congrArg Fin.val eq
    change i.val = T+j.val at e
    omega
  obtain ⟨z,F,n,user,archive,time,ready,left,right⟩ := prepareRoleHeaders_exec body hdr regs node w B rows
    label pos v D ((retained 2).trans base) ((retained 28).trans unit)
    ((congrArg List.length (retained 33)).trans clock) filled (fun j => by
      obtain ⟨l,r⟩ := off _ (fun i => high (slots i) j) (fun i => high (hdr i) j)
      exact ⟨l.trans (free j).1,r.trans (free j).2⟩)
  let V := M^16*((M^112*B)*prime^(64*((w+1)*64))*K)
  have vol : RecursiveInterchangeLayout.volume prime role = V := by
    dsimp [RecursiveInterchangeLayout.volume,role,V,K,M]
    rw [label,width,show 64*(w+1) = (w+1)*64 by omega,pow_mul]
    ring
  have value (i : Fin 6) := (RecursiveHeaderBounds.values_le_volume
    Shared50ModularControl.prime_prime.two_le role pos i).trans_eq vol
  have rowBound : rows ≤ V := value 1
  have nonzero : 0 < V := lt_of_lt_of_le pos.2.1 rowBound
  have bits (i : Fin 6) : (Routines.hdr role i).length ≤ V+1 := by
    have h := GrowingCounterData.canonical_width _ ((Routines.hdr_headers role).2 i)
    rw [(Routines.hdr_headers role).1 i] at h
    exact h.trans (Nat.add_le_add_right ((Nat.log2_le_self _).trans (value i)) 1)
  have sum (is : List (Fin 6)) :
      (is.map (fun i => 8*(Routines.hdr role i).length+8)).sum ≤ is.length*(24*V) := by
    induction is with
    | nil => simp
    | cons i is ih =>
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      rw [Nat.succ_mul is.length]
      have := bits i
      omega
  have copies := sum (List.finRange 6)
  rw [List.length_finRange] at copies
  rw [split] at price
  refine ⟨z,F,_,user.trans same,Exec.seq divide archive,?_,ready,
    fun k a b => ⟨(congrFun left _).trans (keep k a b).1,(right k).trans (keep k a b).2⟩⟩
  exact archiveCost_le _ rows V _ m n nonzero rowBound copies price time

/-- Initial contents of the divider, arithmetic registers and blank archive
on the fixed 80-tape setup bank. -/
def ParentArchiveInput (node : RecursiveInterchangeLayout.Descriptor) (w : ℕ)
    (D : Stacks (80+273) prime) : Prop :=
    let M := prime^(w+1)
    let slots := Fin.castAddEmb 42 (n := 38)
    let hdr := (Fin.natAddEmb 38 (m := 6)).trans (Fin.castAddEmb 36)
    let tmp := (44 : Fin 80)
    let regs := Fin.natAddEmb 45 (m := 35)
    let bank := Fin.castAddEmb 273 (n := 80)
    let read := fun i => D.R (bank i)
    RepT (RecursiveChildQuotients.input (Routines.hdr node)) (embStk (slots.trans bank) D).L
      (embStk (slots.trans bank) D).R ∧
    D.L (bank tmp) = [] ∧ read tmp = [] ∧ (∀ i, read (hdr i) = []) ∧
    read (regs 2) = binSyms M.size M ∧ read (regs 28) = binSyms 1 1 ∧
    (read (regs 33)).length = w ∧
    (∀ j : Fin 273, D.L (j.natAdd 80) = [] ∧ D.R (j.natAdd 80) = [])

/-- Run the parent archive producer before a host stage. The continuation
receives the physical headers and the original worker and scratch stacks. -/
theorem parentArchiveThen_exec {T L Q : ℕ} {P U : Type}
    (host : P → Pr P (80+((T+273)+L)) Q prime U)
    (capacity : (fun {q : ℕ} (_ : Program 38 q prime) => q) (RecursiveRowsNodeHeaders.program 142080) ≤ Q) :
    ∃ setup, ∀ (node : RecursiveInterchangeLayout.Descriptor) (w B rows : ℕ),
    node.width = 64*(w+1) → node.rows = 142080*rows → node.beforeH = B*prime^(64*((w+1)*64)) →
    let role := {node with rows := rows}
    let K := node.beforeRows*rows*node.between*node.afterD
    let W := B*prime^(64*((w+1)*64))*K
    let M := prime^(w+1)
    ∀ (_ : role.Positive) (u : HS _ Q prime U) (S : Stacks _ prime),
    ParentArchiveInput node w (embStk (archiveSetupPlacement 80 T L) S) →
    ∀ code (price : ℝ) (post : Stacks _ prime → Prop),
    (∀ v (F : Stacks (80+((T+273)+L)) prime), (∀ i j, F.R (((borrowedHeaders T i j).castAdd L).natAdd 80) =
        (Routines.hdr (helperAdjacentView (w+1) 1 W i) j).map bitSymbol) →
      (∀ k : Fin T, let p := ((k.castAdd 273).castAdd L).natAdd 80
        F.L p = S.L p ∧ F.R p = S.R p) →
      (∀ k : Fin L, let p := (k.natAdd (T+273)).natAdd 80
        F.L p = S.L p ∧ F.R p = S.R p) →
      ∃ z G t, Exec host code (mk v F) t (mk z G) ∧ (t : ℝ) ≤ price ∧ z.user = v.user ∧ post G) →
    ∃ z G t, Exec host (.seq setup code) (mk u S) t (mk z G) ∧
      (t : ℝ) ≤ (((RecursiveRowsQuotient.constant 142080+30)*142080*43+152402152)*
        (M^16*((M^112*B)*prime^(64*((w+1)*64))*K)) : ℕ)+price ∧ z.user = u.user ∧ post G := by
  let slots := Fin.castAddEmb 42 (n := 38)
  let hdr := (Fin.natAddEmb 38 (m := 6)).trans (Fin.castAddEmb 36)
  let tmp := (44 : Fin 80)
  let regs := Fin.natAddEmb 45 (m := 35)
  let e := archiveSetupPlacement 80 T L
  obtain ⟨prog,prepare⟩ := parentRoleArchive_exec (P := Empty) (U := U) Empty.elim slots hdr tmp regs
    (by intro i j eq; have h := congrArg Fin.val eq; change i.val = 38+j.val at h; omega)
    (by intro i eq; have h := congrArg Fin.val eq; change i.val = 44 at h; omega)
    (by intro j eq; have h := congrArg Fin.val eq; change 44 = 38+j.val at h; omega)
    (by intro i j eq; have h := congrArg Fin.val eq; change i.val = 45+j.val at h; omega)
    (by intro i j eq; have h := congrArg Fin.val eq; change 38+i.val = 45+j.val at h; omega) capacity
  refine ⟨embProg e Empty.elim prog,?_⟩
  intro node w B rows width split label role K W M pos u S input code price post stage
  let D := embStk e S
  obtain ⟨rep,tl,tr,empty,base,unit,clock,free⟩ := input
  obtain ⟨v,F,m,user,run,bill,ready,_⟩ := prepare node w B rows width split label pos (embDn e u) D
    rep tl tr empty base unit clock free
  obtain ⟨y,E,placed,same,headers,workers,leaf⟩ := archiveSetupPlacement_exec (ι := Empty.elim)
    Empty.elim host (fun x => nomatch x) prog u S _ v F m run ready
  obtain ⟨z,G,n,exec,paid,last,done⟩ := stage y E headers workers leaf
  refine ⟨z,G,m+n,Exec.seq placed exec,?_,last.trans (same.trans user),done⟩
  rw [Nat.cast_add]
  exact add_le_add (Nat.cast_le.mpr bill) paid

end IntegerMultBounds.MathlibTM2.M6.BitNode
