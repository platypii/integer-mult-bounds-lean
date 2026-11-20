module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps
public import IntegerMultBounds.MathlibTM2.Host.StatePlacement
import IntegerMultBounds.MathlibTM2.Host.ChunkSwap
import IntegerMultBounds.Machine.RecursiveHeaderBounds
import IntegerMultBounds.MathlibTM2.Cover.FallbackPrefixVolume
public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodRecordWeights
public import IntegerMultBounds.MathlibTM2.Cover.FallbackMiddleSwap
public import IntegerMultBounds.MathlibTM2.Cover.FallbackLeafSignRun

/-! Run the weighted leaf word on the shared caller payload. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open M8.RevMachine RecursiveInterchangeLayout SharedBankStageInput
variable {T P M G B : ℕ} {F U : Type}

/-- A frame and its caller agree on the leading tapes. The remaining tapes
may contain any stacks that represent a blank tape. -/
private theorem frameRep_iff {A k : ℕ} (bank : Tapes T A) (fits : T ≤ k)
    (L R : Fin k → List (Fin (A+4))) :
    RepT (raw bank k) L R ↔
      RepT bank (fun i => L (i.castLE fits)) (fun i => R (i.castLE fits)) ∧
      ∀ i : Fin k, T ≤ i.val → ∀ x, readAt blank (L i) (R i) x = blank := by
  constructor
  · intro rep
    constructor
    · intro i x
      simpa [raw,i.isLt] using rep (i.castLE fits) x
    · intro i hi x
      simpa [raw,Nat.not_lt.mpr hi] using (rep i x).symm
  · rintro ⟨common,work⟩ i x
    by_cases hi : i.val < T
    · simpa [raw,hi] using common ⟨i.val,hi⟩ x
    · simpa [raw,hi] using (work i (Nat.le_of_not_gt hi) x).symm

/-- Run a coordinate frame block on its own ports in the caller's state space.
Both entry and return use the graph's exact bank postcondition. -/
theorem placedFrame_exec {K Q A k : ℕ} (block : Graph.Block T A) (x y : Tapes T A)
    (correct : GraphContract.Runs block x y k) (ports : Fin block.tapes ↪ Fin K)
    (capacity : block.states ≤ Q) (body : F → Pr F K Q A U) (u : HS K Q A U)
    (S : Stacks K A) (fits : T ≤ block.tapes)
    (ready : RepT x (fun i => S.L (ports (i.castLE fits))) (fun i => S.R (ports (i.castLE fits))))
    (work : ∀ i : Fin block.tapes, T ≤ i.val → ∀ j, readAt blank (S.L (ports i)) (S.R (ports i)) j = blank) :
    let pos := Nat.zero_lt_of_lt block.program.start.isLt
    ∃ z D t, z.user = u.user ∧ t ≤ 1 + (k * (block.tapes+5)+6) ∧
      Exec body (statePlacedNormalized ports capacity pos Empty.elim (foreign block.program))
        (mk u S) t (mk z D) ∧
      RepT y (fun i => D.L (ports (i.castLE fits))) (fun i => D.R (ports (i.castLE fits))) ∧
      (∀ i : Fin block.tapes, T ≤ i.val → ∀ j, readAt blank (D.L (ports i)) (D.R (ports i)) j = blank) ∧
      ∀ h, (∀ j, ports j ≠ h) → D.L h = S.L h ∧ D.R h = S.R h := by
  intro pos
  obtain ⟨v,E,_,rfl,next,user,_,_,_,l,bound,run⟩ := foreign_exec (P := Empty) Empty.elim
    block.program correct (stateLiftDown pos (embDn ports u)) (embStk ports S) _ rfl
      ((frameRep_iff x fits _ _).mpr ⟨ready,work⟩)
  obtain ⟨z,_,hz,placed⟩ := statePlaced_exec_normalized ports ports.injective capacity pos Empty.elim
    (body' := body) (fun e => nomatch e) u S run
  have returned : RepT (raw y block.tapes) (embStk ports (embOvr ports E.get S)).L
      (embStk ports (embOvr ports E.get S)).R := by rwa [embStk_ovr ports.injective]
  obtain ⟨common,blankWork⟩ := (frameRep_iff y fits _ _).mp returned
  exact ⟨z,_,_,hz.trans user,Nat.add_le_add_left bound 1,placed,common,blankWork,
    fun h off => embOvr_off _ _ off⟩

/-- Insert the packed leaf's record and arithmetic tapes after the common
bank. Entry and restore can use the same trailing workspace at different sizes. -/
def framePorts {common tapes work : ℕ} (record : ℕ) (fits : tapes ≤ common+work) :
    Fin tapes ↪ Fin ((common+record)+work) where
  toFun i := ⟨if i.val < common then i.val else i.val+record,by
    have := i.isLt
    split <;> omega⟩
  inj' := by
    intro i j eq
    have h := congrArg Fin.val eq
    dsimp only at h
    apply Fin.ext
    split_ifs at h <;> omega

/-- Execute a frame on either side of a packed leaf. Every record stack is
preserved exactly, and the entire shared workspace again reads blank. -/
theorem recordFrame_exec {Q A k work : ℕ} (record : ℕ) (block : Graph.Block T A)
    (x y : Tapes T A) (correct : GraphContract.Runs block x y k)
    (leading : T ≤ block.tapes) (fits : block.tapes ≤ T+work) (capacity : block.states ≤ Q)
    (body : F → Pr F ((T+record)+work) Q A U) (u : HS _ Q A U) (S : Stacks _ A)
    (ready : RepT x (fun i => S.L ((i.castAdd record).castAdd work))
      (fun i => S.R ((i.castAdd record).castAdd work)))
    (blankWork : ∀ (j : Fin work) a, readAt blank (S.L (j.natAdd (T+record)))
      (S.R (j.natAdd (T+record))) a = blank) :
    let ports := framePorts record fits
    ∃ z D t, z.user = u.user ∧ t ≤ 1+(k*(block.tapes+5)+6) ∧
      Exec body (statePlacedNormalized ports capacity (Nat.zero_lt_of_lt block.program.start.isLt)
        Empty.elim (foreign block.program)) (mk u S) t (mk z D) ∧
      RepT y (fun i => D.L ((i.castAdd record).castAdd work))
        (fun i => D.R ((i.castAdd record).castAdd work)) ∧
      (∀ (j : Fin work) a, readAt blank (D.L (j.natAdd (T+record)))
        (D.R (j.natAdd (T+record))) a = blank) ∧
      ∀ j : Fin record, D.L ((j.natAdd T).castAdd work) = S.L ((j.natAdd T).castAdd work) ∧
        D.R ((j.natAdd T).castAdd work) = S.R ((j.natAdd T).castAdd work) := by
  intro ports
  have shared (i : Fin T) : ports (i.castLE leading) = (i.castAdd record).castAdd work := by
    apply Fin.ext
    simp [ports,framePorts,i.isLt]
  have privateSlot (i : Fin block.tapes) (h : T ≤ i.val) :
      ports i = (⟨i.val-T,by have := i.isLt; omega⟩ : Fin work).natAdd (T+record) := by
    apply Fin.ext
    simp [ports,framePorts,Nat.not_lt.mpr h]
    omega
  obtain ⟨z,D,t,user,bound,run,rep,clean,off⟩ := placedFrame_exec block x y correct ports capacity body u S
    leading (by simpa only [shared] using ready)
    (by intro i h; rw [privateSlot i h]; exact blankWork _)
  refine ⟨z,D,t,user,bound,run,by simpa only [shared] using rep,?_,?_⟩
  · intro j a
    by_cases h : T+j.val < block.tapes
    · have eq : ports ⟨T+j.val,h⟩ = j.natAdd (T+record) := by
        apply Fin.ext
        simp [ports,framePorts]
        omega
      simpa only [eq] using clean ⟨T+j.val,h⟩ (by simp) a
    · have keep := off (j.natAdd (T+record)) (by
        intro i eq
        have hval := congrArg Fin.val eq
        have := i.isLt
        simp [ports,framePorts] at hval
        split_ifs at hval <;> omega)
      rw [keep.1,keep.2]
      exact blankWork j a
  · intro j
    apply off
    intro i eq
    have hval := congrArg Fin.val eq
    have := j.isLt
    simp [ports,framePorts] at hval
    split_ifs at hval <;> omega

/-- Place the packed leaf's final 31 arithmetic tapes next to the record
tapes, where frame changes preserve empty stacks exactly. Its interchange
tapes occupy the start of the workspace that frame changes may use. -/
def packedFramePorts {host priv work : ℕ} (fits : priv ≤ work) :
    Fin ((host+priv)+31) ↪ Fin ((host+31)+work) where
  toFun i := ⟨if i.val < host then i.val else if i.val < host+priv then i.val+31 else i.val-priv,by
    have := i.isLt
    split_ifs <;> omega⟩
  inj' := by
    intro i j eq
    have h := congrArg Fin.val eq
    have := i.isLt
    have := j.isLt
    dsimp only at h
    apply Fin.ext
    split_ifs at h <;> omega

theorem packedFramePorts_shared {host priv work : ℕ} (fits : priv ≤ work) (i : Fin host) :
    packedFramePorts fits ((i.castAdd priv).castAdd 31) = (i.castAdd 31).castAdd work := by
  apply Fin.ext
  simp [packedFramePorts,i.isLt]

theorem packedFramePorts_private {host priv work : ℕ} (fits : priv ≤ work) (i : Fin priv) :
    packedFramePorts fits ((i.natAdd host).castAdd 31) = (i.castLE fits).natAdd (host+31) := by
  apply Fin.ext
  simp [packedFramePorts,i.isLt]
  omega

theorem packedFramePorts_arithmetic {host priv work : ℕ} (fits : priv ≤ work) (i : Fin 31) :
    packedFramePorts fits (i.natAdd (host+priv)) = (i.natAdd host).castAdd work := by
  apply Fin.ext
  simp [packedFramePorts]
  split <;> omega

/-- Lift a packed leaf run into the frame's state space. Its returned stacks
supply the active workspace, and unused workspace retains its blank contents. -/
theorem packedFrame_exec {host priv work Q A q n : ℕ} (fits : priv ≤ work) (capacity : q ≤ Q)
    (pos : 0 < q) (leaf : Pr Empty ((host+priv)+31) q A U)
    (body : F → Pr F ((host+31)+work) Q A U) (u : HS _ Q A U) (S : Stacks _ A)
    (v : HS _ q A U) (E : Stacks _ A) :
    let ports := packedFramePorts (host := host) fits
    Exec Empty.elim leaf (mk (stateLiftDown pos (embDn ports u)) (embStk ports S)) n (mk v E) →
    (∀ (j : Fin priv) x, readAt blank (E.L ((j.natAdd host).castAdd 31))
      (E.R ((j.natAdd host).castAdd 31)) x = blank) →
    (∀ (j : Fin work) x, readAt blank (S.L (j.natAdd (host+31))) (S.R (j.natAdd (host+31))) x = blank) →
    ∃ z D, z.user = v.user ∧ Exec body (statePlacedNormalized ports capacity pos Empty.elim leaf)
      (mk u S) (1+n) (mk z D) ∧ embStk ports D = E ∧
      ∀ (j : Fin work) x, readAt blank (D.L (j.natAdd (host+31))) (D.R (j.natAdd (host+31))) x = blank := by
  intro ports run active free
  obtain ⟨z,_,user,placed⟩ := statePlaced_exec_normalized ports ports.injective capacity pos Empty.elim
    (body' := body) (fun f => nomatch f) u S run
  let D := embOvr ports E.get S
  have eq : embStk ports D = E := embStk_ovr ports.injective _ _
  refine ⟨z,D,user,placed,eq,?_⟩
  intro j x
  by_cases h : j.val < priv
  · let i : Fin priv := ⟨j.val,h⟩
    have onPort := packedFramePorts_private (host := host) fits i
    change ports ((i.natAdd host).castAdd 31) = j.natAdd (host+31) at onPort
    rw [← onPort]
    change readAt blank ((embStk ports D).L _) ((embStk ports D).R _) x = blank
    rw [eq]
    exact active i x
  · have off := embOvr_off (e := (ports : Fin _ → Fin _)) E.get S (j := j.natAdd (host+31)) (by
        intro i same
        have val := congrArg Fin.val same
        have := i.isLt
        simp [ports,packedFramePorts] at val
        split_ifs at val <;> omega)
    change readAt blank ((embOvr ports E.get S).L _) ((embOvr ports E.get S).R _) x = blank
    rw [off.1,off.2]
    exact free j x

/-- The local execution of a packed leaf can be replayed in any sufficiently
large coordinate frame with the same input on its selected ports. -/
def PackedFrameRun {host priv Q A : ℕ} (body : F → Pr F ((host+priv)+31) Q A U)
    (p : Pr F ((host+priv)+31) Q A U) (u : HS ((host+priv)+31) Q A U) (S : Stacks ((host+priv)+31) A)
    (n : ℕ) (z : HS ((host+priv)+31) Q A U) (D : Stacks ((host+priv)+31) A) : Prop :=
  ∀ {G : Type} (ι : F → G) {work states : ℕ} (fits : priv ≤ work) (cap : Q ≤ states) (pos : 0 < Q)
    (outer : G → Pr G ((host+31)+work) states A U)
    (v : HS ((host+31)+work) states A U) (E : Stacks ((host+31)+work) A),
    let ports := packedFramePorts (host := host) fits
    (∀ f, outer (ι f) = statePlacedPr ports cap pos ι (body f)) →
    stateLiftDown pos (embDn ports v) = u → embStk ports E = S →
    ∃ y, y.user = z.user ∧ Exec outer (statePlacedNormalized ports cap pos ι p)
      (mk v E) (1+n) (mk y (embOvr ports D.get E))

private theorem packedFrameRun_of_exec {host priv Q A : ℕ}
    {body : F → Pr F ((host+priv)+31) Q A U} {p u S n z D}
    (run : Exec body p (mk u S) n (mk z D)) : PackedFrameRun body p u S n z D := by
  intro G ι work states fits cap pos outer v E ports callbacks hu hS
  subst u S
  obtain ⟨y,_,user,placed⟩ := statePlaced_exec_normalized ports ports.injective cap pos ι callbacks v E run
  exact ⟨y,user,placed⟩

/-- Enclose a leaf in its entry and return blocks. The return bank depends on
the leaf result, so the restored parent retains the changed payload. -/
theorem framedLeaf_exec {Q A record work a b c : ℕ} {ι : Type*}
    (entry leave : Graph.Block T A) (parent child : Tapes T A)
    (changed restored : ι → Tapes T A) (enter : GraphContract.Runs entry parent child a)
    (restore : ∀ i, GraphContract.Runs leave (changed i) (restored i) c)
    (en : T ≤ entry.tapes) (ex : T ≤ leave.tapes) (ef : entry.tapes ≤ T+work)
    (xf : leave.tapes ≤ T+work) (eqs : entry.states ≤ Q) (xqs : leave.states ≤ Q)
    (body : F → Pr F ((T+record)+work) Q A U) (leaf : Pr F _ Q A U)
    (u : HS _ Q A U) (S : Stacks _ A) :
    let rep := fun bank (D : Stacks ((T+record)+work) A) => RepT bank
      (fun i : Fin T => D.L ((i.castAdd record).castAdd work))
      (fun i => D.R ((i.castAdd record).castAdd work))
    let clean := fun (D : Stacks ((T+record)+work) A) => ∀ (j : Fin work) x,
      readAt blank (D.L (j.natAdd (T+record))) (D.R (j.natAdd (T+record))) x = blank
    let keep := fun (D E : Stacks ((T+record)+work) A) => ∀ j : Fin record,
      D.L ((j.natAdd T).castAdd work) = E.L ((j.natAdd T).castAdd work) ∧
      D.R ((j.natAdd T).castAdd work) = E.R ((j.natAdd T).castAdd work)
    let place := fun (g : Graph.Block T A) (fits : g.tapes ≤ T+work) (cap : g.states ≤ Q) =>
      statePlacedNormalized (framePorts record fits) cap (Nat.zero_lt_of_lt g.program.start.isLt)
        Empty.elim (foreign g.program)
    rep parent S → clean S →
    (∀ v D, rep child D → clean D → keep D S → ∃ i z E n, z.user = v.user ∧ n ≤ b ∧
      Exec body leaf (mk v D) n (mk z E) ∧ rep (changed i) E ∧ clean E ∧ keep E D) →
    ∃ i z D n, z.user = u.user ∧ n ≤ (1+(a*(entry.tapes+5)+6))+b+(1+(c*(leave.tapes+5)+6)) ∧
      Exec body (((place entry ef eqs).seq leaf).seq (place leave xf xqs)) (mk u S) n (mk z D) ∧
      rep (restored i) D ∧ clean D ∧ keep D S := by
  intro rep clean keep place initial free runLeaf
  obtain ⟨v,D,t,hv,ht,first,inside,freeD,keepD⟩ :=
    recordFrame_exec record entry parent child enter en ef eqs body u S initial free
  obtain ⟨i,z,E,n,hz,hn,middle,out,freeE,keepE⟩ := runLeaf v D inside freeD keepD
  obtain ⟨y,G,l,hy,hl,last,done,freeG,keepG⟩ :=
    recordFrame_exec record leave _ _ (restore i) ex xf xqs body z E out freeE
  refine ⟨i,y,G,_,hy.trans (hz.trans hv),Nat.add_le_add (Nat.add_le_add ht hn) hl,
    (first.seq middle).seq last,done,freeG,?_⟩
  intro j
  exact ⟨(keepG j).1.trans ((keepE j).1.trans (keepD j).1),
    (keepG j).2.trans ((keepE j).2.trans (keepD j).2)⟩

/-- Read a dimension from the represented common bank into the caller's
arithmetic workspace, preserving every source cell including stored blanks. -/
theorem copyLeafDimension_exec {K extra Q : ℕ} (v : Descriptor) (roles : Tapes T prime)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime)
    (ctr : Fin CommonBank.K → Option ℕ) (st : Tapes 2 prime)
    (ports : Fin (CommonBank.count T + extra) ↪ Fin K) (j : Fin 6) (tmp dst : Fin K)
    (body : F → Pr F K Q prime U) (u : HS K Q prime U) (S : Stacks K prime)
    (initial : RepT (raw (CommonBank.bank roles (Routines.hdr v) f p node scalar ctr st) _)
      (S.L ∘ ports) (S.R ∘ ports)) (left : S.L tmp = []) (right : S.R tmp = []) :
    let src := ports ((CommonBank.headerSlot j).castAdd extra)
    let n := RecursiveDimensionBank.values v j
    [src,tmp,dst].Nodup → ∃ z, z.user = u.user ∧
      Exec body (copyDescriptor src tmp dst) (mk u S) (8*n.size+8)
        (mk z {S with R := Function.update S.R dst (binSyms n.size n ++ S.R dst)}) := by
  intro src n distinct
  have header (x : ℤ) := initial ((CommonBank.headerSlot j).castAdd extra) x
  simp only [(Embed.raw_left _ _).1,(Embed.raw_left _ _).2,(CommonBank.bank_header ..).1,
    (CommonBank.bank_header ..).2,CounterDimensions.descriptorHead,CounterDimensions.descriptorTape,
    Function.comp_apply] at header
  have canonical := Routines.canon (Mult.PhaseCellToeplitz.binBits_size_canonical n)
  rw [Routing.binaryCanonical_value_binBits _ _ (Nat.lt_size_self n)] at canonical
  have bits : Routines.hdr v j = binBits n.size n := canonical.symm
  obtain ⟨z,hz,run⟩ := copyDescriptor_exec body distinct (Routines.hdr v j) u S
    (fun x => (header x).symm) left right
  exact ⟨z,hz,by simpa only [bits,length_binBits,← binSyms_eq] using run⟩

def loadLeafDimensions {K Q A : ℕ} (src dst : Fin 6 → Fin K) (tmp : Fin K) :
    List (Fin 6) → Pr F K Q A U
  | [] => .act .done
  | j :: js => (copyDescriptor (src j) tmp (dst j)).seq (loadLeafDimensions src dst tmp js)

/-- Load the selected descriptor fields once. The cost depends only on their
canonical bit lengths, and every other register retains its original stacks. -/
theorem loadLeafDimensions_exec {K extra Q : ℕ} (v : Descriptor) (roles : Tapes T prime)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime)
    (ctr : Fin CommonBank.K → Option ℕ) (st : Tapes 2 prime)
    (ports : Fin (CommonBank.count T + extra) ↪ Fin K) (dst : Fin 6 ↪ Fin K) (tmp : Fin K)
    (apart : ∀ i j, ports i ≠ dst j) (scratch : ∀ j, tmp ≠ dst j)
    (srcFree : ∀ j, ports ((CommonBank.headerSlot j).castAdd extra) ≠ tmp)
    (body : F → Pr F K Q prime U) (js : List (Fin 6)) (unique : js.Nodup)
    (u : HS K Q prime U) (S : Stacks K prime)
    (initial : RepT (raw (CommonBank.bank roles (Routines.hdr v) f p node scalar ctr st) _)
      (S.L ∘ ports) (S.R ∘ ports)) (left : S.L tmp = []) (right : S.R tmp = [])
    (free : ∀ j ∈ js, S.R (dst j) = []) :
    let src := fun j => ports ((CommonBank.headerSlot j).castAdd extra)
    let n := RecursiveDimensionBank.values v
    ∃ z D, z.user = u.user ∧ Exec body (loadLeafDimensions src dst tmp js) (mk u S)
        ((js.map fun j => 8*(n j).size+8).sum+1) (mk z D) ∧
      D.L = S.L ∧ (∀ j ∈ js, D.R (dst j) = binSyms (n j).size (n j)) ∧
      ∀ k, (∀ j ∈ js, dst j ≠ k) → D.R k = S.R k := by
  intro src n
  induction js generalizing u S with
  | nil => exact ⟨u,S,rfl,Exec.act _ _,rfl,by simp,fun _ _ => rfl⟩
  | cons j js ih =>
    obtain ⟨w,hw,copy⟩ := copyLeafDimension_exec v roles f p node scalar ctr st ports j tmp (dst j)
      body u S initial left right (by simp [List.nodup_cons,srcFree,apart,scratch])
    rw [free j (by simp),List.append_nil] at copy
    let E := {S with R := Function.update S.R (dst j) (binSyms (n j).size (n j))}
    have keep (k) (off : k ≠ dst j) : E.R k = S.R k := Function.update_of_ne off _ _
    obtain ⟨z,D,hz,run,hL,loaded,off⟩ := ih unique.tail w E
      (fun i x => by simpa only [Function.comp_apply, E, Function.update_of_ne (apart i j)] using initial i x)
      left ((keep tmp (scratch j)).trans right)
      (fun i hi => (keep _ (dst.injective.ne (fun h => unique.notMem (h ▸ hi)))).trans (free i (by simp [hi])))
    refine ⟨z,D,hz.trans hw,?_,hL,?_,?_⟩
    · simpa only [loadLeafDimensions,List.map_cons,List.sum_cons,Nat.add_assoc] using Exec.seq copy run
    · intro i hi
      rcases List.mem_cons.mp hi with rfl | hi
      · exact (off (dst i) (fun a ha => dst.injective.ne (fun h => unique.notMem (h ▸ ha)))).trans (Function.update_self ..)
      · exact loaded i hi
    · intro k hk
      exact (off k (fun a ha => hk a (List.mem_cons_of_mem _ ha))).trans (keep _ (hk j (by simp)).symm)

/-- The leaf needs both outer dimensions, the row count, the gap and the
trailing width. The coefficient loader already supplies the modulus. -/
def leafDimensionFields : List (Fin 6) := [0,1,2,4,5]

theorem leafDimensionLoad_le (v : Descriptor) (positive : v.Positive) :
    (leafDimensionFields.map fun j => 8*(RecursiveDimensionBank.values v j).size+8).sum+1 ≤
      81*volume prime v := by
  have primeBound := IntegerMultBounds.Networks.Shared50ModularControl.prime_prime.two_le
  have size (j : Fin 6) : (RecursiveDimensionBank.values v j).size ≤ volume prime v :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans (RecursiveHeaderBounds.values_le_volume primeBound v positive j)
  have pos := RecursiveAffinePrepare.volume_positive primeBound v positive
  have := size 0
  have := size 1
  have := size 2
  have := size 4
  have := size 5
  simp only [leafDimensionFields,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  omega

/-- Bracket a leaf call with the five descriptor copies and their release.
The caller can retain any postcondition on the released bank. -/
theorem withLeafFields_exec {K extra Q : ℕ} (v : Descriptor) (positive : v.Positive)
    (roles : Tapes T prime) (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime)
    (ctr : Fin CommonBank.K → Option ℕ) (st : Tapes 2 prime)
    (ports : Fin (CommonBank.count T + extra) ↪ Fin K) (dst : Fin 6 ↪ Fin K) (tmp : Fin K)
    (apart : ∀ i j, ports i ≠ dst j) (scratch : ∀ j, tmp ≠ dst j)
    (srcFree : ∀ j, ports ((CommonBank.headerSlot j).castAdd extra) ≠ tmp)
    (body : F → Pr F K Q prime U) (u : HS K Q prime U) (S : Stacks K prime)
    (initial : RepT (raw (CommonBank.bank roles (Routines.hdr v) f p node scalar ctr st) _)
      (S.L ∘ ports) (S.R ∘ ports)) (left : S.L tmp = []) (right : S.R tmp = [])
    (free : ∀ j ∈ leafDimensionFields, S.R (dst j) = [])
    (leaf : Pr F K Q prime U) (budget : ℕ) (post : Stacks K prime → Prop) :
    let src := fun j => ports ((CommonBank.headerSlot j).castAdd extra)
    let n := RecursiveDimensionBank.values v
    let fields := leafDimensionFields.map dst
    (∀ w E, w.user = u.user → E.L = S.L →
      (∀ j ∈ leafDimensionFields, E.R (dst j) = binSyms (n j).size (n j)) →
      (∀ k, (∀ j ∈ leafDimensionFields, dst j ≠ k) → E.R k = S.R k) →
      ∃ z D t, z.user = w.user ∧ t ≤ budget ∧ Exec body leaf (mk w E) t (mk z D) ∧
        (∀ j ∈ leafDimensionFields, D.R (dst j) = E.R (dst j)) ∧
        post {D with R := fun k => if k ∈ fields then [] else D.R k}) →
    ∃ z D t, z.user = u.user ∧ t ≤ budget+102*volume prime v ∧
      Exec body ((loadLeafDimensions src dst tmp leafDimensionFields).seq
        (leaf.seq (Mult.ShortConv.clearWords fields))) (mk u S) t (mk z D) ∧
      (∀ j ∈ leafDimensionFields, D.R (dst j) = []) ∧ post D := by
  intro src n fields invoke
  have unique : leafDimensionFields.Nodup := by decide
  obtain ⟨w,E,hw,load,hL,loaded,off⟩ := loadLeafDimensions_exec v roles f p node scalar ctr st
    ports dst tmp apart scratch srcFree body leafDimensionFields unique u S initial left right free
  obtain ⟨z,D,t,hz,ht,run,preserved,result⟩ := invoke w E hw hL loaded off
  obtain ⟨y,hy,clear⟩ := Mult.ShortConv.clearWords_exec (body := body) fields (unique.map dst.injective) z D
  have lengths : fields.map (fun k => (D.R k).length) = leafDimensionFields.map (fun j => (n j).size) := by
    rw [show fields = _ from rfl,List.map_map]
    exact List.map_congr_left fun j hj => by simp [n,preserved j hj,loaded j hj]
  rw [lengths] at clear
  refine ⟨y,_,_,hy.trans (hz.trans hw),?_,Exec.seq load (Exec.seq run clear),?_,result⟩
  · have loadCost := leafDimensionLoad_le v positive
    have primeBound := IntegerMultBounds.Networks.Shared50ModularControl.prime_prime.two_le
    have size (j : Fin 6) : (n j).size ≤ volume prime v :=
      (Nat.size_le.mpr Nat.lt_two_pow_self).trans (RecursiveHeaderBounds.values_le_volume primeBound v positive j)
    have pos := RecursiveAffinePrepare.volume_positive primeBound v positive
    have := size 0
    have := size 1
    have := size 2
    have := size 4
    have := size 5
    have len : fields.length = 5 := by simp [fields,leafDimensionFields]
    rw [len]
    change _ + (t + (2 * ((n 0).size+((n 1).size+((n 2).size+((n 4).size+((n 5).size+0))))) + 2*5+1)) ≤ _
    omega
  · intro j hj
    simp [fields,List.mem_map_of_mem hj]

/-- Two interchange calls, three linear shears, and the final sign pass.
The cleanup multiplier depends only on the host program's push bound. -/
noncomputable def weightedLeafBodyCost [M8.Machine.Net] (N width tapes push : ℕ) : ℕ :=
  (1+186*push)*((3*(210*(2*(Nat.size prime+1)^2)+16120+100)+387)*N+
    2*(LeafCore.coreCost N width*(tapes+5)))+(12000*(1+186*push)+125)*N

noncomputable def weightedLeafCost [M8.Machine.Net] (N width tapes push : ℕ) : ℕ :=
  weightedLeafBodyCost N width tapes push + 550*N

private theorem shearHeaders_le (P M G B : ℕ) (hp : 0 < P) (hm : 0 < M) (hg : 0 < G) (hb : 0 < B) :
    6*(P.size+G.size+3*M.size+B.size)+37+(6*M.size+9) ≤ 100*((P*M*G)*(M*B)) := by
  have pre := Nat.le_mul_of_pos_right (P*M) hg
  have left := Nat.le_mul_of_pos_right (P*M*G) (Nat.mul_pos hm hb)
  have right := Nat.le_mul_of_pos_left (M*B) (Nat.mul_pos (Nat.mul_pos hp hm) hg)
  have p := (Nat.le_mul_of_pos_right P hm).trans (pre.trans left)
  have g := (Nat.le_mul_of_pos_left G (Nat.mul_pos hp hm)).trans left
  have m := (Nat.le_mul_of_pos_right M hb).trans right
  have b := (Nat.le_mul_of_pos_left B hm).trans right
  have bits (x : ℕ) : x.size ≤ x := Nat.size_le.mpr Nat.lt_two_pow_self
  have := bits P
  have := bits G
  have := bits M
  have := bits B
  omega

private theorem threeStageCharge (base exchange push rate N : ℕ) (pos : 0 < N) (linear : base ≤ rate*N) :
    let clean := fun x => x+(125+31*(6*(push*x)))
    2*clean (base+(exchange+6))+clean base ≤ (1+186*push)*((3*rate+387)*N+2*exchange) := by
  intro clean
  have total : 3*base+2*exchange+387 ≤ (3*rate+387)*N+2*exchange := by
    rw [Nat.add_mul,Nat.mul_assoc]
    omega
  apply le_trans _ (Nat.mul_le_mul_left _ total)
  dsimp [clean]
  nlinarith

private theorem weightedLeafTime [M8.Machine.Net] {P M G B V width tapes push n m : ℕ}
    (hP : 0 < P) (hM : 0 < M) (hG : 0 < G) (hB : 0 < B) (size : (P*M*G)*(M*B) = V)
    (signBound : m ≤ (12000*(1+186*push)+125)*(P*(M*(G*(M*B))))) :
    n ≤ middleShearsCost P M G B V width tapes push → n+m ≤ weightedLeafBodyCost V width tapes push := by
  intro hn
  let N := (P*M*G)*(M*B)
  let shearRate := 210*(2*(Nat.size prime+1)^2)+16120
  let exchange := LeafCore.coreCost V width*(tapes+5)
  let base := (6*(P.size+G.size+3*M.size+B.size)+37)+((6*M.size+9)+shearRate*N)
  have linear : base ≤ (shearRate+100)*N := by
    rw [Nat.add_mul shearRate 100 N]
    simpa only [base,Nat.add_left_comm,Nat.add_comm,Nat.add_assoc] using
      Nat.add_le_add_right (shearHeaders_le P M G B hP hM hG hB) (shearRate*N)
  let cleanup := fun x => x+(125+31*(6*(push*x)))
  have bound : n ≤ 2*cleanup (base+(exchange+6))+cleanup base := by
    let headCost := 6*(P.size+G.size+3*M.size+B.size)+37
    let bulk := (6*M.size+9)+shearRate*N
    change n ≤ 2*cleanup (headCost+(bulk+(exchange+6)))+cleanup base at hn
    rw [← Nat.add_assoc headCost bulk (exchange+6)] at hn
    exact hn
  have pos : 0 < N := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hP hM) hG) (Nat.mul_pos hM hB)
  have charge := threeStageCharge base exchange push (shearRate+100) N pos linear
  have shape : P*(M*(G*(M*B))) = N := by simp only [N,Nat.mul_assoc]
  rw [shape] at signBound
  have cost := Nat.add_le_add (bound.trans charge) signBound
  dsimp only [exchange,shearRate,N] at cost
  rw [size] at cost
  exact cost

private theorem signReleaseCost (N push : ℕ) (pos : 0 < N) :
    12000*N+(125+31*(6*(push*(12000*N)))) ≤ (12000*(1+186*push)+125)*N := by
  nlinarith only [pos]

open M8.Machine in
private theorem zeroBranchCapacity [M8.Machine.Net] :
    217 ≤ stateCount (ArbitraryWidthOriginalZeroBranch.zeroProgram (t := 7) Fin.castSucc (Fin.last 6)) := by
  unfold stateCount
  omega

open M8.Machine in
/-- The zero-width branch alone supplies enough states for the leaf shears
and sign routine. The positive-width branch adds to the same state space. -/
theorem leafCoreCapacity [M8.Machine.Net] (io : Fin T) : 217 ≤ (LeafCore.core io).states :=
  zeroBranchCapacity.trans ((Nat.le_add_right _ (stateCount
    (ArbitraryWidthOriginalRun.program (t := 7) Fin.castSucc (Fin.last 6)))).trans (Nat.le_add_right _ 1))

theorem weightedLeaf_exec [M8.Machine.Net] [NeZero M] (v : Descriptor) (positive : v.Positive)
    (w : ℕ) (width : v.width = w+1) (radix : prime^v.width = M)
    (weight inv : ZMod M) (unit : weight*inv = 1) (io : Fin T) (roles : Tapes T prime)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime)
    (ctr : Fin CommonBank.K → Option ℕ) (st : Tapes 2 prime) :
    let P := v.beforeRows*v.rows*v.beforeH
    let G := v.between
    let B := v.afterD
    let size : (P*M*G)*(M*B) = volume prime v := by simp [P,G,B,volume,radix,Nat.mul_assoc]
    let c := fun b : Bool => if b then (⟨(-weight).val,(-weight).val_lt⟩ : Fin M) else ⟨inv.val,inv.val_lt⟩
    ∀ (word : Fin ((P*M*G)*(M*B)) → ZMod 2), roles.head io = 0 → roles.tape io = leafBitTape (List.ofFn word) →
    let block := LeafCore.core io
    ∀ {K : ℕ} (sim : Fin block.tapes ↪ Fin K) (pair : Fin 20 ↪ Fin K) (r : Fin 13 ↪ Fin K) (gap tail : Fin K)
      (dst : Fin 6 ↪ Fin K) (_rowSlots : ∀ i : Fin 3, dst (i.castLE (by decide)) = r (i.castLE (by decide)))
      (_gapSlot : dst 4 = gap) (_tailSlot : dst 5 = tail)
      (_fieldsOff : ∀ i j, sim i ≠ dst j)
      (_scratchOff : ∀ i : Fin 13, (3 ≤ i ∧ i < 10) ∨ i = 12 → ∀ j ∈ leafDimensionFields, r i ≠ dst j)
      (_pairKeep : ∀ i ∈ [0,4,12], ∀ j ∈ leafDimensionFields, pair i ≠ dst j)
      (_radixPort : r 11 = pair 4)
      (_other : ∀ j ∈ [gap,tail,pair 0,pair 12], j ≠ r 4 ∧ j ≠ r 12),
      let dims : Fin 4 → Fin K := ![r 4,gap,r 12,tail]
      ∀
      (_pairOff : ∀ i j, j ∈ [0,4,12] → sim i ≠ pair j) (_dimsOff : ∀ i j, sim i ≠ dims j) (slot : Fin block.tapes) (_leading : slot.val = io.val),
      let capacity := leafCoreCapacity io
      let src := fun b : Bool => ![dims 0,dims 1,if b then pair 12 else pair 0,dims 2,dims 3,pair 4]
      let ports := sim.trans (Fin.castAddEmb 31)
      let shear := statePlacedNormalized (Record.payloadBank (sim slot) (22 : Fin 31)) capacity
        (by decide : 0 < 217) Empty.elim initializedMiddleShear
      let prog := fun b => (Record.copyLeafHeaders (fun i => (src b i).castAdd 31)
        (middleHeaderTargets.trans (Fin.natAddEmb K)) ((4 : Fin 31).natAdd K) ((5 : Fin 31).natAdd K) (List.finRange 6)).seq
        (.seq shear (embProg ports Empty.elim (foreign block.program)))
      let lastProg := (Record.copyLeafHeaders (fun i => (src false i).castAdd 31)
        (middleHeaderTargets.trans (Fin.natAddEmb K)) ((4 : Fin 31).natAdd K) ((5 : Fin 31).natAdd K) (List.finRange 6)).seq shear
      let work := (List.finRange 31).map (Fin.natAddEmb K)
      let stage := fun b => (prog b).seq (clearWorkTapes work)
      let result := fun b x => swapLeafList v size (FiberLayoutData.translated x
        (fun i => (c b).val*(i.val/G%M)%M)) (FiberLayoutData.translated_length ..)
      let y := result true (result false word)
      let xs := FiberLayoutData.translated y (fun i => (c false).val*(i.val/G%M)%M)
      let len : xs.length = P*(M*(G*(M*B))) := by rw [FiberLayoutData.translated_length]; simp [Nat.mul_assoc]
      let signWord := fun i => xs.get (Fin.cast len.symm i)
      let signSrc := fun i : Fin 4 => src false (![0,1,5,4] i)
      let load := Record.copyLeafHeaders (fun i => (signSrc i).castAdd 31) (signHeaderTargets.trans (Fin.natAddEmb K))
        ((1 : Fin 31).natAdd K) ((2 : Fin 31).natAdd K) (List.finRange 4)
      let bank := signWork.trans (Record.payloadBank (sim slot) (0 : Fin 31))
      let child := (leafSignSetup (F := Empty)).seq (embProg (Fin.castAddEmb 2) Empty.elim leafSignReturn)
      let sign := load.seq (statePlacedNormalized bank capacity (by decide) Empty.elim child)
      let output := fun (S D : Stacks (K+31) prime) => RepT (raw (CommonBank.bank (SharedPlacementAlphabet.setTape roles io (leafBitTape (negateLeafHead signWord)) 0)
            (Routines.hdr v) f p node scalar ctr st) block.tapes) (D.L ∘ ports) (D.R ∘ ports) ∧
          (∀ x, readAt blank (D.L (ports slot)) (D.R (ports slot)) x = leafBitTape (negateLeafHead signWord) x) ∧
          (∀ (a : Fin v.beforeRows) (row : Fin v.rows) (pre : Fin v.beforeH)
              (mid : Fin v.between) (post : Fin v.afterD) (h t : ZMod M),
              (negateLeafHead signWord)[index prime v a row pre (weight*t).val mid (inv*h).val post]? =
                (List.ofFn word)[index prime v a row pre h.val mid t.val post]?) ∧
          (∀ j : Fin 31, D.L (j.natAdd K) = [] ∧ D.R (j.natAdd K) = []) ∧
          ∀ j : Fin K, (∀ i, sim i ≠ j) →
            D.L (j.castAdd 31) = S.L (j.castAdd 31) ∧ D.R (j.castAdd 31) = S.R (j.castAdd 31)
      ∀ (body : F → Pr F (K+31) block.states prime U) (u : HS (K+31) block.states prime U)
        (S : Stacks (K+31) prime) push, (∀ b, Fast.Main.mnProgPush (prog b) ≤ push) →
        Fast.Main.mnProgPush lastProg ≤ push → Fast.Main.mnProgPush sign ≤ push → (∀ f, Fast.Main.mnProgPush (body f) ≤ push) →
        (∀ j : Fin 31, S.L (j.natAdd K) = [] ∧ S.R (j.natAdd K) = []) →
        (∀ j ∈ leafDimensionFields, S.R ((dst j).castAdd 31) = []) →
        (∀ i : Fin 13, (3 ≤ i ∧ i < 10) ∨ i = 12 → S.R ((r i).castAdd 31) = []) →
        S.R ((pair 4).castAdd 31) = binSyms M.size M →
        S.R ((pair 0).castAdd 31) = binSyms M.size inv.val →
        S.R ((pair 12).castAdd 31) = binSyms M.size (-weight).val →
        RepT (raw (CommonBank.bank roles (Routines.hdr v) f p node scalar ctr st) block.tapes) (S.L ∘ ports) (S.R ∘ ports) →
        let rr := r.trans (Fin.castAddEmb 31)
        let setup := (middleRowDescriptor ((Fin.castLEEmb (by decide : 11 ≤ 13)).trans rr)).seq
          (bzero (rr 11) (rr 12) (rr 5))
        let leaf := ((((stage false).seq (stage true)).seq (lastProg.seq (clearWorkTapes work))).seq (sign.seq (clearWorkTapes work)))
        let fields := dst.trans (Fin.castAddEmb 31)
        let headers := fun j => ports ((CommonBank.headerSlot j).castAdd LeafCore.small)
        let readFields := loadLeafDimensions headers fields ((0 : Fin 31).natAdd K) leafDimensionFields
        ∃ z D n, z.user = u.user ∧ n ≤ weightedLeafCost (volume prime v) v.width block.tapes push ∧
          Exec body (readFields.seq ((setup.seq (leaf.seq ((bclear (rr 4)).seq (bclear (rr 12))))).seq (Mult.ShortConv.clearWords (leafDimensionFields.map fields)))) (mk u S) n (mk z D) ∧
          output S D := by
  intro P G B size c word head input block K sim pair r gap tail dst rowSlots gapSlot tailSlot fieldsOff scratchOff pairKeep radixPort other dims pairOff dimsOff slot leading capacity src ports shear prog lastProg work stage result y xs len signWord signSrc load bank child sign output body u S push hp hl hsign hb free fieldEmpty empty modulus inverse negative initial rr setup leaf fields headers readFields
  have fromRows (u : HS (K+31) block.states prime U) (S : Stacks (K+31) prime) :
        (∀ j : Fin 31, S.L (j.natAdd K) = [] ∧ S.R (j.natAdd K) = []) →
        (∀ i : Fin 3, S.R ((r (i.castLE (by decide))).castAdd 31) =
          binSyms (RecursiveDimensionBank.values v (i.castLE (by decide))).size
            (RecursiveDimensionBank.values v (i.castLE (by decide)))) →
        (∀ i : Fin 13, (3 ≤ i ∧ i < 10) ∨ i = 12 → S.R ((r i).castAdd 31) = []) →
        S.R (gap.castAdd 31) = binSyms G.size G → S.R (tail.castAdd 31) = binSyms B.size B →
        S.R ((pair 4).castAdd 31) = binSyms M.size M →
        S.R ((pair 0).castAdd 31) = binSyms M.size inv.val →
        S.R ((pair 12).castAdd 31) = binSyms M.size (-weight).val →
        RepT (raw (CommonBank.bank roles (Routines.hdr v) f p node scalar ctr st) block.tapes) (S.L ∘ ports) (S.R ∘ ports) →
        ∃ z D n, z.user = u.user ∧ n ≤ weightedLeafBodyCost (volume prime v) v.width block.tapes push + 448*volume prime v ∧
          Exec body (setup.seq (leaf.seq ((bclear (rr 4)).seq (bclear (rr 12))))) (mk u S) n (mk z D) ∧ output S D := by
    intro free rows empty gapWord tailWord modulus inverse negative initial
    have core (u : HS (K+31) block.states prime U) (S : Stacks (K+31) prime) :
          (∀ j : Fin 31, S.L (j.natAdd K) = [] ∧ S.R (j.natAdd K) = []) →
          (∀ i, S.R ((dims i).castAdd 31) =
            (![binSyms P.size P,binSyms G.size G,binSyms M.size 0,binSyms B.size B] i)) →
          S.R ((pair 4).castAdd 31) = binSyms M.size M →
          S.R ((pair 0).castAdd 31) = binSyms M.size inv.val →
          S.R ((pair 12).castAdd 31) = binSyms M.size (-weight).val →
          RepT (raw (CommonBank.bank roles (Routines.hdr v) f p node scalar ctr st) block.tapes) (S.L ∘ ports) (S.R ∘ ports) →
          ∃ z D n, z.user = u.user ∧ n ≤ weightedLeafBodyCost (volume prime v) v.width block.tapes push ∧
            Exec body leaf (mk u S) n (mk z D) ∧ output S D := by
      intro free dimensions modulus inverse negative initial
      have hP := Nat.mul_pos (Nat.mul_pos positive.1 positive.2.1) positive.2.2.1
      have hG := positive.2.2.2.1
      have hB := positive.2.2.2.2
      have radixPower : M = prime^(w+1) := radix.symm.trans (congrArg (prime^·) width)
      have odd : Odd M := radix ▸ (IntegerMultBounds.Networks.Shared50ModularControl.prime_prime.odd_of_ne_two
        (by have := IntegerMultBounds.Networks.Shared50ModularControl.prime_odd; omega)).pow
      have apart (b : Bool) (i : Fin block.tapes) (j : Fin 6) : sim i ≠ src b j := by
        cases b <;> fin_cases j <;> first | exact dimsOff i 0 | exact dimsOff i 1 | exact dimsOff i 2 | exact dimsOff i 3 | exact pairOff i 0 (by decide) | exact pairOff i 4 (by decide) | exact pairOff i 12 (by decide)
      have headers (b : Bool) (i : Fin 6) : S.R ((src b i).castAdd 31) =
          (![binSyms P.size P,binSyms G.size G,binSyms M.size (c b).val,binSyms M.size 0,
            binSyms B.size B,binSyms M.size M] i) := by
        cases b <;> fin_cases i <;> first
          | exact dimensions 0 | exact dimensions 1 | exact dimensions 2 | exact dimensions 3
          | exact modulus | exact inverse | exact negative
      obtain ⟨b,H,n,hu,hn,run,rep,read,clean,keep⟩ := threeMiddleShears_exec v positive size w radixPower c hP hG hB
        word io roles head input f p node scalar ctr st sim src apart slot leading capacity body u S push hp hl hb free headers initial
      have data : List.ofFn signWord = xs := by
        apply List.ext_getElem
        · simpa only [List.length_ofFn] using len.symm
        · intros; simp [signWord]
      have hM : 0 < M := radixPower ▸ pow_pos IntegerMultBounds.Networks.Shared50ModularControl.prime_prime.pos _
      obtain ⟨z,D,m,hz,hm,last,out,frame⟩ := loadedLeafSign_exec (sim slot) capacity hP hG hM hB odd signWord signSrc
        body b H (by simpa only [data,Function.Embedding.trans_apply,Fin.castAddEmb_apply] using read)
        (by intro i
            rw [(keep _ (fun j => apart false j (![0,1,5,4] i))).2]
            fin_cases i <;> first | exact headers false 0 | exact headers false 1 | exact headers false 5 | exact headers false 4) clean
      have signBound := hm.trans (loadedLeafSign_cost_le P G M B hP hG hM hB)
      obtain ⟨z',J,k,hz',hk,release,preserved,empty⟩ := releaseMiddleWork body sign last signBound hsign hb clean
      have pos := Nat.mul_pos hP (Nat.mul_pos hM (Nat.mul_pos hG (Nat.mul_pos hM hB)))
      refine ⟨z',J,n+k,hz'.trans (hz.trans hu),?_,Exec.seq run release,?_,?_,?_,empty,?_⟩
      · exact weightedLeafTime hP hM hG hB size (hk.trans (signReleaseCost _ push pos)) hn
      · have updated := leafBank_writeRole v io (SharedPlacementAlphabet.setTape roles io (leafBitTape xs) 0)
            f p node scalar ctr st (leafBitTape (negateLeafHead signWord)) ports H J slot leading rep
            (fun i hi => ⟨(preserved (sim i)).1.trans (frame _ (sim.injective.ne hi)).1,
              (preserved (sim i)).2.trans (frame _ (sim.injective.ne hi)).2⟩) (by
              intro x
              change readAt blank (J.L ((sim slot).castAdd 31)) (J.R ((sim slot).castAdd 31)) x = _
              rw [(preserved (sim slot)).1,(preserved (sim slot)).2]; exact out x)
        simpa only [SharedPlacementAlphabet.setTape,Function.update_idem] using updated
      · intro x
        change readAt blank (J.L ((sim slot).castAdd 31)) (J.R ((sim slot).castAdd 31)) x = _
        rw [(preserved (sim slot)).1,(preserved (sim slot)).2]
        exact out x
      · exact weightedLeafOutput_entry v radix weight inv unit word
      · intro j hj
        have same := frame j (hj slot).symm
        exact ⟨(preserved j).1.trans (same.1.trans (keep j hj).1),(preserved j).2.trans (same.2.trans (keep j hj).2)⟩
    let ready : Stacks (K+31) prime := {S with R := Function.update (Function.update S.R (rr 4) (binSyms P.size P)) (rr 12) (binSyms M.size 0)}
    have keep (k : Fin K) (a : k ≠ r 4) (b : k ≠ r 12) : ready.R (k.castAdd 31) = S.R (k.castAdd 31) := by
      simp [ready,rr,a,b]
    have off (i) : sim i ≠ r 4 ∧ sim i ≠ r 12 := ⟨dimsOff i 0,dimsOff i 2⟩
    have right (j : Fin 31) : j.natAdd K ≠ rr 4 ∧ j.natAdd K ≠ rr 12 := by
      constructor <;> intro eq <;> have h := congrArg Fin.val eq <;> simp [rr] at h <;> omega
    have modOff : pair 4 ≠ r 4 ∧ pair 4 ≠ r 12 := by rw [← radixPort]; simp [r.injective.eq_iff]
    let post := output S
    suffices h : ∃ z D n, z.user = u.user ∧ n ≤ 432*P+(4*M.size+4)+(weightedLeafBodyCost (volume prime v) v.width block.tapes push+
            (2*P.size+2+(2*M.size+2))) ∧
            Exec body (setup.seq (leaf.seq ((bclear (rr 4)).seq (bclear (rr 12))))) (mk u S) n (mk z D) ∧
            D.R (rr 4) = S.R (rr 4) ∧ D.R (rr 12) = S.R (rr 12) ∧ post D by
      obtain ⟨z,D,n,hu,hn,run,_,_,result⟩ := h
      refine ⟨z,D,n,hu,?_,run,result⟩
      have hP : 0 < P := Nat.mul_pos (Nat.mul_pos positive.1 positive.2.1) positive.2.2.1
      have hM : 0 < M := NeZero.pos M
      have outer : P*M ≤ volume prime v := (Nat.le_mul_of_pos_right _ positive.2.2.2.1).trans
        (size ▸ Nat.le_mul_of_pos_right _ (Nat.mul_pos hM positive.2.2.2.2))
      have pBound := (Nat.le_mul_of_pos_right P hM).trans outer
      have mBound := (Nat.le_mul_of_pos_left M hP).trans outer
      have bitSize (x : ℕ) : x.size ≤ x := Nat.size_le.mpr Nat.lt_two_pow_self
      have := bitSize P
      have := bitSize M
      omega
    apply withLeafDimensions_exec body rr v.beforeRows v.rows v.beforeH M positive.1 positive.2.1
      positive.2.2.1 u S (rows 0) (rows 1) (rows 2) (by simpa [rr,radixPort] using modulus) empty leaf _ post
    intro w' _
    obtain ⟨z,D,n,hu,hn,run,rep,read,addr,clean,frame⟩ := core w' ready
      (fun j => ⟨(free j).1,by simpa [ready,Function.update_of_ne (right j).1,Function.update_of_ne (right j).2] using (free j).2⟩)
      (by intro i; fin_cases i
          · change ready.R (rr 4) = _; simp [ready,rr,r.injective.eq_iff,P]
          · exact (keep gap (other gap (by simp)).1 (other gap (by simp)).2).trans gapWord
          · exact Function.update_self ..
          · exact (keep tail (other tail (by simp)).1 (other tail (by simp)).2).trans tailWord)
      ((keep _ modOff.1 modOff.2).trans modulus)
      ((keep _ (other _ (by simp)).1 (other _ (by simp)).2).trans inverse)
      ((keep _ (other _ (by simp)).1 (other _ (by simp)).2).trans negative)
      (fun i x => by change _ = readAt blank (S.L ((sim i).castAdd 31)) (ready.R ((sim i).castAdd 31)) _; rw [keep _ (off i).1 (off i).2]; exact initial i x)
    refine ⟨z,D,n,hu,hn,run,(frame _ (fun i => (off i).1)).2,(frame _ (fun i => (off i).2)).2,?_,?_,addr,?_,?_⟩
    · intro i x
      simp only [Function.comp_apply,ports,rr,Function.Embedding.trans_apply,Fin.castAddEmb_apply,Function.update_apply,Fin.castAdd_inj,(off i).1,(off i).2,ite_false]; exact rep i x
    · intro x
      simp only [ports,rr,Function.Embedding.trans_apply,Fin.castAddEmb_apply,Function.update_apply,Fin.castAdd_inj,(off slot).1,(off slot).2,ite_false]; exact read x
    · intro j
      simpa [Function.update_of_ne (right j).1,Function.update_of_ne (right j).2] using clean j
    · intro j hj
      refine ⟨(frame j hj).1,?_⟩
      by_cases a : j = r 4
      · subst j; simp [rr,r.injective.eq_iff,empty 4 (by decide)]
      by_cases b : j = r 12
      · subst j; simp [rr,empty 12 (by decide)]
      simpa [rr,Function.update_apply,a,b] using ((frame j hj).2.trans (keep j a b))
  have apart (i j) : ports i ≠ fields j := by simpa [ports,fields] using fieldsOff i j
  have privateOff (i : Fin 31) (j : Fin K) : i.natAdd K ≠ j.castAdd 31 := by
    intro eq
    have h := congrArg Fin.val eq
    simp at h
    omega
  obtain ⟨z,D,n,hu,hn,run,_,result⟩ := withLeafFields_exec v positive roles f p node scalar ctr st ports fields
    ((0 : Fin 31).natAdd K) apart (fun j => privateOff 0 (dst j))
    (fun j => (privateOff 0 _).symm) body u S initial (free 0).1 (free 0).2 fieldEmpty
    (setup.seq (leaf.seq ((bclear (rr 4)).seq (bclear (rr 12))))) (weightedLeafBodyCost (volume prime v) v.width block.tapes push + 448*volume prime v) (output S) (by
      intro y E hy hL loaded keep
      have simKeep (i) := keep (ports i) (fun j _ => (apart i j).symm)
      have laneKeep (k : Fin K) (h : ∀ j ∈ leafDimensionFields, k ≠ dst j) :=
        keep (k.castAdd 31) (fun j hj => by simpa [fields] using (h j hj).symm)
      have privKeep (i : Fin 31) := keep (i.natAdd K) (fun j _ => (privateOff i (dst j)).symm)
      obtain ⟨z,D,t,hz,ht,exec,rep,read,addr,clean,frame⟩ := fromRows y E
        (fun j => ⟨(congrFun hL _).trans (free j).1,(privKeep j).trans (free j).2⟩)
        (fun i => by
          have mem : i.castLE (by decide : 3 ≤ 6) ∈ leafDimensionFields := by fin_cases i <;> decide
          simpa only [fields,Function.Embedding.trans_apply,Fin.castAddEmb_apply,rowSlots] using loaded _ mem)
        (fun i hi => (laneKeep _ (scratchOff i hi)).trans (empty i hi))
        (by simpa [fields,gapSlot,RecursiveDimensionBank.values,G] using loaded 4 (by decide))
        (by simpa [fields,tailSlot,RecursiveDimensionBank.values,B] using loaded 5 (by decide))
        ((laneKeep _ (pairKeep 4 (by decide))).trans modulus)
        ((laneKeep _ (pairKeep 0 (by decide))).trans inverse)
        ((laneKeep _ (pairKeep 12 (by decide))).trans negative)
        (fun i x => by simpa only [Function.comp_apply,hL,simKeep] using initial i x)
      have outside (k) (h : ∀ j ∈ leafDimensionFields, k ≠ fields j) : k ∉ leafDimensionFields.map fields := by
        rintro mem
        obtain ⟨j,hj,eq⟩ := List.mem_map.mp mem
        exact h j hj eq.symm
      refine ⟨z,D,t,hz,ht,exec,fun j _ => (frame (dst j) (fun i => fieldsOff i j)).2,?_,?_,addr,?_,?_⟩
      · intro i x
        simpa only [Function.comp_apply,if_neg (outside _ (fun j _ => apart i j))] using rep i x
      · intro x
        simpa only [if_neg (outside _ (fun j _ => apart slot j))] using read x
      · intro i
        simpa only [if_neg (outside _ (fun j _ => privateOff i (dst j)))] using clean i
      · intro k hk
        refine ⟨(frame k hk).1.trans (congrFun hL _),?_⟩
        by_cases mem : k.castAdd 31 ∈ leafDimensionFields.map fields
        · obtain ⟨j,hj,eq⟩ := List.mem_map.mp mem
          change (if k.castAdd 31 ∈ leafDimensionFields.map fields then [] else D.R _) = S.R _; rw [if_pos mem,← eq]; exact (fieldEmpty j hj).symm
        · exact (if_neg mem).trans ((frame k hk).2.trans (keep _ (fun j hj eq => mem (eq ▸ List.mem_map_of_mem hj)))))
  exact ⟨z,D,n,hu,by unfold weightedLeafCost; omega,run,result⟩

/-- Coefficient arithmetic and the two indexed archive reads fit in one
radix factor of the terminal volume. -/
private theorem leafPairCharge (w i j : ℕ) :
    let H := Nat.size (prime^(w+1))
    let C := 48*H*H+152*H+66
    (8*(j*H)+14*H+22)+((8*(i*H)+48*H*H+166*H+88)+
      (6*w+6+(14*H+16+(prime-2)*C+C+w*(12*H+15+prime*C))))+
      (2*H+2)+(8*H+8)+(6*H+7) ≤
      ((1000*(prime+1)+8*(i+j))*(2*(prime.size+1)^2))*prime^(w+1) := by
  intro H C
  have setup := prefixSetup_volume_le w 0
  have polynomial : (8*(j*H)+14*H+22)+((8*(i*H)+48*H*H+166*H+88)+
      (6*w+6+(14*H+16+(prime-2)*C+C+w*(12*H+15+prime*C))))+
      (2*H+2)+(8*H+8)+(6*H+7) ≤ (1000*(prime+1)+8*(i+j))*((w+2)*(H+1)^2) := by
    grw [Nat.sub_le prime 2]
    dsimp only [C]
    ring_nf
    omega
  apply polynomial.trans
  rw [Nat.mul_assoc]
  exact Nat.mul_le_mul_left _ (by simpa [H,Nat.add_assoc] using setup)

section
local instance (w : ℕ) : NeZero (prime^(w+1)) :=
  ⟨(pow_pos IntegerMultBounds.Networks.Shared50ModularControl.prime_prime.pos _).ne'⟩

/-- A frame change preserves the 24 record stacks and 31 arithmetic stacks.
Read the packed leaf's inputs directly from those preserved host tapes. -/
theorem packedFrame_inputs {common priv work m d w : ℕ} (fits : priv ≤ work)
    (parent : Fin m → ZMod (prime^(w+1))) (pivot : Fin d → ZMod (prime^(w+1)))
    (bank : Tapes common prime) (pivotTail parentTail : List (Fin (prime+4))) :
    let host := common+24
    let ports := packedFramePorts (host := host) fits
    let caller := (Fin.natAddEmb common (m := 24)).trans (Fin.castAddEmb priv)
    let record := (Fin.natAddEmb common (m := 24)).trans ((Fin.castAddEmb 31).trans (Fin.castAddEmb work))
    ∀ (S D : Stacks ((host+31)+work) prime),
      (∀ j : Fin 55, D.L ((j.natAdd common).castAdd work) = S.L ((j.natAdd common).castAdd work) ∧
        D.R ((j.natAdd common).castAdd work) = S.R ((j.natAdd common).castAdd work)) →
      (∀ j : Fin 31, S.L ((j.natAdd host).castAdd work) = [] ∧ S.R ((j.natAdd host).castAdd work) = []) →
      S.R (record 18) = [] →
      PackedLeafInputs (goodChildPorts.trans record) (prime^(w+1)).size parent pivot S pivotTail parentTail →
      RepT bank (fun i => D.L (((i.castAdd 24).castAdd 31).castAdd work))
        (fun i => D.R (((i.castAdd 24).castAdd 31).castAdd work)) →
      (∀ (j : Fin work) x, readAt blank (D.L (j.natAdd (host+31))) (D.R (j.natAdd (host+31))) x = blank) →
      let E := embStk ports D
      (∀ j : Fin 31, E.L (j.natAdd (host+priv)) = [] ∧ E.R (j.natAdd (host+priv)) = []) ∧
      E.R ((caller 18).castAdd 31) = [] ∧
      PackedLeafInputs ((goodChildPorts.trans caller).trans (Fin.castAddEmb 31)) (prime^(w+1)).size
        parent pivot E pivotTail parentTail ∧
      RepT bank (fun i => E.L (((i.castAdd 24).castAdd priv).castAdd 31))
        (fun i => E.R (((i.castAdd 24).castAdd priv).castAdd 31)) ∧
      ∀ (j : Fin priv) x, readAt blank (E.L ((j.natAdd host).castAdd 31))
        (E.R ((j.natAdd host).castAdd 31)) x = blank := by
  intro host ports caller record S D keep free spare archives rep clean E
  have eqR (j : Fin 24) : E.R ((caller j).castAdd 31) = S.R (record j) := by
    change D.R (ports (((j.natAdd common).castAdd priv).castAdd 31)) = _
    rw [packedFramePorts_shared]
    exact (keep (j.castAdd 31)).2
  refine ⟨?_,(eqR _).trans spare,?_,?_,?_⟩
  · intro j
    have h := keep (j.natAdd 24)
    have idx : ((j.natAdd 24).natAdd common : Fin (common+55)) = j.natAdd host := by
      apply Fin.ext
      simp [host,Nat.add_assoc]
    rw [idx] at h
    simpa only [E,embStk,Function.comp_apply,ports,packedFramePorts_arithmetic] using
      And.intro (h.1.trans (free j).1) (h.2.trans (free j).2)
  · exact ⟨(eqR _).trans archives.weights,(eqR _).trans archives.pivots,(eqR _).trans archives.modulus,
      (eqR _).trans archives.one,(congrArg List.length (eqR _)).trans archives.clock,
      fun j h => (eqR _).trans (archives.scratch j h)⟩
  · simpa only [E,embStk,Function.comp_apply,ports,packedFramePorts_shared] using rep
  · intro j x
    simpa only [E,embStk,Function.comp_apply,ports,packedFramePorts_private] using clean (j.castLE fits) x

/-- The leaf's returned common bank is the restore block's input. The
24 records retain their stacks, and the 31 arithmetic tapes return to their
initial empty stacks, so all 55 satisfy the frame contract. -/
theorem packedFrame_return {common priv work A : ℕ} (fits : priv ≤ work) (bank : Tapes common A) :
    let host := common+24
    let ports := packedFramePorts (host := host) fits
    ∀ (S D : Stacks ((host+31)+work) A) (E : Stacks ((host+priv)+31) A),
      embStk ports D = E →
      RepT bank (fun i => E.L (((i.castAdd 24).castAdd priv).castAdd 31))
        (fun i => E.R (((i.castAdd 24).castAdd priv).castAdd 31)) →
      (∀ j : Fin 24, let k := ((j.natAdd common).castAdd priv).castAdd 31
        E.L k = (embStk ports S).L k ∧ E.R k = (embStk ports S).R k) →
      (∀ j : Fin 31, E.L (j.natAdd (host+priv)) = [] ∧ E.R (j.natAdd (host+priv)) = []) →
      (∀ j : Fin 31, S.L ((j.natAdd host).castAdd work) = [] ∧ S.R ((j.natAdd host).castAdd work) = []) →
      RepT bank (fun i => D.L (((i.castAdd 24).castAdd 31).castAdd work))
        (fun i => D.R (((i.castAdd 24).castAdd 31).castAdd work)) ∧
      ∀ j : Fin 55, D.L ((j.natAdd common).castAdd work) = S.L ((j.natAdd common).castAdd work) ∧
        D.R ((j.natAdd common).castAdd work) = S.R ((j.natAdd common).castAdd work) := by
  intro host ports S D E projected rep record cleared free
  subst E
  simp only [embStk,Function.comp_apply,ports,packedFramePorts_shared,packedFramePorts_arithmetic] at rep record cleared
  refine ⟨rep,?_⟩
  intro j
  refine Fin.addCases (m := 24) (n := 31) ?_ ?_ j
  · exact record
  · intro k
    have idx : ((k.natAdd 24).natAdd common : Fin (common+55)) = k.natAdd host := by
      apply Fin.ext
      simp [host,Nat.add_assoc]
    rw [idx]
    exact ⟨(cleared k).1.trans (free k).1.symm,(cleared k).2.trans (free k).2.symm⟩

/-- Row arithmetic reuses the coefficient bank's cleared slots. Its padded
zero occupies the one extra slot after that bank. -/
def packedRowPorts : Fin 13 ↪ Fin 21 := ⟨![1,2,3,7,8,9,10,11,13,17,5,4,20],by decide⟩

def packedFieldPorts : Fin 6 ↪ Fin 20 := ⟨![1,2,3,4,5,6],by decide⟩

private theorem ext_ofFn_read {N : ℕ} (word : Fin N → ZMod 2) (k : ℕ) :
    ((List.ofFn word)[k]?).getD 0 = ext word k := by
  by_cases h : k < N <;> simp [List.getElem?_ofFn,ext,h]

/-- Insert the record tapes between the represented common bank and the
interchange workspace. The two banks are disjoint and the workspace may
already contain explicit blank cells left by an earlier interchange. -/
theorem packedLeafPlacement {common record priv A : ℕ} (bank : Tapes common A)
    (L R : Fin ((common+record)+priv) → List (Fin (A+4))) :
    let sim := appendPrivate (Fin.castAddEmb (n := common) record) priv
    let caller := (Fin.natAddEmb common (m := record)).trans (Fin.castAddEmb priv)
    (∀ i j, sim i ≠ caller j) ∧
      (RepT (raw bank (common+priv)) (L ∘ sim) (R ∘ sim) ↔
        RepT bank (fun i => L ((i.castAdd record).castAdd priv))
          (fun i => R ((i.castAdd record).castAdd priv)) ∧
        ∀ (j : Fin priv) x, readAt blank (L (j.natAdd (common+record))) (R (j.natAdd (common+record))) x = blank) := by
  intro sim caller
  constructor
  · intro i j
    refine Fin.addCases (m := common) (n := priv) ?_ ?_ i
    · intro k eq
      have h := congrArg Fin.val eq
      simp [sim,caller,appendPrivate_shared] at h
      omega
    · intro k eq
      have h := congrArg Fin.val eq
      simp [sim,caller,appendPrivate_work] at h
      omega
  · constructor
    · intro rep
      constructor
      · intro i x
        simpa only [(Embed.raw_left _ _).1,(Embed.raw_left _ _).2,Function.comp_apply,sim,
          appendPrivate_shared,Fin.castAddEmb_apply] using rep (i.castAdd priv) x
      · intro j x
        simpa only [(Embed.raw_right _ _).1,(Embed.raw_right _ _).2,Function.comp_apply,sim,
          appendPrivate_work,sub_zero] using (rep (j.natAdd common) x).symm
    · rintro ⟨shared,empty⟩ i
      refine Fin.addCases (m := common) (n := priv) ?_ ?_ i
      · intro j x
        simpa only [(Embed.raw_left _ _).1,(Embed.raw_left _ _).2,Function.comp_apply,sim,
          appendPrivate_shared,Fin.castAddEmb_apply] using shared j x
      · intro j x
        simpa only [(Embed.raw_right _ _).1,(Embed.raw_right _ _).2,Function.comp_apply,sim,
          appendPrivate_work,sub_zero] using (empty j x).symm

theorem packedWeightedLeaf_exec [M8.Machine.Net] [Fintype F] {m d : ℕ} (v : Descriptor) (positive : v.Positive)
    (w : ℕ) (width : v.width = w+1)
    (parent : Fin m → ZMod (prime^(w+1))) (j : Fin m) (parentInv : ZMod (prime^(w+1)))
    (reciprocal : parent j * parentInv = 1) (pivot : Fin d → ZMod (prime^(w+1)))
    (i : Fin d) (pivotUnit : IsUnit (pivot i)) (io : Fin T) (roles : Tapes T prime)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime)
    (ctr : Fin CommonBank.K → Option ℕ) (st : Tapes 2 prime) :
    let M := prime^(w+1)
    let weight := parent j * pivot i
    let inv := parentInv * Ring.inverse (pivot i)
    let P := v.beforeRows*v.rows*v.beforeH
    let G := v.between
    let B := v.afterD
    let size : (P*M*G)*(M*B) = volume prime v := by simp [P,G,B,volume,M,width,Nat.mul_assoc]
    let c := fun b : Bool => if b then (⟨(-weight).val,(-weight).val_lt⟩ : Fin M) else ⟨inv.val,inv.val_lt⟩
    ∀ (word : Fin ((P*M*G)*(M*B)) → ZMod 2), roles.head io = 0 → roles.tape io = leafBitTape (List.ofFn word) →
    let block := LeafCore.core io
    let common := CommonBank.count T
    let host := common+24
    let K := host+LeafCore.small
    let sim := appendPrivate (Fin.castAddEmb (n := common) 24) LeafCore.small
    let caller := (Fin.natAddEmb common (m := 24)).trans (Fin.castAddEmb LeafCore.small)
    let workBank := goodLeafPorts.trans caller
    let pair := (Fin.castAddEmb 1).trans workBank
    let r := packedRowPorts.trans workBank
    let dst := packedFieldPorts.trans pair
    let gap := dst 4
    let tail := dst 5
    let dims : Fin 4 → Fin K := ![r 4,gap,r 12,tail]
    let slot := (LeafCore.roleSlot io).castAdd LeafCore.small
    let capacity := leafCoreCapacity io
      let src := fun b : Bool => ![dims 0,dims 1,if b then pair 12 else pair 0,dims 2,dims 3,pair 4]
      let ports := sim.trans (Fin.castAddEmb 31)
      let shear := statePlacedNormalized (Record.payloadBank (sim slot) (22 : Fin 31)) capacity
        (by decide : 0 < 217) Empty.elim initializedMiddleShear
      let prog := fun b => (Record.copyLeafHeaders (fun i => (src b i).castAdd 31)
        (middleHeaderTargets.trans (Fin.natAddEmb K)) ((4 : Fin 31).natAdd K) ((5 : Fin 31).natAdd K) (List.finRange 6)).seq
        (.seq shear (embProg ports Empty.elim (foreign block.program)))
      let lastProg := (Record.copyLeafHeaders (fun i => (src false i).castAdd 31)
        (middleHeaderTargets.trans (Fin.natAddEmb K)) ((4 : Fin 31).natAdd K) ((5 : Fin 31).natAdd K) (List.finRange 6)).seq shear
      let work := (List.finRange 31).map (Fin.natAddEmb K)
      let stage := fun b => (prog b).seq (clearWorkTapes work)
      let result := fun b x => swapLeafList v size (FiberLayoutData.translated x
        (fun i => (c b).val*(i.val/G%M)%M)) (FiberLayoutData.translated_length ..)
      let y := result true (result false word)
      let xs := FiberLayoutData.translated y (fun i => (c false).val*(i.val/G%M)%M)
      let len : xs.length = P*(M*(G*(M*B))) := by rw [FiberLayoutData.translated_length]; simp [Nat.mul_assoc]
      let signWord := fun i => xs.get (Fin.cast len.symm i)
      let signSrc := fun i : Fin 4 => src false (![0,1,5,4] i)
      let load := Record.copyLeafHeaders (fun i => (signSrc i).castAdd 31) (signHeaderTargets.trans (Fin.natAddEmb K))
        ((1 : Fin 31).natAdd K) ((2 : Fin 31).natAdd K) (List.finRange 4)
      let bank := signWork.trans (Record.payloadBank (sim slot) (0 : Fin 31))
      let child := (leafSignSetup (F := Empty)).seq (embProg (Fin.castAddEmb 2) Empty.elim leafSignReturn)
      let sign := load.seq (statePlacedNormalized bank capacity (by decide) Empty.elim child)
      let output := fun (S D : Stacks (K+31) prime) => (RepT (CommonBank.bank (SharedPlacementAlphabet.setTape roles io (leafBitTape (negateLeafHead signWord)) 0)
            (Routines.hdr v) f p node scalar ctr st)
            (fun i => D.L (((i.castAdd 24).castAdd LeafCore.small).castAdd 31))
            (fun i => D.R (((i.castAdd 24).castAdd LeafCore.small).castAdd 31)) ∧
            ∀ (j : Fin LeafCore.small) x, readAt blank (D.L ((j.natAdd host).castAdd 31))
              (D.R ((j.natAdd host).castAdd 31)) x = blank) ∧
          (∀ x, readAt blank (D.L (ports slot)) (D.R (ports slot)) x = leafBitTape (negateLeafHead signWord) x) ∧
          (∀ (a : Fin v.beforeRows) (row : Fin v.rows) (pre : Fin v.beforeH)
              (mid : Fin v.between) (post : Fin v.afterD) (h t : ZMod M),
              (negateLeafHead signWord)[index prime v a row pre (weight*t).val mid (inv*h).val post]? =
                (List.ofFn word)[index prime v a row pre h.val mid t.val post]?) ∧
          (∀ j : Fin 31, D.L (j.natAdd K) = [] ∧ D.R (j.natAdd K) = []) ∧
          ∀ j : Fin 24, let k := (caller j).castAdd 31
            D.L k = S.L k ∧ D.R k = S.R k
      ∀ (body : F → Pr F (K+31) block.states prime U) (u : HS (K+31) block.states prime U)
        (S : Stacks (K+31) prime),
        let bodyPush := Fast.Main.mnPushC body
        let push := max (max (Fast.Main.mnProgPush (prog false)) (Fast.Main.mnProgPush (prog true)))
          (max (Fast.Main.mnProgPush lastProg) (max (Fast.Main.mnProgPush sign) bodyPush))
        (∀ j : Fin 31, S.L (j.natAdd K) = [] ∧ S.R (j.natAdd K) = []) →
        S.R ((caller 18).castAdd 31) = [] →
        ∀ (pivotTail parentTail : List (Fin (prime+4))),
        PackedLeafInputs ((goodChildPorts.trans caller).trans (Fin.castAddEmb 31)) M.size parent pivot S pivotTail parentTail →
        RepT (CommonBank.bank roles (Routines.hdr v) f p node scalar ctr st)
          (fun i => S.L (((i.castAdd 24).castAdd LeafCore.small).castAdd 31))
          (fun i => S.R (((i.castAdd 24).castAdd LeafCore.small).castAdd 31)) →
        (∀ (j : Fin LeafCore.small) x, readAt blank (S.L ((j.natAdd host).castAdd 31))
          (S.R ((j.natAdd host).castAdd 31)) x = blank) →
        let rr := r.trans (Fin.castAddEmb 31)
        let setup := (middleRowDescriptor ((Fin.castLEEmb (by decide : 11 ≤ 13)).trans rr)).seq
          (bzero (rr 11) (rr 12) (rr 5))
        let leaf := ((((stage false).seq (stage true)).seq (lastProg.seq (clearWorkTapes work))).seq (sign.seq (clearWorkTapes work)))
        let fields := dst.trans (Fin.castAddEmb 31)
        let headers := fun j => ports ((CommonBank.headerSlot j).castAdd LeafCore.small)
        let readFields := loadLeafDimensions headers fields ((0 : Fin 31).natAdd K) leafDimensionFields
        let call := (readFields.seq ((setup.seq (leaf.seq ((bclear (rr 4)).seq (bclear (rr 12))))).seq (Mult.ShortConv.clearWords (leafDimensionFields.map fields))))
        let coeff := pair.trans (Fin.castAddEmb 31)
        let coefficientRate := (1000*(prime+1)+8*(i.val+j.val))*(2*(prime.size+1)^2)
        ∃ z D n, z.user = u.user ∧ n ≤ weightedLeafCost (volume prime v) v.width block.tapes push+
          coefficientRate*M ∧
          (let program := (signedChildPair prime j.val i.val coeff true).seq
              (call.seq (Mult.ShortConv.clearWords [coeff 0,coeff 14,coeff 12]))
           Exec body program (mk u S) n (mk z D) ∧ PackedFrameRun body program u S n z D) ∧
          output S D ∧ ∃ next : Fin ((P*M*G)*(M*B)) → ZMod 2,
            List.ofFn next = negateLeafHead signWord ∧
            ∀ a < v.beforeRows, ∀ row < v.rows, ∀ pre < v.beforeH, ∀ mid < v.between,
              ∀ post < v.afterD, ∀ h t : ZMod M,
                ext next (index prime v a row pre (weight*t).val mid (inv*h).val post) =
                ext word (index prime v a row pre h.val mid t.val post) := by
  intro M weight inv P G B size c word head input block common host K sim caller workBank pair r dst gap tail dims slot capacity src ports shear prog lastProg work stage result y xs len signWord signSrc load bank child sign output body u S bodyPush push free spare pivotTail parentTail recordInputs commonRep privateBlank rr setup leaf fields headers readFields call coeff coefficientRate
  have hp (b : Bool) : Fast.Main.mnProgPush (prog b) ≤ push := by cases b <;> dsimp only [push] <;> omega
  have hl : Fast.Main.mnProgPush lastProg ≤ push := by dsimp only [push]; omega
  have hsign : Fast.Main.mnProgPush sign ≤ push := by dsimp only [push]; omega
  have hb (f) : Fast.Main.mnProgPush (body f) ≤ push := (Fast.Main.mn_progPush_le_pushC body f).trans (by dsimp only [push,bodyPush]; omega)
  have placement := packedLeafPlacement (record := 24) (priv := LeafCore.small)
    (CommonBank.bank roles (Routines.hdr v) f p node scalar ctr st)
    (fun j => S.L (j.castAdd 31)) (fun j => S.R (j.castAdd 31))
  have apart (i : Fin block.tapes) (j : Fin 21) : sim i ≠ caller (goodLeafPorts j) :=
    placement.1 i _
  have leading : slot.val = io.val := rfl
  have initial : RepT (raw (CommonBank.bank roles (Routines.hdr v) f p node scalar ctr st) block.tapes)
      (S.L ∘ ports) (S.R ∘ ports) := placement.2.mpr ⟨commonRep,privateBlank⟩
  have pairEq : pair = goodChildPorts.trans caller := by
    apply Function.Embedding.ext
    intro j
    exact congrArg caller (DFunLike.congr_fun goodLeafPorts_pair j)
  have archives : PackedLeafInputs coeff M.size parent pivot S pivotTail parentTail := by
    simpa only [coeff,pairEq] using recordInputs
  have rowSlots (i : Fin 3) : dst (i.castLE (by decide)) = r (i.castLE (by decide)) :=
    congrArg workBank ((by decide : ∀ i : Fin 3, (packedFieldPorts (i.castLE (by decide))).castAdd 1 =
      packedRowPorts (i.castLE (by decide))) i)
  have fieldsOff (i j) : sim i ≠ dst j := apart i _
  have pairOff (i) (j : Fin 20) (_ : j ∈ [0,4,12,14]) : sim i ≠ pair j := apart i _
  have dimsOff (i) (j : Fin 4) : sim i ≠ dims j := by fin_cases j <;> exact apart i _
  have fieldPair (i) (hi : i ∈ leafDimensionFields) (j) (hj : j ∈ [0,14,12]) : dst i ≠ pair j :=
    pair.injective.ne ((by decide : ∀ i ∈ leafDimensionFields, ∀ j ∈ [0,14,12], packedFieldPorts i ≠ j) i hi j hj)
  have pairKeep (j) (hj : j ∈ [0,4,12]) (i) (hi : i ∈ leafDimensionFields) : pair j ≠ dst i :=
    pair.injective.ne ((by decide : ∀ j ∈ [0,4,12], ∀ i ∈ leafDimensionFields, j ≠ packedFieldPorts i) j hj i hi)
  have scratchOff (i : Fin 13) (hi : (3 ≤ i ∧ i < 10) ∨ i = 12) (j) (hj : j ∈ leafDimensionFields) : r i ≠ dst j :=
    workBank.injective.ne ((by decide : ∀ i : Fin 13, (3 ≤ i ∧ i < 10) ∨ i = 12 → ∀ j ∈ leafDimensionFields,
      packedRowPorts i ≠ (packedFieldPorts j).castAdd 1) i hi j hj)
  have pairScratch (i : Fin 13) (hi : (3 ≤ i ∧ i < 10) ∨ i = 12) (j : Fin 20) (hj : j ∈ [0,14,12]) : r i ≠ pair j :=
    workBank.injective.ne ((by decide : ∀ i : Fin 13, (3 ≤ i ∧ i < 10) ∨ i = 12 → ∀ j : Fin 20,
      j ∈ [0,14,12] → packedRowPorts i ≠ j.castAdd 1) i hi j hj)
  have other (k) (hk : k ∈ [gap,tail,pair 0,pair 12]) : k ≠ r 4 ∧ k ≠ r 12 := by
    simp at hk
    rcases hk with rfl | rfl | rfl | rfl <;> constructor <;> apply workBank.injective.ne <;> decide
  have fieldEmpty (j) (hj : j ∈ leafDimensionFields) : S.R ((dst j).castAdd 31) = [] :=
    archives.scratch (packedFieldPorts j) ((by decide : ∀ j ∈ leafDimensionFields,
      (packedFieldPorts j ≤ 14 ∧ packedFieldPorts j ≠ 4) ∨ packedFieldPorts j = 17) j hj)
  have empty (i : Fin 13) (hi : (3 ≤ i ∧ i < 10) ∨ i = 12) : S.R ((r i).castAdd 31) = [] := by
    rcases (by decide : ∀ i : Fin 13, (3 ≤ i ∧ i < 10) ∨ i = 12 → packedRowPorts i = 20 ∨
      ∃ j : Fin 20, packedRowPorts i = j.castAdd 1 ∧ ((j ≤ 14 ∧ j ≠ 4) ∨ j = 17)) i hi with eq | ⟨j,eq,free⟩
    · change S.R ((workBank (packedRowPorts i)).castAdd 31) = []; rw [eq]; exact spare
    · change S.R ((workBank (packedRowPorts i)).castAdd 31) = []; rw [eq]; exact archives.scratch j free
  have distinct (k : Fin K) (h : ∀ a ∈ [0,14,12], k ≠ pair a) :
      k.castAdd 31 ∉ [coeff 0,coeff 14,coeff 12] := by
    simp [coeff,h 0 (by decide),h 14 (by decide),h 12 (by decide)]
  have outside (k) : ports k ∉ [coeff 0,coeff 14,coeff 12] := distinct (sim k) (fun a ha => pairOff k a (by
    simp at ha ⊢; rcases ha with h | h | h <;> simp [h]))
  have privateOff (k : Fin 31) : k.natAdd K ∉ [coeff 0,coeff 14,coeff 12] := by
    have ne (a : Fin 20) : k.natAdd K ≠ coeff a := by
      intro eq
      have h := congrArg Fin.val eq
      simp [coeff] at h
      omega
    simp [ne]
  obtain ⟨z,D,t,hz,ht,run,_,post⟩ := withLeafPair_exec body coeff parent j parentInv reciprocal pivot i pivotUnit
    IntegerMultBounds.Networks.Shared50ModularControl.prime_prime u S pivotTail parentTail call
    (weightedLeafCost (volume prime v) v.width block.tapes push) (output S) archives.weights archives.pivots archives.modulus archives.one archives.clock archives.scratch (by
      intro y E hy unit hL modWord invWord negWord keep
      obtain ⟨z,D,t,hz,ht,run,rep,read,addr,clean,frame⟩ := weightedLeaf_exec v positive w width
        (show prime^v.width = M by rw [width]) weight inv unit io roles f p node scalar ctr st word head input
        sim pair r gap tail dst rowSlots rfl rfl fieldsOff scratchOff pairKeep rfl other
        (fun k a ha => pairOff k a (by simp at ha ⊢; rcases ha with h | h | h <;> simp [h]))
        dimsOff slot leading body y E push hp hl hsign hb
        (fun k => ⟨(congrFun hL _).trans (free k).1,(keep _ (privateOff k)).trans (free k).2⟩)
        (fun k hk => (keep _ (distinct _ (fieldPair k hk))).trans (fieldEmpty k hk))
        (fun k hk => (keep _ (distinct _ (pairScratch k hk))).trans (empty k hk))
        modWord invWord negWord (fun k x => by
          change _ = readAt blank (E.L (ports k)) (E.R (ports k)) _; rw [hL,keep _ (outside k)]; exact initial k x)
      refine ⟨z,D,t,hz,ht,run,?_,?_,?_,addr,?_,?_⟩
      · intro k hk
        simp at hk
        rcases hk with rfl | rfl | rfl <;> exact (frame _ (fun k => pairOff k _ (by decide))).2
      · apply (packedLeafPlacement (record := 24) (priv := LeafCore.small) _
          (fun j => D.L (j.castAdd 31))
          (fun j => if j.castAdd 31 ∈ [coeff 0,coeff 14,coeff 12] then [] else D.R (j.castAdd 31))).2.mp
        intro k x
        change _ = readAt blank (D.L (ports k)) (if ports k ∈ _ then [] else D.R (ports k)) _
        exact (rep k x).trans (congrArg (fun tape => readAt blank (D.L (ports k)) tape _)
          (ite_eq_right (outside k)).symm)
      · intro x
        change readAt blank _ (if ports slot ∈ _ then [] else D.R (ports slot)) _ = _
        rw [if_neg (outside slot)]
        exact read x
      · intro k
        simpa only [if_neg (privateOff k)] using clean k
      · intro j
        dsimp only
        generalize eq : caller j = k
        have hk (i) : sim i ≠ k := eq ▸ placement.1 i j
        clear eq
        refine ⟨(frame k hk).1.trans (congrFun hL _),?_⟩
        change (if k.castAdd 31 ∈ [coeff 0,coeff 14,coeff 12] then [] else D.R _) = _
        split_ifs with mem
        · simp [coeff] at mem
          rcases mem with h | h | h <;> subst k <;> exact (archives.scratch _ (by decide)).symm
        · exact (frame k hk).2.trans (keep _ mem))
  have charge := leafPairCharge w i.val j.val
  have length : (negateLeafHead signWord).length = (P*M*G)*(M*B) := by
    rw [negateLeafHead_length]
    simp only [Nat.mul_assoc]
  let next := fun k : Fin ((P*M*G)*(M*B)) => (negateLeafHead signWord).get (k.cast length.symm)
  have cells : List.ofFn next = negateLeafHead signWord := by
    apply List.ext_getElem <;> simp [next,length]
  refine ⟨z,D,t,hz,by dsimp only at ht charge; dsimp only [coefficientRate,M]; omega,
    ⟨run,packedFrameRun_of_exec run⟩,post,next,cells,?_⟩
  intro a ha row hr pre hp mid hm tail ht h t
  have addr := post.2.2.1 ⟨a,ha⟩ ⟨row,hr⟩ ⟨pre,hp⟩ ⟨mid,hm⟩ ⟨tail,ht⟩ h t
  rw [← cells] at addr
  simpa only [ext_ofFn_read] using congrArg (fun cell => cell.getD 0) addr

end

/-- Follow the descriptor counter from rank down to zero. Each step sees
its own descriptor view, while the conclusion acts on the full rank fields. -/
theorem weightedCoordinates_exec {r M q w K Q A : ℕ} [NeZero M] {α : Type*}
    (v : Descriptor) (width : v.width = r) (radix : M = q^w)
    (weight inv : Fin r → ZMod M) (unit : ∀ i, weight i * inv i = 1)
    (body : F → Pr F K Q A U) (call : Fin r → Pr F K Q A U) (budget : Fin r → ℕ)
    (ready : ℕ → Stacks K A → (ℕ → α) → Prop) :
    let view := fun i : Fin r => {(RecursiveInterchangeLayout.child M 1 1 v i i.rev) with width := w}
    let addr := fun a row pre mid post (x : IntegerMultBounds.Swap.Shear.State (Fin r) (ZMod M)) =>
      index M v a row pre (FlatCoordinateLayout.rank x.1).val mid (FlatCoordinateLayout.rank x.2).val post
    (∀ (i : Fin r) u S word, ready (i.val+1) S word → ∃ z D out n, z.user = u.user ∧ n ≤ budget i ∧
      Exec body (call i) (mk u S) n (mk z D) ∧ ready i.val D out ∧
      ∀ a < v.beforeRows, ∀ row < v.rows, ∀ pre < (view i).beforeH, ∀ mid < (view i).between,
        ∀ post < (view i).afterD, ∀ h t : ZMod M,
        out (index q (view i) a row pre (weight i*t).val mid (inv i*h).val post) =
          word (index q (view i) a row pre h.val mid t.val post)) →
    ∀ u S word, ready r S word → ∃ z D out n, z.user = u.user ∧ n ≤ ((List.finRange r).map budget).sum+1 ∧
      Exec body (Prog.seqList ((List.finRange r).reverse.map call)) (mk u S) n (mk z D) ∧ ready 0 D out ∧
      ∀ a < v.beforeRows, ∀ row < v.rows, ∀ pre < v.beforeH, ∀ mid < v.between, ∀ post < v.afterD, ∀ x,
        out (addr a row pre mid post (Weighted.child r weight inv x)) = word (addr a row pre mid post x) := by
  intro view addr step
  have run (is : List (Fin r)) (order : ∀ (j : Fin is.length), (is.get j).val + j.val + 1 = is.length) : ∀ u S word, ready is.length S word → ∃ z D out n, z.user = u.user ∧ n ≤ (is.map budget).sum+1 ∧
      Exec body (Prog.seqList (is.map call)) (mk u S) n (mk z D) ∧ ready 0 D out ∧
      ∀ a < v.beforeRows, ∀ row < v.rows, ∀ pre < v.beforeH, ∀ mid < v.between, ∀ post < v.afterD, ∀ x,
        out (addr a row pre mid post (is.foldl (Weighted.leafAt weight inv) x)) = word (addr a row pre mid post x) := by
    induction is with
    | nil =>
      intro u S word initial
      exact ⟨u,S,word,1,rfl,le_rfl,Exec.act _ _,initial,by intros; rfl⟩
    | cons i is ih =>
      intro u S word initial
      have top := order ⟨0,by simp⟩
      have atHead : i.val = is.length := by simpa using top
      have tailOrder (j : Fin is.length) : (is.get j).val+j.val+1 = is.length := by
        have h := order j.succ
        simp only [List.get_eq_getElem,List.getElem_cons_succ,Fin.val_succ,List.length_cons] at h
        simpa only [List.get_eq_getElem] using (show is[j.val].val+j.val+1 = is.length by omega)
      obtain ⟨y,E,next,k,hy,hk,first,prepared,action⟩ := step i u S word (by simpa [atHead] using initial)
      obtain ⟨z,D,out,n,hz,hn,rest,done,tail⟩ := ih tailOrder y E next (atHead ▸ prepared)
      refine ⟨z,D,out,k+n,hz.trans hy,by simp only [List.map_cons,List.sum_cons]; omega,
        Exec.seq first rest,done,?_⟩
      intro a ha row hr pre hp mid hm post he x
      apply (tail a ha row hr pre hp mid hm post he (Weighted.leafAt weight inv x i)).trans
      have pair := leafPair_apply v width q w radix i (fun z => (weight i*z.2,inv i*z.1)) word next
        x.1 x.2 a row pre mid post hp hm he (action a ha row hr)
      simpa only [addr,Weighted.leafAt,Weighted.leaf_word _ _ (unit i)] using pair
  intro u S word initial
  let coords := (List.finRange r).reverse
  have len : coords.length = r := by simp [coords]
  have order (j : Fin coords.length) : (coords.get j).val+j.val+1 = coords.length := by
    simp [coords,List.get_eq_getElem,List.getElem_reverse]
    have := j.isLt
    omega
  obtain ⟨z,D,out,n,hz,hn,exec,done,action⟩ := run coords order u S word (len.symm ▸ initial)
  refine ⟨z,D,out,n,hz,by simpa [coords,List.map_reverse] using hn,exec,done,?_⟩
  intro a ha row hr pre hp mid hm post he x
  have effect := Weighted.fold_leafAt weight inv coords (by simpa [coords] using List.nodup_finRange r) (fun i _ => unit i) x
  have active (j : Fin r) : j ∈ coords := by simp [coords]
  simpa only [effect,Weighted.child,active,Fin.isLt,ite_true] using action a ha row hr pre hp mid hm post he x

end IntegerMultBounds.MathlibTM2.Cover.Fallback
