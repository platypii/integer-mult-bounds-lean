module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps
import IntegerMultBounds.Machine.RecursiveHeaderBounds
import IntegerMultBounds.MathlibTM2.Cover.FallbackPrefixVolume
public import IntegerMultBounds.MathlibTM2.Cover.FallbackPairWeights
public import IntegerMultBounds.MathlibTM2.Cover.FallbackMiddleSwap
public import IntegerMultBounds.MathlibTM2.Cover.FallbackLeafSignRun

/-! Run the weighted leaf word on the shared caller payload. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open M8.RevMachine RecursiveInterchangeLayout SharedBankStageInput
variable {T P M G B : ℕ} {F U : Type}

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
      (_pairOff : ∀ i j, j ∈ [0,4,12] → sim i ≠ pair j) (_dimsOff : ∀ i j, sim i ≠ dims j) (slot : Fin block.tapes) (_leading : slot.val = io.val)
      (capacity : 217 ≤ block.states),
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

theorem packedWeightedLeaf_exec [M8.Machine.Net] {m d : ℕ} (v : Descriptor) (positive : v.Positive)
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
      (_pairScratch : ∀ k : Fin 13, (3 ≤ k ∧ k < 10) ∨ k = 12 → ∀ a ∈ [0,14,12], r k ≠ pair a)
      (_fieldPair : ∀ k ∈ leafDimensionFields, ∀ a ∈ [0,14,12], dst k ≠ pair a)
      (_pairOff : ∀ i j, j ∈ [0,4,12,14] → sim i ≠ pair j) (_dimsOff : ∀ i j, sim i ≠ dims j) (slot : Fin block.tapes) (_leading : slot.val = io.val)
      (capacity : 217 ≤ block.states),
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
        (∀ a : Fin 20, (a ≤ 14 ∧ a ≠ 4) ∨ a = 17 → S.R ((pair a).castAdd 31) = []) →
        S.R ((pair 15).castAdd 31) = binSyms M.size (1 : ZMod M).val →
        (S.R ((pair 16).castAdd 31)).length = w →
        ∀ (pivotTail parentTail : List (Fin (prime+4))),
        S.R ((pair 18).castAdd 31) = (List.ofFn fun k => binSyms M.size (pivot k).val).flatten ++ pivotTail →
        S.R ((pair 19).castAdd 31) = (List.ofFn fun k => binSyms M.size (parent k).val).flatten ++ parentTail →
        RepT (raw (CommonBank.bank roles (Routines.hdr v) f p node scalar ctr st) block.tapes) (S.L ∘ ports) (S.R ∘ ports) →
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
          Exec body ((signedChildPair prime j.val i.val coeff true).seq
            (call.seq (Mult.ShortConv.clearWords [coeff 0,coeff 14,coeff 12]))) (mk u S) n (mk z D) ∧
          output S D := by
  intro M weight inv P G B size c word head input block K sim pair r gap tail dst rowSlots gapSlot tailSlot fieldsOff scratchOff pairKeep radixPort other dims pairScratch fieldPair pairOff dimsOff slot leading capacity src ports shear prog lastProg work stage result y xs len signWord signSrc load bank child sign output body u S push hp hl hsign hb free fieldEmpty empty modulus fresh one clock pivotTail parentTail record weights initial rr setup leaf fields headers readFields call coeff coefficientRate
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
    (weightedLeafCost (volume prime v) v.width block.tapes push) (output S) weights record modulus one clock fresh (by
      intro y E hy unit hL modWord invWord negWord keep
      obtain ⟨z,D,t,hz,ht,run,rep,read,addr,clean,frame⟩ := weightedLeaf_exec v positive w width
        (show prime^v.width = M by rw [width]) weight inv unit io roles f p node scalar ctr st word head input
        sim pair r gap tail dst rowSlots gapSlot tailSlot fieldsOff scratchOff pairKeep radixPort other
        (fun k a ha => pairOff k a (by simp at ha ⊢; rcases ha with h | h | h <;> simp [h]))
        dimsOff slot leading capacity body y E push hp hl hsign hb
        (fun k => ⟨(congrFun hL _).trans (free k).1,(keep _ (privateOff k)).trans (free k).2⟩)
        (fun k hk => (keep _ (distinct _ (fieldPair k hk))).trans (fieldEmpty k hk))
        (fun k hk => (keep _ (distinct _ (pairScratch k hk))).trans (empty k hk))
        modWord invWord negWord (fun k x => by
          change _ = readAt blank (E.L (ports k)) (E.R (ports k)) _; rw [hL,keep _ (outside k)]; exact initial k x)
      refine ⟨z,D,t,hz,ht,run,?_,?_,?_,addr,?_,?_⟩
      · intro k hk
        simp at hk
        rcases hk with rfl | rfl | rfl <;> exact (frame _ (fun k => pairOff k _ (by decide))).2
      · intro k x
        change _ = readAt blank (D.L (ports k)) (if ports k ∈ _ then [] else D.R (ports k)) _
        rw [if_neg (outside k)]
        exact rep k x
      · intro x
        change readAt blank _ (if ports slot ∈ _ then [] else D.R (ports slot)) _ = _
        rw [if_neg (outside slot)]
        exact read x
      · intro k
        simpa only [if_neg (privateOff k)] using clean k
      · intro k hk
        refine ⟨(frame k hk).1.trans (congrFun hL _),?_⟩
        change (if k.castAdd 31 ∈ [coeff 0,coeff 14,coeff 12] then [] else D.R _) = _
        split_ifs with mem
        · simp [coeff] at mem
          rcases mem with h | h | h <;> subst k <;> exact (fresh _ (by decide)).symm
        · exact (frame k hk).2.trans (keep _ mem))
  have charge := leafPairCharge w i.val j.val
  exact ⟨z,D,t,hz,by dsimp only at ht charge; dsimp only [coefficientRate,M]; omega,run,post⟩

end

end IntegerMultBounds.MathlibTM2.Cover.Fallback
