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
      (u : HS _ Q prime U) (whole : Stacks K prime) (tail parentTail : List (Fin (prime+4))),
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
      S.R (bank 15) = matrixWords prime M.size G ++ tail → S.R (bank 2) = binSyms M.size M →
      S.R (bank 20) = binSyms M.size (1 : ZMod M).val → (S.R (bank 22)).length = w →
      (∀ k : Fin 23, (k < 15 ∧ k ≠ 2) ∨ (17 ≤ k ∧ k ≤ 19) ∨ k = 21 → S.R (bank k) = []) →
      S.R (record 23) = (List.ofFn fun k => binSyms M.size (parent k).val).flatten ++ parentTail →
      let call := fun i : Fin d => packedCoordinateProgram (F := Empty) (U := U) io i.val i.val ef xf fits eqs xqs cap
      let cost := packedCoordinatesTime d N w (LeafCore.core io).tapes
        (packedLeafPush (F := Empty) (U := U) io Empty.elim) entry.tapes leave.tapes
      let budget := (d*(4*w+4+columnTime m prime w M.size)+1+(d*(8*(m*m*M.size)+14*M.size+22)+1))+cost
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
      ∃ z D t ys, z.user = u.user ∧ t ≤ (dimensionTime H 1 fields+(4*(fields*H+1)+6)+(10*J+12)+(6*(M^fields).size+6)) +
        (budget+2*((218*N+1)*13+6)+3) ∧
        Exec body ((recordCounterSetup caller fields).seq ((.act (pushMarkers marks) : Pr F K Q prime U).seq
          ((transfer r).seq ((embProg inner Empty.elim coordinate).seq (transfer reverse))))) (mk u whole) t (mk z D) ∧
        effect ys ∧ ∀ k, readAt blank (D.L (r 0)) (D.R (r 0)) (k-head) =
          RadixToBinary.binaryEncoding.encode (putWord source head (ys.map SparseRoleCircuit.encode) k) := by
  intro d common host M N entry leave record bank g G rep clean logical addr inner caller K ef xf eqs xqs word
    body u whole tail parentTail slot r S base unit trailing spare input blank initial free empty good matrix modulus
    one ticks scratch archive call cost budget coordinate effect reverse transfer marks
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
  have transferRun := stagedLeafRoundTrip_exec pos pos hW capacity body r (embProg inner Empty.elim coordinate)
    a A source head (List.ofFn word) (List.length_ofFn.trans length) effect budget
    (by rw [first,left,off _ (caller.injective.ne (by decide)) (caller.injective.ne (by decide))
          (caller.injective.ne (by decide))]; simpa only [first] using input)
    (by rw [← shared,left,kept]; simpa only [← shared] using blank)
    (by intro i; rw [port]; exact raw i)
  suffices process : _ by
    obtain ⟨z,D,t,ys,hz,ht,run,act,read⟩ := transferRun process
    exact ⟨z,D,_,ys,hz.trans ha,Nat.add_le_add hc (by simpa only [← volumeEq] using ht),Exec.seq setup run,act,read⟩
  apply stagedCoordinateChild_exec body inner r slot shared (recordRoundTripPorts_apart slot) coordinate A
    (List.ofFn word) effect budget
  intro y E read frame
  have original (i) (ne : i ≠ slot) := And.intro ((frame i ne).1.trans (congrFun left _)) ((frame i ne).2.trans (kept i))
  obtain ⟨z,D,t,user,time,exec,minor,next,_,_,_,out,_,action⟩ := stagedGoodRecordCoordinates_exec
    v positive w proj width idem factor hd label live rankFits parent parentInv reciprocal io roles f p node scalar
    arity st freeNode fits cap ef xf eqs xqs word Empty.elim y S E tail parentTail initial original read free empty
    good matrix modulus one ticks scratch archive
  exact ⟨z,D,t,List.ofFn next,user,time,exec,by simp [N],⟨minor,next,rfl,action⟩,out⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
