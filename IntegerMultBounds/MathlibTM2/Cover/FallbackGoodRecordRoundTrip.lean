module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodCoordinates

/-! Stage the caller word, run the weighted coordinate loop, and return the result. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open M8.RevMachine RecursiveInterchangeLayout Matrix Finset IntegerMultBounds.Swap.LowerTriangular
  IntegerMultBounds.Swap.Modular
local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨pow_ne_zero _ Networks.Shared50ModularControl.prime_prime.ne_zero⟩

theorem goodRecordRoundTrip_exec [M8.Machine.Net] {T m work Q K P H B : ℕ} {F U : Type}
    (v : Descriptor) (positive : v.Positive) (w : ℕ) (proj : Matrix (Fin m) (Fin m) ℚ)
    (width : v.width = proj.rank*(w+1)) (idem : proj*proj = proj)
    (factor : Factorization univ univ proj) (hd : ∀ a ∈ factorizationDenominators factor, a < prime)
    (label : ℕ) (live : LabelStock.live m (w+1) 1 label = true)
    (rankFits : proj.rank ≤ m) (parent parentInv : Fin m → ZMod (prime^(w+1)))
    (reciprocal : ∀ i, parent i * parentInv i = 1)
    (io : Fin T) (roles : Tapes T prime)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime)
    (arity : ℕ) (st : Tapes 2 prime) (freeNode : Family.NodeFree node)
    (hP : 0 < P) (hH : 0 < H) (hB : 0 < B) (length : volume prime v = P*(H*B))
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
    ∀ (ef : entry.tapes ≤ common+work) (xf : leave.tapes ≤ common+work)
      (eqs : entry.states ≤ Q) (xqs : leave.states ≤ Q) (word : Fin N → ZMod 2) (body : F → Pr F K Q prime U)
      (inner : Fin ((host+31)+work) ↪ Fin K) (r : Fin 8 ↪ Fin K)
      (u : HS _ Q prime U) (whole : Stacks K prime) (tail parentTail : List (Fin (prime+4))),
      let slot := (((LeafCore.roleSlot io).castAdd 24).castAdd 31).castAdd work
      let S := embStk inner whole
      inner slot = r 1 → (∀ i j, j ≠ 1 → inner i ≠ r j) →
      (∀ z, readAt blank (whole.L (r 0)) (whole.R (r 0)) (z-head) =
        RadixToBinary.binaryEncoding.encode (putWord source head ((List.ofFn word).map SparseRoleCircuit.encode) z)) →
      (∀ z, readAt blank (whole.L (r 1)) (whole.R (r 1)) z = blank) →
      (∀ i : Fin 6, whole.L (r (Fin.natAdd 2 i)) = [] ∧ whole.R (r (Fin.natAdd 2 i)) =
        ![[],binSyms B.size B,[],binSyms H.size H,[],binSyms P.size P] i) →
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
      ∃ z D t ys, z.user = u.user ∧ t ≤ budget+2*((218*N+1)*13+6)+3 ∧
        Exec body ((.act (pushMarkers marks) : Pr F K Q prime U).seq
          ((transfer r).seq ((embProg inner Empty.elim coordinate).seq (transfer reverse)))) (mk u whole) t (mk z D) ∧
        effect ys ∧ ∀ k, readAt blank (D.L (r 0)) (D.R (r 0)) (k-head) =
          RadixToBinary.binaryEncoding.encode (putWord source head (ys.map SparseRoleCircuit.encode) k) := by
  intro d common host M N entry leave record bank g G rep clean logical addr ef xf eqs xqs word body inner r
    u whole tail parentTail slot S shared apart input blank raw initial free empty good matrix modulus one ticks
    scratch archive call cost budget coordinate effect reverse transfer marks
  have run := stagedLeafRoundTrip_exec hP hH hB capacity body r (embProg inner Empty.elim coordinate)
    u whole source head (List.ofFn word) (List.length_ofFn.trans length) effect budget input blank raw
  apply (by simpa only [← length] using run : _ → _)
  apply stagedCoordinateChild_exec body inner r slot shared apart coordinate whole (List.ofFn word) effect budget
  intro y E read frame
  obtain ⟨z,D,t,user,time,exec,minor,next,_,_,_,out,_,action⟩ := stagedGoodRecordCoordinates_exec
    v positive w proj width idem factor hd label live rankFits parent parentInv reciprocal io roles f p node scalar
    arity st freeNode fits cap ef xf eqs xqs word Empty.elim y S E tail parentTail initial frame read free empty
    good matrix modulus one ticks scratch archive
  exact ⟨z,D,t,List.ofFn next,user,time,exec,by simp [N],⟨minor,next,rfl,action⟩,out⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
