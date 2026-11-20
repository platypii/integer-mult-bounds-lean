module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodCoordinates
public import IntegerMultBounds.MathlibTM2.Cover.FallbackLeafReturnHeaders

/-! Return the weighted good-record output at the caller’s saved head. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open M8.RevMachine RecursiveInterchangeLayout Matrix Finset IntegerMultBounds.Swap.LowerTriangular
  IntegerMultBounds.Swap.Modular
local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨pow_ne_zero _ Networks.Shared50ModularControl.prime_prime.ne_zero⟩

theorem goodRecordReturn_exec [M8.Machine.Net] {T m work Q : ℕ} {F U : Type}
    (v : Descriptor) (positive : v.Positive) (w : ℕ) (proj : Matrix (Fin m) (Fin m) ℚ)
    (width : v.width = proj.rank*(w+1)) (idem : proj*proj = proj)
    (factor : Factorization univ univ proj) (hd : ∀ a ∈ factorizationDenominators factor, a < prime)
    (label : ℕ) (live : LabelStock.live m (w+1) 1 label = true)
    (rankFits : proj.rank ≤ m) (parent parentInv : Fin m → ZMod (prime^(w+1)))
    (reciprocal : ∀ i, parent i * parentInv i = 1)
    (io : Fin T) (roles : Tapes T prime)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime)
    (arity : ℕ) (st : Tapes 2 prime) (freeNode : Family.NodeFree node)
    {P H B : ℕ} (hP : 0 < P) (hH : 0 < H) (hB : 0 < B) (length : volume prime v = P*(H*B))
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
    let payload := fun x : Fin N → ZMod 2 => SharedPlacementAlphabet.setTape roles io (leafBitTape (List.ofFn x)) 0
    let logical := {v with width := d}
    let addr := fun a row pre mid post (x : IntegerMultBounds.Swap.Shear.State (Fin d) (ZMod M)) =>
      index M logical a row pre (FlatCoordinateLayout.rank x.1).val mid (FlatCoordinateLayout.rank x.2).val post
    let K := (host+31)+work
    let inner := Fin.natAddEmb 13 (m := K)
    let outer := Fin.castAddEmb (n := 13) K
    let slot := (((LeafCore.roleSlot io).castAdd 24).castAdd 31).castAdd work
    ∀ (ef : entry.tapes ≤ common+work) (xf : leave.tapes ≤ common+work)
      (eqs : entry.states ≤ Q) (xqs : leave.states ≤ Q) (word : Fin N → ZMod 2) (body : F → Pr F (13+K) Q prime U)
      (u : HS _ Q prime U) (whole : Stacks (13+K) prime) (tail parentTail : List (Fin (prime+4))),
      let S := embStk inner whole
      rep d (payload word) S → clean S →
      (∀ k : Fin 31, S.L ((k.natAdd host).castAdd work) = [] ∧ S.R ((k.natAdd host).castAdd work) = []) →
      fallbackBit rankFits (reduce M proj) g = false →
      S.R (bank 15) = matrixWords prime M.size G ++ tail → S.R (bank 2) = binSyms M.size M →
      S.R (bank 20) = binSyms M.size (1 : ZMod M).val → (S.R (bank 22)).length = w →
      (∀ k : Fin 23, (k < 15 ∧ k ≠ 2) ∨ (17 ≤ k ∧ k ≤ 19) ∨ k = 21 → S.R (bank k) = []) →
      S.R (record 23) = (List.ofFn fun k => binSyms M.size (parent k).val).flatten ++ parentTail →
      (∀ z, readAt blank (whole.L (outer 1)) (whole.R (outer 1)) (z-head) = RadixToBinary.binaryEncoding.encode (source z)) →
      (∀ i : Fin 3, whole.R (outer (i.natAdd 10)) = ![binSyms B.size B,binSyms H.size H,binSyms P.size P] i) →
      (∀ i : Fin 10, 2 ≤ i.val → whole.L (outer (i.castAdd 3)) = [] ∧ whole.R (outer (i.castAdd 3)) = []) →
      let call := fun i : Fin d => packedCoordinateProgram (F := Empty) (U := U) io i.val i.val ef xf fits eqs xqs cap
      let cost := packedCoordinatesTime d N w (LeafCore.core io).tapes
        (packedLeafPush (F := Empty) (U := U) io Empty.elim) entry.tapes leave.tapes
      let r := ((Fin.castAddEmb (n := 10) 3).trans outer).trans (Equiv.swap (outer 0) (inner slot)).toEmbedding
      let header := fun i : Fin 3 => outer (i.natAdd 10)
      let setup := Record.copyLeafHeaders header (returnHeaderTargets.trans r) (r 8) (r 9) (List.finRange 3)
      let localRun : Pr Empty 8 217 prime U := (.act (pushMarkers [2,3,4,5,6,7]) : Pr Empty 8 217 prime U).seq
        (returnFromOrigin (Function.Embedding.refl _))
      let finish := setup.seq (statePlacedNormalized ((Fin.castAddEmb 2).trans r) capacity (by decide) Empty.elim localRun)
      let coordinate := (goodWeights prime d rankFits bank).seq (Prog.seqList ((List.finRange d).reverse.map call))
      ∃ z D t, z.user = u.user ∧ t ≤ ((d*(4*w+4+columnTime m prime w M.size)+1+
        (d*(8*(m*m*M.size)+14*M.size+22)+1))+cost)+(6*(B.size+H.size+P.size)+19+((218*N+1)*13+8)) ∧
        Exec body ((embProg inner Empty.elim coordinate).seq finish) (mk u whole) t (mk z D) ∧
        ∃ minor : ∀ k (hk : k < d), IsUnit (GoodForm.lead (k+1) (lt_of_lt_of_le hk rankFits) G).det,
        let stage := GoodForm.stageAt G d rankFits minor d le_rfl
        let pivot := fun i : Fin d => stage.M (i.castLE rankFits) (i.castLE rankFits)
        let weight := fun i : Fin d => parent (i.castLE rankFits)*pivot i
        let inv := fun i : Fin d => parentInv (i.castLE rankFits)*Ring.inverse (pivot i)
        ∃ next : Fin N → ZMod 2, (∀ z, readAt blank (D.L (outer 1)) (D.R (outer 1)) (z-head) =
          RadixToBinary.binaryEncoding.encode (putWord source head ((List.ofFn next).map SparseRoleCircuit.encode) z)) ∧
          (∀ i, D.L (header i) = whole.L (header i) ∧ D.R (header i) = whole.R (header i)) ∧
          (∀ a < v.beforeRows, ∀ row < v.rows, ∀ pre < v.beforeH, ∀ mid < v.between, ∀ post < v.afterD, ∀ x,
            ext next (addr a row pre mid post (Weighted.child d weight inv x)) = ext word (addr a row pre mid post x)) ∧
          ∀ gaps W, logical = goodChildDescriptor M d gaps W →
            ∀ (hg tg : Fin gaps → ZMod M) x (j : Fin W),
            let flat := fun y => let fields := childFields hg tg y
                                 (FlatCoordinateLayout.index (Fin.append fields.1 fields.2) j).val
            readAt blank (D.L (outer 1)) (D.R (outer 1)) (flat (Weighted.child d weight inv x)) =
              RadixToBinary.binaryEncoding.encode (SparseRoleCircuit.encode (ext word (flat x))) := by
  intro d common host M N entry leave record bank g G rep clean payload logical addr K inner outer slot
    ef xf eqs xqs word body u whole tail parentTail S initial free empty good matrix modulus one ticks scratch archive
    src words spare call cost r header setup localRun finish coordinate
  obtain ⟨y,E,t,user,time,run,minor,next,_,_,_,read,_,address⟩ := goodRecordCoordinates_exec v positive w proj
    width idem factor hd label live rankFits parent parentInv reciprocal io roles f p node scalar arity st freeNode
    fits cap ef xf eqs xqs word (F := Empty) Empty.elim (embDn inner u) S tail parentTail initial free empty good
    matrix modulus one ticks scratch archive
  obtain ⟨z,D,n,hz,bound,done,out,kept⟩ := coordinateReturn_exec hP hH hB capacity body slot coordinate u whole
    source head (List.ofFn next) (List.length_ofFn.trans length) y E t run user read src words spare
  refine ⟨z,D,n,hz,bound.trans ?_,done,minor,next,out,kept,address,?_⟩
  · rw [← length]
    exact Nat.add_le_add_right time _
  · intro gaps W layout hg tg x j flat
    let stage := GoodForm.stageAt G d rankFits minor d le_rfl
    let pivot := fun i : Fin d => stage.M (i.castLE rankFits) (i.castLE rankFits)
    let y := Weighted.child d (fun i => parent (i.castLE rankFits)*pivot i)
      (fun i => parentInv (i.castLE rankFits)*Ring.inverse (pivot i)) x
    have shape : volume M logical = N := by
      simp [N,logical,volume,width,M,d,pow_mul,Nat.mul_comm proj.rank (w+1)]
    have inside : flat y < N := by
      rw [← shape,layout,goodChildVolume]
      exact (FlatCoordinateLayout.index (Fin.append (childFields hg tg y).1 (childFields hg tg y).2) j).isLt
    have coord (u) : flat u = addr 0 0 0 (FlatCoordinateLayout.rank (Fin.append hg tg)).val j.val u := by
      dsimp only [addr]
      rw [layout]
      exact goodChildIndex hg tg u j
    have dims := congrArg (fun v : Descriptor => (v.beforeRows,v.rows,v.beforeH,v.between,v.afterD)) layout
    have mid := (FlatCoordinateLayout.rank (Fin.append hg tg)).isLt
    simp only [logical,goodChildDescriptor,Prod.mk.injEq] at dims
    obtain ⟨_,_,_,hm,he⟩ := dims
    have act := address 0 positive.1 0 positive.2.1 0 positive.2.2.1 _ (by rw [hm]; exact mid) j.val (by rw [he]; exact j.isLt) x
    change ext next (addr _ _ _ _ _ y) = ext word (addr _ _ _ _ _ x) at act
    rw [← coord,← coord] at act
    have read := out (head+(flat y : ℤ))
    rw [add_sub_cancel_left,WordSegments.get source head _ (flat y) (by simpa using inside)] at read
    simp only [List.getElem_map,List.getElem_ofFn] at read
    have valid : flat y < volume prime v := inside
    simp only [M8.RevMachine.ext,dite_eq_left valid] at act
    exact
      read.trans (congrArg (fun b => RadixToBinary.binaryEncoding.encode (SparseRoleCircuit.encode b)) act)

end IntegerMultBounds.MathlibTM2.Cover.Fallback
