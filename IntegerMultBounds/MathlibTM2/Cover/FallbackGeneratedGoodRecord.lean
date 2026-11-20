module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodRecordRoundTrip
public import IntegerMultBounds.MathlibTM2.Cover.FallbackPackedConjugate

/-! Generate the conjugate from packed inputs before the good-record round trip. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open M8.RevMachine RecursiveInterchangeLayout Matrix Finset IntegerMultBounds.Swap.LowerTriangular
  IntegerMultBounds.Swap.Modular
local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨pow_ne_zero _ Networks.Shared50ModularControl.prime_prime.ne_zero⟩

open RingFormula in
theorem generatedGoodRecordRoundTrip_exec [M8.Machine.Net] {T m work Q fields H J W : ℕ} {F U : Type}
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
      (u : HS _ Q prime U) (whole : Stacks K prime),
      ∀ {depth : ℕ} (pool : Fin ((depth+1)*13) ↪ Fin K)
        (inputs : Leaf (Entry Bool m) → Fin 7 ↪ Fin K) (ports : Fin 14 ↪ Fin K),
      let mat := fun b : Bool => if b then reduce M proj else g
      let formula := fun i j : Fin m => numerator (matrixInput false) (matrixInput true) i j
      let formulaCost := Finset.univ.sup fun ij : Fin m × Fin m => time H (readTime H) (formula ij.1 ij.2)
      let generation := (m*(m*(formulaCost+4*H+4)+1)+1) + (m*(m*(8*(m*m*H)+48*H*H+166*H+88)+1)+1) + (2*(m*m*H)+2)
      (∀ i j, (formula i j).depth ≤ depth) →
      (∀ a i j, inputs a i ≠ pool j) → (∀ k j, j = 1 ∨ j = 13 → pool k ≠ ports j) →
      (∀ a i j, j = 1 ∨ j = 13 → inputs a i ≠ ports j) → ports 3 = inner (record 16) →
      ((∀ k ≤ depth, whole.R (frame pool k 2) = binSyms H M) ∧
        (∀ k ≤ depth, ∀ i : Fin 13, i ≠ 2 → whole.R (frame pool k i) = []) ∧
        (∀ a, leafReady (fun b _ => inputs b) mat H a (inputs a 3) whole.R) ∧
        whole.R (ports 0) = binSyms H (Ring.inverse g.det).val ∧ whole.R (ports 2) = binSyms H M ∧
        whole.R (ports 13) = [] ∧ ∀ k : Fin 14, k = 1 ∨ 4 ≤ k ∧ k < 12 → whole.R (ports k) = []) →
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
      whole.R (caller 44) = binSyms H (1 : ZMod M).val → (whole.R (caller 45)).length = w →
      whole.R (caller 55) = (List.ofFn fun i => binSyms H (parent i).val).flatten →
      (∀ i : Fin 24, i ≠ 16 → S.R (record i) = []) →
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
      let packed := (List.ofFn fun i => binSyms (A := prime) M.size (parent i).val).flatten
      let loading := ((6*(whole.R (caller 55)).length+6)+((10*H+12)+(m*(10*M.size+8*(H-M.size)+12)+1+
        (2*packed.length+2))))+((10*M.size+10)+(6*(whole.R (caller 45)).length+6))
      let conversion := (m*m)*(10*M.size+8*(H-M.size)+12)+1+(2*(matrixWords prime M.size G).length+2)
      ∃ z D t ys, z.user = u.user ∧ t ≤ generation + ((dimensionTime H 1 fields+(4*(fields*H+1)+6)+(10*J+12)+(6*(M^fields).size+6)) +
        (loading+(conversion+(budget+2*((218*N+1)*13+6)+3)))) ∧
        Exec body ((packedConjugate pool inputs ports false true).seq ((recordCounterSetup caller fields).seq ((recordInputProgram record m).seq ((recordMatrixProgram record m).seq ((.act (pushMarkers marks) : Pr F K Q prime U).seq
          ((transfer r).seq ((embProg inner Empty.elim coordinate).seq (transfer reverse)))))))) (mk u whole) t (mk z D) ∧
        effect ys ∧ (∀ k, readAt blank (D.L (r 0)) (D.R (r 0)) (k-head) =
          RadixToBinary.binaryEncoding.encode (putWord source head (ys.map SparseRoleCircuit.encode) k)) ∧
        ∀ j : Fin 58, j ≠ 24 → let port := caller (j.castAdd 8)
          D.L port = whole.L port ∧ D.R port = whole.R port := by
  intro d common host M N entry leave record bank g G rep clean logical addr inner caller K ef xf eqs xqs word
    body u whole depth pool inputs ports mat formula formulaCost generation depthFits apart poolFree srcFree output ready slot r S base unit trailing spare input blank initial free empty good
    one ticks archive scratch call cost budget coordinate effect reverse transfer marks packed loading conversion

  let out := inner (record 16)
  have gen := packedConjugate_writes body pool inputs apart mat false true H hm ports poolFree srcFree
    depthFits u whole (by simpa [mat] using ready)
  obtain ⟨y,n,hy,hn,write⟩ := gen
  let B : Stacks K prime := {whole with R := Function.update whole.R out (matrixWords prime H G ++ whole.R out)}
  have runWriter : Exec body (packedConjugate pool inputs ports false true) (mk u whole) n (mk y B) := by
    simpa only [output,mat,B,out,G,Bool.false_eq_true,ite_false,ite_true] using write
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
  obtain ⟨z,D,t,ys,hz,ht,run,act,read,frame⟩ := goodRecordRoundTrip_exec
    v positive w proj width idem factor hd label live rankFits parent parentInv reciprocal io roles f p node scalar
    arity st freeNode hm hw hW length capacity source head fits cap ef xf eqs xqs word body y B (whole.R out)
    ((preserved 2).trans base) ((preserved 28).trans unit) ((preserved 53).trans trailing)
    (fun i hi => ⟨(spare i hi).1,(preserved i).trans (spare i hi).2⟩)
    (by intro z; change readAt _ (whole.L (r 0)) (B.R (r 0)) _ = _; rw [first,preserved]; simpa only [first] using input z)
    (by intro z; change readAt _ (whole.L (r 1)) (B.R (r 1)) _ = _; rw [← shared,privateKept _ (Or.inl (LeafCore.roleSlot io).isLt)]; simpa only [← shared] using blank z)
    (by intro k x
        change _ = readAt _ _ (B.R (inner (((k.castAdd 24).castAdd 31).castAdd work))) _
        rw [privateKept _ (Or.inl k.isLt)]
        exact initial k x)
    (by intro k x
        change readAt _ _ (B.R (inner (k.natAdd (host+31)))) _ = _
        rw [privateKept _ (Or.inr (by simp; omega))]
        exact free k x)
    (fun k => ⟨(empty k).1,(privateKept ((k.natAdd host).castAdd work) (Or.inr (by simp))).trans (empty k).2⟩)
    good (by change B.R out = _; simp [B,G,g,M])
    ((preserved 44).trans one) ((congrArg List.length (preserved 45)).trans ticks)
    ((preserved 55).trans archive)
    (by intro i hi
        exact (Function.update_of_ne (inner.injective.ne (record.injective.ne hi)) _ _).trans (scratch i hi))
  refine ⟨z,D,_,ys,hz.trans hy,Nat.add_le_add hn ?_,Exec.seq runWriter run,act,read,?_⟩
  · rw [show B.R ((Fin.castAddEmb (CommonBank.count T+24+31+work)) 55) = whole.R (caller 55) from preserved 55,
      show B.R ((Fin.castAddEmb (CommonBank.count T+24+31+work)) 45) = whole.R (caller 45) from preserved 45] at ht
    exact ht
  · intro j ne
    exact ⟨(frame j ne).1,(frame j ne).2.trans (preserved _)⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
