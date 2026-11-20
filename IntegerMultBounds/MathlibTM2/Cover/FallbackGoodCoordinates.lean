module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackCoordinateFrame

/-! Run the coordinate loop on elimination's packed pivots and original parent archive. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open M8.RevMachine RecursiveInterchangeLayout Matrix Finset IntegerMultBounds.Swap.LowerTriangular
  IntegerMultBounds.Swap.Modular
local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨pow_ne_zero _ Networks.Shared50ModularControl.prime_prime.ne_zero⟩

theorem goodRecordCoordinates_exec [M8.Machine.Net] {T m work Q : ℕ} {F U : Type}
    (v : Descriptor) (positive : v.Positive) (w : ℕ) (proj : Matrix (Fin m) (Fin m) ℚ)
    (width : v.width = proj.rank*(w+1)) (idem : proj*proj = proj)
    (factor : Factorization univ univ proj) (hd : ∀ a ∈ factorizationDenominators factor, a < prime)
    (label : ℕ) (live : LabelStock.live m (w+1) 1 label = true)
    (rankFits : proj.rank ≤ m) (parent parentInv : Fin m → ZMod (prime^(w+1)))
    (reciprocal : ∀ i, parent i * parentInv i = 1)
    (io : Fin T) (roles : Tapes T prime)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime)
    (arity : ℕ) (st : Tapes 2 prime) (freeNode : Family.NodeFree node)
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
    ∀ (ef : entry.tapes ≤ common+work) (xf : leave.tapes ≤ common+work)
      (eqs : entry.states ≤ Q) (xqs : leave.states ≤ Q) (word : Fin N → ZMod 2) (body : F → Pr F ((host+31)+work) Q prime U)
      (u : HS _ Q prime U) (S : Stacks _ prime) (tail parentTail : List (Fin (prime+4))),
      rep d (payload word) S → clean S →
      (∀ k : Fin 31, S.L ((k.natAdd host).castAdd work) = [] ∧ S.R ((k.natAdd host).castAdd work) = []) →
      fallbackBit rankFits (reduce M proj) g = false →
      S.R (bank 15) = matrixWords prime M.size G ++ tail → S.R (bank 2) = binSyms M.size M →
      S.R (bank 20) = binSyms M.size (1 : ZMod M).val → (S.R (bank 22)).length = w →
      (∀ k : Fin 23, (k < 15 ∧ k ≠ 2) ∨ (17 ≤ k ∧ k ≤ 19) ∨ k = 21 → S.R (bank k) = []) →
      S.R (record 23) = (List.ofFn fun k => binSyms M.size (parent k).val).flatten ++ parentTail →
      let call := fun i : Fin d => packedCoordinateProgram (F := F) (U := U) io i.val i.val ef xf fits eqs xqs cap
      let cost := packedCoordinatesTime d N w (LeafCore.core io).tapes
        (packedLeafPush (F := Empty) (U := U) io Empty.elim) entry.tapes leave.tapes
      ∃ z D t, z.user = u.user ∧ t ≤ (d*(4*w+4+columnTime m prime w M.size)+1+
        (d*(8*(m*m*M.size)+14*M.size+22)+1))+cost ∧
        Exec body ((goodWeights prime d rankFits bank).seq (Prog.seqList ((List.finRange d).reverse.map call)))
          (mk u S) t (mk z D) ∧
        ∃ minor : ∀ k (hk : k < d), IsUnit (GoodForm.lead (k+1) (lt_of_lt_of_le hk rankFits) G).det,
        let stage := GoodForm.stageAt G d rankFits minor d le_rfl
        let pivot := fun i : Fin d => stage.M (i.castLE rankFits) (i.castLE rankFits)
        let weight := fun i : Fin d => parent (i.castLE rankFits)*pivot i
        let inv := fun i : Fin d => parentInv (i.castLE rankFits)*Ring.inverse (pivot i)
        ∃ next : Fin N → ZMod 2, rep 0 (payload next) D ∧ clean D ∧
          (∀ k : Fin 31, D.L ((k.natAdd host).castAdd work) = [] ∧ D.R ((k.natAdd host).castAdd work) = []) ∧
          (∀ x, let slot := (((LeafCore.roleSlot io).castAdd 24).castAdd 31).castAdd work
                readAt blank (D.L slot) (D.R slot) x = leafBitTape (List.ofFn next) x) ∧
          (D.R (stageBank bank d 15), D.R (stageBank bank d 16)) =
            matrixArchive (fun k => if hk : k ≤ d then matrixWords prime M.size
              (GoodForm.stageAt G d rankFits minor k hk).M else []) (S.R (bank 15)) (S.R (bank 16)) d ∧
          ∀ a < v.beforeRows, ∀ row < v.rows, ∀ pre < v.beforeH, ∀ mid < v.between, ∀ post < v.afterD, ∀ x,
            ext next (addr a row pre mid post (Weighted.child d weight inv x)) = ext word (addr a row pre mid post x) := by
  intro d common host M N entry leave record bank g G rep clean payload logical addr ef xf eqs xqs word body u S tail parentTail initial freeWork empty good matrix modulus one ticks scratch archive call cost
  apply withGoodRecordWeights_exec body record proj idem factor hd rankFits label M.size
    (Nat.lt_size_self _) live parent parentInv reciprocal u S tail parentTail _ cost _ good matrix modulus one ticks scratch archive
  intro minor y E stage pivot units inputs spare matrixPair left frame
  have outside (k : Fin ((host+31)+work)) (h : k.val < common ∨ host ≤ k.val) : E.R k = S.R k := by
    apply frame
    intro j eq
    have atSlot := congrArg Fin.val eq
    change common+j.val = k.val at atSlot
    have := j.isLt
    dsimp only [host] at h
    omega
  have initialE : rep d (payload word) E := by
    intro k x
    change _ = readAt blank (E.L _) (E.R (((k.castAdd 24).castAdd 31).castAdd work)) _
    rw [left,outside _ (Or.inl k.isLt)]
    exact initial k x
  have cleanE : clean E := by
    intro k x
    rw [left,outside _ (Or.inr (by simp; omega))]
    exact freeWork k x
  have emptyE (k : Fin 31) : E.L ((k.natAdd host).castAdd work) = [] ∧ E.R ((k.natAdd host).castAdd work) = [] := by
    rw [left,outside _ (Or.inr (by simp))]
    exact empty k
  obtain ⟨next,z,D,t,user,time,run,out,free,kept,address⟩ := packedCoordinates_exec v positive w width
    rankFits parent parentInv reciprocal pivot units io roles f p node scalar arity st freeNode fits cap
    ef xf eqs xqs word body y E [] parentTail initialE cleanE emptyE spare inputs
  have stageKept (k : Fin 23) : D.R (stageBank bank d k) = E.R (stageBank bank d k) := by
    obtain ⟨j,eq⟩ := stageBank_slot bank d k
    rw [eq]
    exact (kept ((j.castLE (by decide : 23 ≤ 24)).castAdd 31)).2
  have emptyD (k : Fin 31) : D.L ((k.natAdd host).castAdd work) = [] ∧ D.R ((k.natAdd host).castAdd work) = [] := by
    have h := kept (k.natAdd 24)
    have eq : ((k.natAdd 24).natAdd common : Fin (common+55)) = k.natAdd host := by
      apply Fin.ext
      simp [host,Nat.add_assoc]
    rw [eq] at h
    exact ⟨h.1.trans (emptyE k).1,h.2.trans (emptyE k).2⟩
  refine ⟨z,D,t,user,time,run,minor,next,out,free,emptyD,?_,by rwa [stageKept,stageKept],address⟩
  intro x
  have view := LeafCore.bank_role (payload next) (Routines.hdr v) f p node scalar
    (Family.leafC (w+1) arity d 0) st io
  have h := out (LeafCore.roleSlot io) x
  rw [view.1, view.2] at h
  simpa [payload, SharedPlacementAlphabet.setTape] using h.symm

end IntegerMultBounds.MathlibTM2.Cover.Fallback
