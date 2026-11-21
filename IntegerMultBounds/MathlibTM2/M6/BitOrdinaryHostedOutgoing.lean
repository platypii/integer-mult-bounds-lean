module

public import IntegerMultBounds.MathlibTM2.M6.BitOrdinaryDirectoryReplay

/-! Execute the outgoing directory pass on the saved scanner bank and the physical owner registers. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover Cover.Fallback Stack Host LabelTraversal
open Shared50ModularControl (prime)
local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

open GoodForm FlatCoordinateLayout Matrix M8.Exchange M8.ReversedExchange IntegerMultBounds.Swap.Shear
open IntegerMultBounds.Swap.Modular GoodChildLayout

theorem hostedOutgoingScan_exec [M8.Machine.Net] {P U : Type} {r g w W common work : ℕ}
    (v : RecursiveInterchangeLayout.Descriptor) :
    let m := r+g
    let hr := Nat.le_add_right r g
    let K := common+24+31+work
    let M := prime^(w+1)
    let N := M^(m+m)*W
    let V := RecursiveInterchangeLayout.volume prime (ordinaryChildDescriptor r g w W)
    ∀ (proj : Matrix (Fin m) (Fin m) ℚ) (_rank : proj.rank = r) (_dim : m = 64)
      (_idem : proj*proj = proj) (factor : IntegerMultBounds.Swap.LowerTriangular.Factorization Finset.univ Finset.univ proj)
      (_small : ∀ k ∈ factorizationDenominators factor, k < prime)
      (weights : Fin m → ZMod M) (_unit : ∀ i, IsUnit (weights i)) (_hW : 0 < W)
      (prefixes : ℕ → List (Fin (prime+4))) (archiveTail ownerTail : List (Fin (prime+4))) (R : ℕ)
      (pool : (RingFormula.conjugationDepth m+1)*13 ≤ work) (room : 58+(rowSwapBlock.tapes+35+1) ≤ K)
      (body : P → Pr P (66+K) columnCapacity prime U) {G : Type} {T : ℕ}
      (localBank : Fin (66+K) ↪ Fin T) (regs : Fin 5 ↪ Fin T) (apart : ∀ i j, localBank i ≠ regs j)
      (label : P → G) (host : G → Pr G T columnCapacity prime U)
      (a : HS T columnCapacity prime U) (A : Stacks T prime) (original : ℕ → Fin N → ZMod 2) (returned : ℕ → Fin V → ZMod 2) (c : ℕ),
    let rs := List.range R
    let full := ordinaryCaller (by omega : 58 ≤ K)
    let machine := GoodChildLayout.parent.trans (parentWithWeights.trans full)
    let caller := Fin.castAddEmb (n := 66) K
    let bank := fun i : Fin (66+K) => i.castAdd 5
    let place := outgoingOwnerPlacement localBank regs apart
    let start := embStk localBank A
    let ready := DirectoryReady v proj w W M.size W.size weights prefixes archiveTail (fun _ => [])
    let reduced := reduce M proj
    let live := LabelStock.live m (w+1) 1
    let bad := fun j => fallbackBit proj.rank_le_height reduced (physicalLabel m (w+1) j)
    let active := fun j => live j && !bad j
    let G := fun j => let label := physicalLabel m (w+1) j; label*reduced*label⁻¹
    let inv := fun i => Ring.inverse (weights i)
    let pos := ordinaryRecursivePosition r g w W
    let size := ordinaryChildVolume r g w W
    let prog := outgoingRowProgram (P := P) (U := U) (common := common) r g pool room
    let privateTapes := (List.finRange (66+K)).filter (fun i => 58 ≤ i.val)
    let slots : Fin 7 ↪ Fin 58 := ⟨![45,46,2,47,48,44,49],by decide⟩
    let scan := ((goodRecordScanPorts.trans slots).trans (Fin.castAddEmb 8)).trans caller
    let skip : Pr P (66+K) columnCapacity prime U := readWithSuccessorClock (scan 1) (advanceDirectory m scan)
    let dispatch := ownerDispatch (caller 57) (caller 56) ((prog.seq (clearWorkTapes privateTapes)).seq skip) skip skip
    let cost := fun j => let base := outgoingRowTime U machine r g w W (prefixes j).length
                         let cursor := 1+(4*(prefixes j).length+4+(m*m*(4*(w+1)+4)+1)+1)
                         (if active j then base+(4*privateTapes.length+1+privateTapes.length*(6*(c*base)))+cursor else cursor) +
                           (if live j then 4 else 3)
    let effect := fun j (word : Fin N → ZMod 2) => ∀ x k,
      let y := transform (diagonal weights) 1 (revExchangeOf (rev m) (G j) (transform (diagonal inv) 1 x))
      word (index (Fin.append y.1 y.2) k) = original j (index (Fin.append x.1 x.2) k)
    (∀ f, host (label f) = embProg place label (embProg bank id (body f))) →
    Fast.Main.mnProgPush prog ≤ c → (∀ f, Fast.Main.mnProgPush (body f) ≤ c) →
    (∀ j ∈ rs, live j = true → bad j = false →
      ∃ minor : ∀ i (hi : i < r), IsUnit (lead (i+1) (lt_of_lt_of_le hi hr) (G j)).det,
      ∃ before, IncomingRowEffect (w := w) (W := W) hr (G j) minor weights inv (original j) before ∧
        returned j = ordinaryChildOutput (r := r) (g := g) (w := w) before ∘ pos) →
    ready start rs → start.R (caller 57) = rs.map (fun j => bitSymbol (live j)) →
    start.R (caller 56) = rs.map (fun j => bitSymbol (bad j)) →
    A.R (regs 0) = rs.flatMap (fun j => payloadWord (SparseRoleCircuit.encode ∘ returned j)) ++ ownerTail →
    A.R (regs 1) = [] → (A.R (regs 2)).length = N → A.R (regs 3) = [] → A.R (regs 4) = [] →
    (∀ j, readAt blank (start.L (caller 24)) (start.R (caller 24)) j = blank) →
    ∀ (bypass : ℕ → (Fin N → ZMod 2) → Prop),
    (∀ j : Fin R, active j = false → ∃ word, bypass j word ∧ returned j = fun i => word (i.cast size)) →
    ∃ z F n, ∃ output : Fin (R*N) → ZMod 2, z.user = a.user ∧
      n ≤ (rs.map (fun j => 6*N+6+cost j+(4*N+4))).sum+2*rs.length+2+(2*(rs.length*N)+2) ∧
      Exec host (embProg place label (packedOwner (caller 24) (caller 57) dispatch)) (mk a A) n (mk z F) ∧
      (∀ j : Fin R, if active j then effect j (ownerRow rfl output j) else bypass j (ownerRow rfl output j)) ∧
      F.L (regs 0) = A.L (regs 0) ∧ F.R (regs 0) = payloadWord (SparseRoleCircuit.encode ∘ output) ++ ownerTail ∧ F.R (regs 1) = [] ∧
      (F.R (regs 2)).length = N ∧ F.R (regs 3) = [] ∧ F.R (regs 4) = [] ∧ ready (embStk localBank F) [] ∧
      F.R (localBank (caller 57)) = [] ∧ F.R (localBank (caller 56)) = [] ∧
      ∀ i, (∀ j, place j ≠ i) → F.L i = A.L i ∧ F.R i = A.R i := by
  intro m hr K M N V proj rank dim idem factor small weights unit hW prefixes archiveTail ownerTail R pool room body
    G T localBank regs apart label host a A original returned c rs full machine caller bank place start ready reduced live bad
    active matrices inv pos size prog privateTapes slots scan skip dispatch cost effect calls bounded localPush classified
    directory liveBits badBits queue acc width saved tmp blankPort bypass restored
  have project (B : Stacks T prime) : embStk bank (embStk place B) = embStk localBank B := by
    refine Stacks.ext rfl rfl (funext fun i => ?_) (funext fun i => ?_) <;>
      simp [embStk,place,bank]
  have regEq (j : Fin 5) : place (Fin.natAdd (66+(common+24+31+work)) j) = regs j :=
    outgoingOwnerPlacement_reg localBank regs apart j
  have bankEq (i : Fin (66+(common+24+31+work))) : place (i.castAdd 5) = localBank i :=
    outgoingOwnerPlacement_bank localBank regs apart i
  obtain ⟨y,B,n,out,user,time,run,action,left,right,empty,length,clear,free,done,ls,bs⟩ :=
    generatedOutgoingScan_exec (common := common) v proj rank dim idem factor small weights unit hW prefixes archiveTail
      ownerTail R pool room body (embDn place a) (embStk place A) original returned c bounded localPush classified
      (by rwa [project]) (by rwa [project]) (by rwa [project])
      (by simpa only [embStk,Function.comp_apply,regEq] using queue) (by simpa only [embStk,Function.comp_apply,regEq] using acc)
      (by simpa only [embStk,Function.comp_apply,regEq] using width) (by simpa only [embStk,Function.comp_apply,regEq] using saved)
      (by simpa only [embStk,Function.comp_apply,regEq] using tmp) (by rwa [project]) bypass restored
  obtain ⟨z,F,placed,_,same,physical,frame⟩ := exec_emb place.injective calls run a rfl A rfl
  subst B
  refine ⟨z,F,n,out,same.trans user,time,placed,action,?_,?_,?_,?_,?_,?_,?_,?_,?_,frame⟩
  · simpa only [embStk,Function.comp_apply,regEq] using left
  · simpa only [embStk,Function.comp_apply,regEq] using right
  · simpa only [embStk,Function.comp_apply,regEq] using empty
  · simpa only [embStk,Function.comp_apply,regEq] using length
  · simpa only [embStk,Function.comp_apply,regEq] using clear
  · simpa only [embStk,Function.comp_apply,regEq] using free
  · rwa [project] at done
  · simpa only [embStk,Function.comp_apply,bank,bankEq] using ls
  · simpa only [embStk,Function.comp_apply,bank,bankEq] using bs

end IntegerMultBounds.MathlibTM2.M6.BitNode
