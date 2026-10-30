module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaKeyLayout

/-! Fixed-width symbol encoding commutes with the replica/key packet layout. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

/-- Replica-major order is the nested list of key packets in each replica. -/
theorem replicaKeyWords_blocks {α : Type*} {N K W : ℕ} (f : Fin N → Fin K → Fin W → α) :
    replicaKeyWords f =
      (List.ofFn fun r : Fin N => (List.ofFn fun k : Fin K => List.ofFn fun b : Fin W => f r k b).flatten).flatten :=
  keyReplicaWords_blocks (fun k r b => f r k b)

/-- Encoding each coefficient by a fixed-width word preserves packet boundaries.
No concrete index cases or numerical decoding bounds enter this identity. -/
theorem replicaKeyWords_encode {α β : Type*} {N K L w : ℕ}
    (f : Fin N → Fin K → Fin L → α) (encode : α → Fin w → β) :
    (replicaKeyWords f).flatMap (fun x => List.ofFn (encode x)) =
      replicaKeyWords (fun n k (z : Fin (L*w)) =>
        encode (f n k (finProdFinEquiv.symm z).1) (finProdFinEquiv.symm z).2) := by
  have hflatten (ys : List (List α)) :
      ys.flatten.flatMap (fun x => List.ofFn (encode x)) =
        (ys.map (fun zs => zs.flatMap (fun x => List.ofFn (encode x)))).flatten := by
    induction ys with
    | nil => simp
    | cons zs ys ih => simp [ih]
  have hword (g : Fin L → α) :
      (List.ofFn g).flatMap (fun x => List.ofFn (encode x)) =
        List.ofFn (fun z : Fin (L*w) => encode (g (finProdFinEquiv.symm z).1) (finProdFinEquiv.symm z).2) := by
    rw [ofFn_finProd (fun i j => encode (g i) j)]
    simp [List.flatMap_def,List.map_ofFn,Function.comp_def]
  rw [replicaKeyWords_blocks,replicaKeyWords_blocks,hflatten]
  simp only [List.map_ofFn,Function.comp_def]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext n
  rw [hflatten]
  simp only [List.map_ofFn,Function.comp_def]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext k
  exact hword (f n k)

/-- The same encoding law in complete-key order. -/
theorem keyReplicaWords_encode {α β : Type*} {N K L w : ℕ}
    (f : Fin N → Fin K → Fin L → α) (encode : α → Fin w → β) :
    (keyReplicaWords f).flatMap (fun x => List.ofFn (encode x)) =
      keyReplicaWords (fun n k (z : Fin (L*w)) =>
        encode (f n k (finProdFinEquiv.symm z).1) (finProdFinEquiv.symm z).2) :=
  replicaKeyWords_encode (fun k n b => f n k b) encode

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
