module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaPublicationRead

/-! Packed replica reads inside ownership ignore an accumulated output bank's
borrowed suffix. No decoding or magnitude hypothesis is needed. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {A span L s origin : ℕ}

theorem publicationReplicas_read_suffix (windows : PublicationWindows span L) (q w : ℕ)
    (replicas : List (PublicationReplica A)) (hvalid : ∀ r ∈ replicas, r.Valid windows w 0)
    (tail : List (Fin (A+4))) (r : Fin replicas.length) (k : ZMod s)
    (hklo : origin ≤ k.val) (hkhi : k.val < origin+span) :
    packedIntervalRead q w origin
      (((replicas.flatMap (PublicationReplica.output windows w))++tail).drop (r.val*span*w)) k =
    packedIntervalRead q w origin
      ((replicas.flatMap (PublicationReplica.output windows w)).drop (r.val*span*w)) k := by
  have hfit : (k.val-origin)*w+w ≤ span*w := by
    have hh := Nat.mul_le_mul_right w (show k.val-origin+1 ≤ span by omega)
    simpa only [Nat.add_mul,Nat.one_mul] using hh
  have ht := flatMap_uniform_slice (PublicationReplica.output windows w) replicas (span*w)
    ((k.val-origin)*w) w (fun r hr => (hvalid r hr).output_length) r hfit tail
  have he := flatMap_uniform_slice (PublicationReplica.output windows w) replicas (span*w)
    ((k.val-origin)*w) w (fun r hr => (hvalid r hr).output_length) r hfit []
  have hh := ht.trans he.symm
  simp only [List.append_nil] at hh
  dsimp only [packedIntervalRead]
  simp only [List.drop_drop,Nat.mul_assoc]
  exact congrArg (fun ys => value q (decodeWord ys)) hh

theorem publicationReplicas_errorOn_suffix (windows : PublicationWindows span L) (q w : ℕ)
    (replicas : List (PublicationReplica A)) (hvalid : ∀ r ∈ replicas, r.Valid windows w 0)
    (tail : List (Fin (A+4))) (r : Fin replicas.length)
    (core : Finset (ZMod s)) (x : ZMod s → ℝ) (error : ℝ)
    (hcore : ∀ k ∈ core, origin ≤ k.val ∧ k.val < origin+span)
    (herror : PhaseCellInterface.ErrorOn core
      (fun k => (packedIntervalRead q w origin
        ((replicas.flatMap (PublicationReplica.output windows w)).drop (r.val*span*w)) k).re) x error) :
    PhaseCellInterface.ErrorOn core
      (fun k => (packedIntervalRead q w origin
        (((replicas.flatMap (PublicationReplica.output windows w))++tail).drop (r.val*span*w)) k).re) x error := by
  intro k hk
  dsimp only
  rw [publicationReplicas_read_suffix windows q w replicas hvalid tail r k (hcore k hk).1 (hcore k hk).2]
  exact herror k hk

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
