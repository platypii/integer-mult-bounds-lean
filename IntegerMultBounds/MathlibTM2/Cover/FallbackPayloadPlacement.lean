module

public import IntegerMultBounds.MathlibTM2.Host.StatePlacement
public import IntegerMultBounds.MathlibTM2.Cover.FallbackShearReady
public import IntegerMultBounds.MathlibTM2.Cover.FallbackSignedOutput

/-! Place a child workspace beside its caller, sharing just the positioned payload tape. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
variable {T K Q Q' A : ℕ} {P U : Type}

def payloadPlacement (slot : Fin T) (payload : Fin K) : Fin T ↪ Fin (T+K) :=
  (Fin.castAddEmb K).trans (Equiv.swap (slot.castAdd K) (payload.natAdd T)).toEmbedding

theorem payloadPlacement_shared (slot : Fin T) (payload : Fin K) :
    payloadPlacement slot payload slot = payload.natAdd T := Equiv.swap_apply_left ..

private theorem payloadPlacement_off (slot : Fin T) (payload k : Fin K) (hk : k ≠ payload)
    (j : Fin T) : payloadPlacement slot payload j ≠ k.natAdd T := by
  by_cases same : j = slot
  · subst j
    rw [payloadPlacement_shared]
    exact (Fin.natAddEmb T).injective.ne hk.symm
  have apart (x : Fin K) : j.castAdd K ≠ x.natAdd T := by
    intro eq
    have := congrArg Fin.val eq
    simp at this
    omega
  have diff : j.castAdd K ≠ slot.castAdd K := (Fin.castAddEmb K).injective.ne same
  change Equiv.swap (slot.castAdd K) (payload.natAdd T) (j.castAdd K) ≠ _
  rw [Equiv.swap_apply_of_ne_of_ne diff (apart payload)]
  exact apart k

/-- The returned payload is the child's actual pair of stacks. Every other
caller tape retains both stacks, irrespective of the child's internal writes. -/
theorem payloadPlacement_exec (slot : Fin T) (payload : Fin K) (cap : Q ≤ Q') (pos : 0 < Q)
    (body : P → Pr P (T+K) Q' A U) (child : Pr Empty T Q A U)
    (v : HS (T+K) Q' A U) (S : Stacks (T+K) A) :
    let bank := payloadPlacement slot payload
    ∀ u D n, Exec Empty.elim child (mk (stateLiftDown pos (embDn bank v)) (embStk bank S)) n (mk u D) →
      ∃ z F, z.user = u.user ∧
        Exec body (statePlacedNormalized bank cap pos Empty.elim child) (mk v S) (1+n) (mk z F) ∧
        F.L (payload.natAdd T) = D.L slot ∧ F.R (payload.natAdd T) = D.R slot ∧
        ∀ k ≠ payload, F.L (k.natAdd T) = S.L (k.natAdd T) ∧ F.R (k.natAdd T) = S.R (k.natAdd T) := by
  intro bank u D n run
  obtain ⟨z,_,user,placed⟩ := statePlaced_exec_normalized bank bank.injective cap pos Empty.elim
    (body' := body) (fun e => nomatch e) v S run
  let F := embOvr bank D.get S
  have eq : embStk bank F = D := embStk_ovr bank.injective _ _
  have left := congrArg (fun X : Stacks T A => X.L slot) eq
  have right := congrArg (fun X : Stacks T A => X.R slot) eq
  change F.L (bank slot) = D.L slot at left
  change F.R (bank slot) = D.R slot at right
  rw [show bank slot = payload.natAdd T from payloadPlacement_shared ..] at left right
  exact ⟨z,F,user,placed,left,right,fun k hk => embOvr_off _ _ (payloadPlacement_off slot payload k hk)⟩

open IntegerMultBounds.Machine in
theorem placedPayload_record_exec {b w d W H J : ℕ} {α : Type}
    (slot : Fin T) (column : Fin 35 ↪ Fin K) (cap : Q ≤ Q') (pos : 0 < Q)
    (body : P → Pr P (T+K) Q' A U) (child : Pr Empty T Q A U)
    (v : HS (T+K) Q' A U) (S : Stacks (T+K) A)
    (record : List (Fin (A+4))) (sym : α → Fin 4) (src dst : ℤ → Fin 4) (p q : ℤ)
    (input output : Fin ((b^(w+1))^d*W) → α) :
    let bank := payloadPlacement slot (column 24)
    let ready := RecordReady (b := b) (w := w) (d := d) (W := W)
      (column.trans (Fin.natAddEmb T)) H J record sym src dst p q
    ready input S → ∀ u D n,
      Exec Empty.elim child (mk (stateLiftDown pos (embDn bank v)) (embStk bank S)) n (mk u D) →
      (∀ z, RadixToBinary.binaryEncoding.encode (putWord src p (List.ofFn (sym ∘ output)) z) =
        readAt blank (D.L slot) (D.R slot) (z-p)) →
      ∃ z F, z.user = u.user ∧ Exec body (statePlacedNormalized bank cap pos Empty.elim child)
        (mk v S) (1+n) (mk z F) ∧ ready output F := by
  intro bank ready start u D n run returned
  obtain ⟨z,F,user,placed,left,right,keep⟩ := payloadPlacement_exec slot (column 24) cap pos body child v S u D n run
  refine ⟨z,F,user,placed,start.returnPayload (fun i hi => keep _ (column.injective.ne hi)) ?_⟩
  intro k
  exact (returned k).trans (by change _ = readAt blank (F.L ((column 24).natAdd T)) (F.R ((column 24).natAdd T)) _; rw [left,right])

open IntegerMultBounds.Machine FlatCoordinateLayout in
/-- Use the signed pass's positioned symbol reads and cell action to recover
the binary payload and the read required by the caller's record frame. -/
theorem signedChildReturnedRead {M r d W records : ℕ} [NeZero M]
    (e : (Fin r ⊕ Fin r) ≃ Fin d) (w inv : Fin r → ZMod M) (units : ∀ i, w i * inv i = 1)
    (before : Fin (records*(M^d*W)) → ZMod 2) (out : Fin (records*(M^d*W)) → Fin 4)
    (src : ℤ → Fin 4) (p : ℤ) (left right : List (Fin (A+4)))
    (returned : ∀ z, RadixToBinary.binaryEncoding.encode (putWord src p (List.ofFn out) z) =
      readAt blank left right (z-p))
    (action : ∀ j x k, out (finProdFinEquiv (j,index (signedChildAddress e w inv x) k)) =
      SparseRoleCircuit.encode (before (finProdFinEquiv (j,index x k)))) :
    ∃ after : Fin (records*(M^d*W)) → ZMod 2,
      (∀ z, RadixToBinary.binaryEncoding.encode (putWord src p (List.ofFn (SparseRoleCircuit.encode ∘ after)) z) =
        readAt blank left right (z-p)) ∧
      ∀ j x k, after (finProdFinEquiv (j,index (signedChildAddress e w inv x) k)) =
        before (finProdFinEquiv (j,index x k)) := by
  obtain ⟨after,rfl,cell⟩ := signedChildOutput SparseRoleCircuit.encode e w inv units before out action
  exact ⟨after,returned,cell⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
