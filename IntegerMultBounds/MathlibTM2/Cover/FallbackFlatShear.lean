module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackShearRead
import IntegerMultBounds.Machine.FlatControlledShift

/-! Row-operation semantics of the executed shear on a single packed array. -/
public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
variable {T A : ℕ} {P U : Type}

theorem flatShear_exec (body : P → Pr P T 217 A U) (r : Fin 13 ↪ Fin T)
    (call : Fin 12 ↪ Fin T) (slot : call 8 = r 3)
    (outside : ∀ i : Fin 13, i ≠ 3 → ∀ j, call j ≠ r i)
    (count : Fin T) (hr : ∀ i, r i ≠ count) (ht : ∀ i, call i ≠ count)
    (L K M B : ℕ) [NeZero M] (c : ZMod M) (hwidth : B < 2^K) (hM : M < 2^L) (hB : 0 < B)
    (v : HS T 217 A U) (S : Stacks T A) (coef : S.R (r 0) = binSyms L c.val)
    (modulus : S.R (r 2) = binSyms L M) (width : S.R (r 12) = binSyms K B) (digit : S.R (r 1) = [])
    (scratch : ∀ i : Fin 13, 3 ≤ i → i < 12 → S.R (r i) = [])
    (source dest : ℤ → Fin 4) (p q : ℤ) (a : Fin (M*(M*B)) → Fin 4)
    (empty : S.R count = [])
    (left : ∀ i : Fin 12, i < 10 → S.L (call i) = [])
    (right : ∀ i : Fin 12, i < 10 → S.R (call i) = [])
    (src : ∀ k, RadixToBinary.binaryEncoding.encode
      (putWord source p (List.ofFn a) k) =
        readAt blank (S.L (call 10)) (S.R (call 10)) (k-p))
    (dst : ∀ k, RadixToBinary.binaryEncoding.encode (dest k) =
        readAt blank (S.L (call 11)) (S.R (call 11)) (k-q)) :
    ∃ z F n, z.user = v.user ∧ n ≤ 6*M+25*L+10*K+35 + M*(48*L*L+162*L+93+(207*(M*B)+241)*25)+2 ∧
      Exec body (dimensionShear r call count) (mk v S) n (mk z F) ∧
      F.R count = [] ∧ FiberReady r L c.val M M F ∧
      ∀ {d : ℕ} (i k : Fin d) (hik : i < k) (u : Fin d → ZMod M) (j : Fin B),
        let w := (RowOp.shear i k hik c).apply u
        let index (f : Fin d → ZMod M) := FiberLayoutData.index
          (⟨(f i).val,(f i).val_lt⟩ : Fin M) (⟨(f k).val,(f k).val_lt⟩ : Fin M) j
        readAt blank (F.L (call 11)) (F.R (call 11)) (((index w).val : ℤ) - (M*(M*B) : ℕ)) =
          RadixToBinary.binaryEncoding.encode (a (index u)) := by
  obtain ⟨bs,ms,z,F,n,_,_,hu,hn,run,rest,ready,rep⟩ :=
    dimensionShear_exec body r call slot outside count hr ht L K c.val M B hwidth c.val_lt hM hB
      v S coef modulus width digit scratch source dest p q (FlatControlledShift.payload a)
      (FlatControlledShift.payload_length a) empty left right
      (by simpa only [FlatControlledShift.source_eq] using src) dst
  refine ⟨z,F,n,hu,hn,run,rest,ready,?_⟩
  intro d i k hik u j
  have h := shear_read call F source dest p q _ (FlatControlledShift.payload_length a) bs ms c i k hik u j rep
  simpa only [FiberLayoutData.index_val,Nat.add_assoc,FlatControlledShift.payload,
    dite_eq_left (u i).val_lt,dite_eq_left (u k).val_lt,List.getElem_ofFn,Fin.eta] using h

end IntegerMultBounds.MathlibTM2.Cover.Fallback
