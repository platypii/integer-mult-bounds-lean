module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackPrefixPass
public import IntegerMultBounds.MathlibTM2.Cover.FallbackFiberBank
public import IntegerMultBounds.MathlibTM2.Routing.BinaryCanonicalCopy

/-! Initialize the original-order shear from binary dimensions and unmarked metadata. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host Routing
variable {T A : ℕ} {P U : Type}

def prefixShear (r : Fin 15 ↪ Fin T) (call : Fin 12 ↪ Fin T) (count : Fin T) : Pr P T 217 A U :=
  .seq (binaryCanonicalProgram (call 5) (r 4))
    (.seq (binaryCanonicalCopyProgram (r 2) (call 7) (r 4) (r 5))
      (.seq (initializeBank call) (prefixPass r call count)))

theorem prefixShear_exec (body : P → Pr P T 217 A U) (r : Fin 15 ↪ Fin T)
    (call : Fin 12 ↪ Fin T) (slot : call 8 = r 3)
    (outside : ∀ i : Fin 15, i ≠ 3 → ∀ j, call j ≠ r i)
    (count : Fin T) (hr : ∀ i, r i ≠ count) (ht : ∀ i, call i ≠ count)
    (L K H W N stride c M B : ℕ) (hW : B < 2^W) (fits : N < 2^L) (hs : stride < 2^K) (ps : 0 < stride) (hc : c < M) (hM : M < 2^H) (hB : 0 < B)
    (v : HS T 217 A U) (S : Stacks T A) (extent : S.R (r 1) = binSyms L N)
    (counter : S.R (r 13) = []) (gap : S.R (r 14) = binSyms K stride)
    (coef : S.R (r 0) = binSyms H c) (modulus : S.R (r 2) = binSyms H M)
    (scratch : ∀ j : Fin 15, 3 ≤ j → j ≤ 12 → S.R (r j) = [])
    (source dest : ℤ → Fin 4) (p q : ℤ) (payload : ℕ → ℕ → List (Fin 4))
    (hw : ∀ i y, (payload i y).length = B)
    (empty : S.R count = []) (left : ∀ i : Fin 12, i < 10 → S.L (call i) = [])
    (right : ∀ i : Fin 12, i < 10 → S.R (call i) = if i = 5 then binSyms W B else [])
    (src : ∀ k, RadixToBinary.binaryEncoding.encode
      (putWord source p (TranslationStream.fibers M N payload).flatten k) =
        readAt blank (S.L (call 10)) (S.R (call 10)) (k-p))
    (dst : ∀ k, RadixToBinary.binaryEncoding.encode (dest k) =
        readAt blank (S.L (call 11)) (S.R (call 11)) (k-q)) :
    ∃ bs ms z F n, Counter.value bs = B ∧ Counter.value ms = M ∧ z.user = v.user ∧ n ≤ 6*N+17*L+4*W+10*H+31 + N*(L*(12*(K+H)+78)+22*K+180*H+173+48*H*H+(207*(M*B)+241)*25)+2 ∧
      Exec body (prefixShear r call count) (mk v S) n (mk z F) ∧
      F.R count = [] ∧ PrefixReady r L K H stride c M N F ∧
      RepT (Alphabet.mapTapes RadixToBinary.binaryEncoding
        (prefixBank N M B (fun i => c*(i/stride%M)%M) source dest p q payload bs ms N)) (F.L ∘ call) (F.R ∘ call) := by
  have dis (i : Fin 15) (j : Fin 12) (hj : j ≠ 8) : r i ≠ call j := by
    by_cases h : i = 3
    · subst i; rw [← slot]; exact call.injective.ne hj.symm
    · exact (outside i h j).symm
  have d5 (i : Fin 15) := dis i 5 (by decide)
  have d7 (i : Fin 15) := dis i 7 (by decide)
  obtain ⟨bs,u,cb,hb,_,hu,width⟩ := binaryCanonical_exec body (call 5) (r 4)
    (outside 4 (by decide) 5) W B hW v S (by simpa using right 5 (by decide))
    (scratch 4 (by decide) (by decide))
  let D : Stacks T A := {S with R := Function.update S.R (call 5) (bs.map bitSymbol)}
  obtain ⟨ms,w,cm,hm,_,hw',mod⟩ := binaryCanonicalCopy_exec body (r 2) (call 7) (r 4) (r 5)
    (by simp [List.nodup_cons,r.injective.eq_iff,d7,Ne.symm (d7 4),Ne.symm (d7 5)])
    H M hM u D (by simpa [D,Function.update_of_ne (d5 2)] using modulus)
    (by simpa [D,call.injective.eq_iff] using right 7 (by decide))
    (by simpa [D,Function.update_of_ne (d5 4)] using scratch 4 (by decide) (by decide))
    (by simpa [D,Function.update_of_ne (d5 5)] using scratch 5 (by decide) (by decide))
  let E : Stacks T A := {D with R := Function.update D.R (call 7) (ms.map bitSymbol)}
  obtain ⟨G,init,hR,mark,_,rep⟩ := initializeBank_exec body call bs ms _ dest p q w E left
    (by intro i hi; by_cases h : i = 5
        · subst i; simp [E,D,call.injective.eq_iff]
        · by_cases h' : i = 7 <;> simp [E,D,call.injective.eq_iff,h,h',right i hi])
    (by simpa [E,D,call.injective.eq_iff] using src)
    (by simpa [E,D,call.injective.eq_iff] using dst)
  have keep (i : Fin 15) : G.R (r i) = S.R (r i) := by
    simp [hR,E,D,Function.update_of_ne (d7 i),Function.update_of_ne (d5 i)]
  obtain ⟨z,F,n,hz,hn,run,rest,ready,final⟩ := prefixPass_exec body r call slot outside count hr ht
    L K H N stride c M B fits hs ps hc hM hB w G ((keep 1).trans extent) ((keep 13).trans counter)
    ((keep 14).trans gap) ((keep 0).trans coef) ((keep 2).trans modulus)
    (fun i hi hj => (keep i).trans (scratch i hi hj)) (slot ▸ mark)
    source dest p q payload hw bs ms hb hm cb cm
    (by simpa [hR,E,D,Function.update_of_ne (ht 5).symm,Function.update_of_ne (ht 7).symm] using empty)
    (by simpa [prefixBank,TranslationPreparedFamily.outputPrefix,putWord] using rep)
  exact ⟨bs,ms,z,F,_,hb,hm,hz.trans (hw'.trans hu),by omega,
    Exec.seq width (Exec.seq mod (Exec.seq init run)),rest,ready,final⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
