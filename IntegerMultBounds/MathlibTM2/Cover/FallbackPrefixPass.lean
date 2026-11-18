module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackPrefixLoop

/-! Build the prefix loop clock from the binary extent supplied in the digit workspace. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open Mult.PhaseCellToeplitz (countedLoop)
variable {T A : ℕ} {P U : Type}

def prefixPass (r : Fin 15 ↪ Fin T) (call : Fin 12 ↪ Fin T) (count : Fin T) : Pr P T 217 A U :=
  .seq (toUnary (r 1) count (r 4) (r 5) (r 6)) (.seq (bzero (r 1) (r 13) (r 4))
    (.seq (bclear (r 1)) (countedLoop count (prefixStep r call))))

theorem prefixPass_exec (body : P → Pr P T 217 A U) (r : Fin 15 ↪ Fin T)
    (call : Fin 12 ↪ Fin T) (slot : call 8 = r 3)
    (outside : ∀ i : Fin 15, i ≠ 3 → ∀ j, call j ≠ r i)
    (count : Fin T) (hr : ∀ i, r i ≠ count) (ht : ∀ i, call i ≠ count)
    (L K H N stride c M B : ℕ) (fits : N < 2^L) (hs : stride < 2^K) (ps : 0 < stride) (hc : c < M) (hM : M < 2^H) (hB : 0 < B)
    (v : HS T 217 A U) (S : Stacks T A) (extent : S.R (r 1) = binSyms L N)
    (counter : S.R (r 13) = []) (gap : S.R (r 14) = binSyms K stride)
    (coef : S.R (r 0) = binSyms H c) (modulus : S.R (r 2) = binSyms H M)
    (scratch : ∀ j : Fin 15, 3 ≤ j → j ≤ 12 → S.R (r j) = [])
    (marker : S.L (r 3) = [separator])
    (source dest : ℤ → Fin 4) (p q : ℤ) (payload : ℕ → ℕ → List (Fin 4))
    (hw : ∀ i y, (payload i y).length = B) (bs ms : List Bool)
    (hb : Counter.value bs = B) (hm : Counter.value ms = M)
    (cb : GrowingCounterData.Canonical bs) (cm : GrowingCounterData.Canonical ms)
    (empty : S.R count = [])
    (rep : RepT (Alphabet.mapTapes RadixToBinary.binaryEncoding
      (prefixBank N M B (fun i => c*(i/stride%M)%M) source dest p q payload bs ms 0)) (S.L ∘ call) (S.R ∘ call)) :
    ∃ z F n, z.user = v.user ∧ n ≤ 6*N+17*L+12 + N*(L*(12*(K+H)+78)+22*K+180*H+173+48*H*H+(207*(M*B)+241)*25)+2 ∧
      Exec body (prefixPass r call count) (mk v S) n (mk z F) ∧
      F.R count = [] ∧ PrefixReady r L K H stride c M N F ∧
      RepT (Alphabet.mapTapes RadixToBinary.binaryEncoding
        (prefixBank N M B (fun i => c*(i/stride%M)%M) source dest p q payload bs ms N)) (F.L ∘ call) (F.R ∘ call) := by
  have sep (i : Fin 15) : count ≠ r i := (hr i).symm
  obtain ⟨u,k,hu,hk,clock⟩ := toUnary_exec_linear body (a := r 1) (z := count)
    (w := r 4) (t := r 5) (t₂ := r 6) (by simp [List.nodup_cons,r.injective.eq_iff,hr,sep])
    fits v S extent (scratch 4 (by decide) (by decide)) (scratch 5 (by decide) (by decide))
    (scratch 6 (by decide) (by decide))
  rw [empty,List.append_nil] at clock
  let D : Stacks T A := {S with R := Function.update S.R count (List.replicate N Node.tick)}
  obtain ⟨u',hu',zero⟩ := bzero_exec body (wR := r 1) (c := r 13) (t := r 4)
    (by simp [List.nodup_cons,r.injective.eq_iff]) u D
    (by simpa [D,Function.update_of_ne (hr 4)] using scratch 4 (by decide) (by decide))
  have len : (D.R (r 1)).length = L := by simp [D,Function.update_of_ne (hr 1),extent,length_binSyms]
  have free : D.R (r 13) = [] := by simpa [D,Function.update_of_ne (hr 13)] using counter
  rw [len,free,List.append_nil] at zero
  let E : Stacks T A := {D with R := Function.update D.R (r 13) (binSyms L 0)}
  obtain ⟨w,hw',_,clear⟩ := bclear_exec body (r 1) u' E
  have len' : (E.R (r 1)).length = L := by simpa [E,r.injective.eq_iff] using len
  rw [len'] at clear
  let G : Stacks T A := {E with R := Function.update E.R (r 1) []}
  have keep (i : Fin 15) (h : i ≠ 1) (h' : i ≠ 13) : G.R (r i) = S.R (r i) := by
    simp [G,E,D,Function.update_of_ne (hr i),Function.update_of_ne (r.injective.ne h),
      Function.update_of_ne (r.injective.ne h')]
  have ready : PrefixReady r L K H stride c M 0 G := by
    refine ⟨?_,(keep 14 (by decide) (by decide)).trans gap,(keep 0 (by decide) (by decide)).trans coef,
      (keep 2 (by decide) (by decide)).trans modulus,?_,marker⟩
    · simp [G,E,r.injective.eq_iff]
    · intro j hj hk h2
      by_cases h1 : j = 1
      · simp [G,h1]
      · exact (keep j h1 (by omega)).trans (scratch j (by omega) hk)
  obtain ⟨z,F,n,hz,hn,loop,rest,final,bank⟩ := prefixLoop_exec body r call slot outside count hr ht
    L K H N stride c M B fits.le hs ps hc hM hB w G ready source dest p q payload hw bs ms hb hm cb cm
    (by simp [G,E,D,Function.update_of_ne (sep 1),Function.update_of_ne (sep 13)])
    (by intro i j; simpa [G,E,D,Function.comp_apply,Function.update_of_ne (ht i),
          Function.update_of_ne (outside 1 (by decide) i),Function.update_of_ne (outside 13 (by decide) i)] using rep i j)
  exact ⟨z,F,_,hz.trans (hw'.trans (hu'.trans hu)),by omega,Exec.seq clock (Exec.seq zero (Exec.seq clear loop)),
    rest,final,bank⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
