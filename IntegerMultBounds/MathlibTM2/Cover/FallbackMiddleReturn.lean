module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackMiddleShear
public import IntegerMultBounds.MathlibTM2.Cover.FallbackDimension
import IntegerMultBounds.MathlibTM2.Host.ChunkSwap

/-! Install the row descriptor, shear the payload and return it to its original port. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
variable {T A P M G B : ℕ} {U F : Type}

def middleWork : Fin 30 ↪ Fin 31 := Fin.castLEEmb (by decide)
def middleDescriptorPorts : Fin 11 ↪ Fin 31 := ⟨![28,2,29,4,30,5,6,7,8,9,10],by decide⟩
def middleReturnPorts : Fin 8 ↪ Fin 31 := ⟨![23,22,17,18,19,20,14,30],by decide⟩

def returnedMiddleShear (r : Fin 31 ↪ Fin T) : Pr F T 217 A U :=
  .seq (middleRowDescriptor (middleDescriptorPorts.trans r))
    (middleShearAndReturn (middleWork.trans r) (middleReturnPorts.trans r))

theorem returnedMiddleShear_exec (body : F → Pr F T 217 A U) (r : Fin 31 ↪ Fin T)
    (w c : ℕ) (radix : M = prime^(w+1)) (hc : c < M) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (source dest : ℤ → Fin 4) (p q : ℤ) (word : Fin ((P*M*G)*(M*B)) → Fin 4)
    (bs ms : List Bool) (hb : Counter.value bs = B) (hm : Counter.value ms = M)
    (cb : GrowingCounterData.Canonical bs) (cm : GrowingCounterData.Canonical ms)
    (v : HS T 217 A U) (S : Stacks T A)
    (heads : S.R (r 28) = binSyms P.size P) (ticks : S.R (r 29) = binSyms G.size G)
    (free : ∀ i : Fin 30, 24 ≤ i → i ≤ 27 → S.R (r (middleWork i)) = [])
    (ready : MiddleGroupReady middleArithmetic M.size c 0 M (embStk (middleWork.trans r) S))
    (marker : S.L (r 30) = [separator]) (fresh : S.R (r 30) = [])
    (rep : RepT (Alphabet.mapTapes RadixToBinary.binaryEncoding
      (TranslationExecutionReuse.bank (putWord source p (List.ofFn word)) dest p q bs ms []))
      (S.L ∘ r ∘ middleWork ∘ middleTranslation) (S.R ∘ r ∘ middleWork ∘ middleTranslation))
    (empty : ∀ z, q ≤ z → z < q+((P*M*G)*(M*B) : ℕ) → dest z = blank) :
    let N := (P*M*G)*(M*B)
    let out := FiberLayoutData.translated word (fun i => c*(i.val/G%M)%M)
    ∃ z D n, z.user = v.user ∧ n ≤ (210*(2*(Nat.size prime+1)^2)+16120)*N ∧
      Exec body (returnedMiddleShear r) (mk v S) n (mk z D) ∧
      (∀ x, readAt blank (D.L (r 22)) (D.R (r 22)) (x-p) =
        RadixToBinary.binaryEncoding.encode (putWord source p out x)) ∧
      ∀ x, readAt blank (D.L (r 23)) (D.R (r 23)) (x-q) = RadixToBinary.binaryEncoding.encode (dest x) := by
  intro N out
  have hM : 0 < M := radix ▸ pow_pos prime_prime.pos _
  obtain ⟨ps,u,n,cp,hp,hu,hn,setup⟩ := middleRowDescriptor_exec body (middleDescriptorPorts.trans r)
    P M G hP hM hG v S heads ready.2.2.1 ticks (by
      intro i lo hi
      fin_cases i <;> first
        | contradiction | exact fresh | exact ready.2.2.2.1 4 (by decide) (by decide)
        | exact ready.2.2.2.1 5 (by decide) (by decide) | exact ready.2.2.2.1 6 (by decide) (by decide)
        | exact ready.2.2.2.1 7 (by decide) (by decide) | exact ready.2.2.2.1 8 (by decide) (by decide)
        | exact ready.2.2.2.1 9 (by decide) (by decide))
  let E : Stacks T A := {S with R := Function.update S.R (r 30) (ps.map bitSymbol)}
  have keep (i : Fin 30) : E.R (r (middleWork i)) = S.R (r (middleWork i)) :=
    Function.update_of_ne (r.injective.ne ((by decide : ∀ j, middleWork j ≠ 30) i)) _ _
  have eq : embStk (middleWork.trans r) E = embStk (middleWork.trans r) S :=
    Stacks.ext rfl rfl rfl (funext keep)
  obtain ⟨z,D,m,hz,ht,run,tapes⟩ := middleShearAndReturn_exec body (middleWork.trans r)
    (middleReturnPorts.trans r) (fun i => congrArg r ((by decide : ∀ i : Fin 7,
      middleReturnPorts i.castSucc = middleWork (middleTranslation (![11,10,4,5,6,7,1] i))) i))
    (fun i => r.injective.ne ((by decide : ∀ j, middleWork j ≠ middleReturnPorts 7) i))
    w c radix hc hP hG hB source dest p q word bs ms ps hb hm hp cb cm cp u E
    ((keep 28).trans heads) ((keep 29).trans ticks) (fun i lo hi => (keep i).trans (free i lo hi))
    (eq ▸ ready) (by intro i x; exact (rep i x).trans (by simp only [Function.comp_apply,Function.Embedding.trans_apply,keep]; rfl))
    (by intro x
        change _ = readAt blank (S.L (r 30)) (Function.update S.R (r 30) _ (r 30)) _
        simp only [marker,Function.update_self,readAt_single]
        rw [← CountedLoopReuseAlphabet.encoding_binary]
        exact congrFun (encodedBinary_eq ps) x) empty
  change m ≤ (210*(2*(Nat.size prime+1)^2)+15688)*N at ht
  have rows : P*M*G ≤ N := Nat.le_mul_of_pos_right _ (Nat.mul_pos hM hB)
  exact ⟨z,D,n+m,hz.trans hu,by nlinarith only [hn,ht,rows],Exec.seq setup run,
    fun x => (tapes 1 x).symm,fun x => (tapes 0 x).symm⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
