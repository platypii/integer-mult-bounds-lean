module

public import IntegerMultBounds.MathlibTM2.M6.BitIdleDispatchClocks
public import IntegerMultBounds.MathlibTM2.M6.BitParentArchiveSeed
public import IntegerMultBounds.MathlibTM2.Cover.LabelCounts

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback Node M8.RevMachine
open Shared50ModularControl (prime)

/-- From the long width clock alone, construct the unit and the binary modulus.
The temporary unary power is erased before returning to the caller. -/
theorem archiveModulus {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U) (r : Fin 10 ↪ Fin T) :
    ∃ code, ∀ w u (S : Stacks T prime), (S.R (r 0)).length = w →
      (∀ j : Fin 10, j ≠ 0 → S.R (r j) = []) →
      let M := prime^w
      let A := {S with R := Function.update S.R (r 1) (binSyms 1 1)}
      let F := {A with R := Function.update A.R (r 3) (binSyms M.size M)}
      ∃ z t, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧ CleanupBound S F t (47*M+15) := by
  let unit : Act T Q prime U := .push (.rt (r 1)) (fun _ => bitSymbol true) .done
  let power := expProg (P := P) (U := U) (Q := Q) (A := prime) 0 prime (r 1) (r 0) (r 2) (r 4) (r 5) (r 6)
  let binary := unaryBinary (P := P) (U := U) (Q := Q) (A := prime) (r 2) (r 3) (r 4) (r 5) (r 6) (r 7) (r 8) (r 9)
  refine ⟨(.act unit : Pr P T Q prime U).seq (power.seq (binary.seq (bclear (r 2)))),?_⟩
  intro w u S clock free M A F
  have start : Exec body (.act unit) (mk u S) 1 (mk u A) := by
    simpa [unit,Action.run,update_rt,A,free,binSyms] using Exec.act (body := body) unit (mk u S)
  have vacant (j : Fin 10) (h : 2 ≤ j.val) : A.R (r j) = [] := by
    have ne : j ≠ 1 := by intro e; subst j; contradiction
    simpa [A,Function.update_of_ne (r.injective.ne ne)] using free j (by intro e; subst j; contradiction)
  obtain ⟨v,n,user,time,first⟩ := Cover.LabelCounts.power_exec body
    (one := r 1) (exponent := r 0) (dst := r 2) (t₁ := r 4) (t₂ := r 5) (t₃ := r 6)
    (by simp [r.injective.eq_iff]) u A (by simp [A,length_binSyms]) (by
      intro j hj
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl <;> apply vacant <;> decide)
  have exponent : (A.R (r 0)).length = w := by simpa [A,r.injective.eq_iff] using clock
  rw [exponent] at first time
  let B := {A with R := Function.update A.R (r 2) (List.replicate M tick)}
  have aux (j : Fin 10) (h : 3 ≤ j.val) : B.R (r j) = [] := by
    have ne : j ≠ 2 := by intro e; subst j; contradiction
    simpa [B,Function.update_of_ne (r.injective.ne ne)] using vacant j (by omega)
  obtain ⟨y,m,same,cost,encode⟩ := unaryBinary_exec (body := body) (src := r 2) (dst := r 3)
    (a := r 4) (h := r 5) (par := r 6) (bits := r 7) (cnt := r 8) (saved := r 9)
    (by simp [r.injective.eq_iff]) M v B (by simp [B]) (by
      intro j hj
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> apply aux <;> decide)
  let D := {B with R := Function.update B.R (r 3) (binSyms M.size M)}
  obtain ⟨z,done,_,erase⟩ := bclear_exec body (r 2) y D
  have len : (D.R (r 2)).length = M := by simp [D,B,r.injective.eq_iff]
  rw [len] at erase
  refine ⟨z,_,start.seq (first.seq (encode.seq (erase.cast rfl ?_))),done.trans (same.trans user),?_⟩
  · have reset : Function.update A.R (r 2) [] = A.R := by rw [← vacant 2 (by decide),Function.update_eq_self]
    simp [D,B,F,Function.update_comm (r.injective.ne (by decide : (3 : Fin 10) ≠ 2)),reset]
  · intro js nd
    have one := prependedWordCharge S (r 1) (binSyms 1 1) js nd
    have word := prependedWordCharge A (r 3) (binSyms M.size M) js nd
    simp only [free 1 (by decide),List.append_nil,length_binSyms] at one
    simp only [vacant 3 (by decide),List.append_nil,length_binSyms] at word
    change tapeCharge cleanupWeight js A ≤ _ at one
    change tapeCharge cleanupWeight js F ≤ _ at word
    have size : M.size ≤ M := Nat.size_le.mpr Nat.lt_two_pow_self
    change n ≤ 22*M at time
    change 1+(n+(m+(2*M+2)))+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+(47*M+15)
    omega

def descriptorArchiveSources {T : ℕ} (fields : Fin 6 → Fin T) (clock : Fin 7 ↪ Fin T)
    (power : Fin 10 ↪ Fin T) (i : Fin 9) : Fin T :=
  Fin.addCases (motive := fun _ => Fin T) fields (![power 3,power 1,clock 2] : Fin 3 → Fin T) i

def outsideArchiveOutputs {T : ℕ} (clock : Fin 7 ↪ Fin T) (power : Fin 10 ↪ Fin T) (j : Fin T) : Prop :=
  j ≠ clock 1 ∧ j ≠ clock 2 ∧ j ≠ power 1 ∧ j ≠ power 3

/-- Use a shared long clock for width division and exponentiation. The resulting
nine source words are exactly the inputs of the parent archive loader. -/
theorem descriptorArchiveWords {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (fields : Fin 6 → Fin T) (clock : Fin 7 ↪ Fin T) (power : Fin 10 ↪ Fin T)
    (widthPort : clock 0 = fields 3) (longPort : power 0 = clock 1)
    (shortFree : ∀ j, clock 2 ≠ power j)
    (outside : ∀ i, fields i ≠ clock 1 ∧ fields i ≠ clock 2 ∧ fields i ≠ power 1 ∧ fields i ≠ power 3) :
    let src := descriptorArchiveSources fields clock power
    ∃ code, ∀ (node : RecursiveInterchangeLayout.Descriptor) w, node.width = 64*(w+1) →
      ∀ u (S : Stacks T prime), (∀ i, S.R (fields i) = (Routines.hdr node i).map bitSymbol) →
        (∀ j : Fin 7, j ≠ 0 → S.R (clock j) = []) →
        (∀ j : Fin 10, j ≠ 0 → S.R (power j) = []) →
        ∃ z F t, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧
          CleanupBound S F t ((18*(w+1)+11*(w+1).size+17)+(47*prime^(w+1)+15)) ∧
          F.R (clock 1) = List.replicate (w+1) blank ∧
          (∀ i, F.R (src i) = (parentArchiveSeed node w).R (parentArchivePorts i)) ∧
          ∀ j, j ≠ clock 1 → j ≠ clock 2 → j ≠ power 1 → j ≠ power 3 →
            F.L j = S.L j ∧ F.R j = S.R j := by
  intro src
  obtain ⟨read,divide⟩ := idleDispatchClocks body clock
  obtain ⟨make,encode⟩ := archiveModulus body power
  refine ⟨read.seq make,?_⟩
  intro node w width u S digits empty free
  have bits := (digits 3).trans (canonicalBits_symbols node.width)
  rw [width] at bits
  obtain ⟨v,n,start,user,paid⟩ := divide w u S (widthPort ▸ bits) empty
  let D := {S with R := Function.update (Function.update S.R (clock 1) (List.replicate (w+1) blank)) (clock 2) (List.replicate w blank)}
  have live : (D.R (power 0)).length = w+1 := by simp [D,longPort,clock.injective.eq_iff]
  have clear j (ne : j ≠ 0) : D.R (power j) = [] := by
    have away : power j ≠ clock 1 := longPort ▸ power.injective.ne ne
    simp [D,(shortFree j).symm,away,free j ne]
  obtain ⟨z,t,finish,same,charge⟩ := encode (w+1) v D live clear
  refine ⟨z,_,_,start.seq finish,same.trans user,paid.seq charge,?_,?_,?_⟩
  · have a : clock 1 ≠ power 1 := longPort ▸ power.injective.ne (by decide : (0 : Fin 10) ≠ 1)
    have b : clock 1 ≠ power 3 := longPort ▸ power.injective.ne (by decide : (0 : Fin 10) ≠ 3)
    simp [D,a,b,clock.injective.eq_iff]
  · intro i
    change _ = (fun j => (parentArchiveSeed node w).R (parentArchivePorts j)) i
    rw [parentArchiveSeed_words]
    induction i using Fin.addCases (m := 6) (n := 3) with
    | left j => simpa [src,descriptorArchiveSources,D,(outside j).1,(outside j).2.1,(outside j).2.2.1,(outside j).2.2.2] using digits j
    | right j =>
      simp only [src,descriptorArchiveSources,Fin.addCases_right]
      fin_cases j <;> simp [D,power.injective.eq_iff,shortFree]
  · intro j a b c d
    exact ⟨rfl,by simp [D,a,b,c,d]⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
