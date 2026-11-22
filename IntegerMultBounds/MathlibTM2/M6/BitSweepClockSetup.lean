module

public import IntegerMultBounds.MathlibTM2.Cover.LabelDirectorySetup
public import IntegerMultBounds.MathlibTM2.Host.UnaryBinaryHalving

/-! Initialize the destination counter, sweep clocks and binary rank modulus. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks.Shared50ModularControl
open Cover.LabelDirectorySetup Host Stack Node RadixCounterData RadixDigits

def sweepSetupPorts : Fin 15 ↪ Fin 37 := ⟨![1,2,3,4,7,6,8,9,11,12,0,5,13,14,15],by decide⟩

noncomputable def setupSweepClocks {T Q : ℕ} {P U : Type} (p : Fin 37 ↪ Fin T) : Pr P T Q prime U :=
  .seq (setupFields 128 (sweepSetupPorts.trans p) (p 10) (p 29))
    (.seq (umul 128 (p 18) (p 21) (p 3))
      (unaryBinaryWidth (p 7) (p 18) (p 35) (p 1) (p 2) (p 3) (p 4) (p 6) (p 8)))

theorem setupSweepClocks_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (p : Fin 37 ↪ Fin T) (w H : ℕ) (v : HS T Q prime U) (S : Stacks T prime)
    (width : (S.R (p 10)).length = w) (bits : (S.R (p 18)).length = H) (unit : (S.R (p 29)).length = 1)
    (fits : (prime^w)^128 < 2^H)
    (blank : ∀ i ∈ ([0,1,2,3,4,5,6,7,8,21,35] : List (Fin 37)), S.R (p i) = []) :
    let L := w*128
    let M := (prime^w)^128
    let R := Function.update (Function.update (Function.update (Function.update (Function.update S.R
      (p 5) (List.replicate L tick)) (p 0) ((zeros prime_prime.two_le L).map digitSymbol))
      (p 7) (List.replicate M tick)) (p 21) (List.replicate (128*H) tick)) (p 35) (binSyms H M)
    ∃ z n, z.user = v.user ∧ n ≤ 8*w+43*M+16*H+40 ∧
      Exec body (setupSweepClocks p) (mk v S) n (mk z {S with R := R}) := by
  intro L M R
  obtain ⟨u,k,hu,hk,setup⟩ := setupFields_exec (body := body) 128 (sweepSetupPorts.trans p) (p 10) (p 29)
    (fun i => p.injective.ne (by decide +revert)) (fun i => p.injective.ne (by decide +revert)) v S unit
    (fun i hi => blank (sweepSetupPorts i) (by decide +revert))
  rw [width,pow_mul] at hk
  let B := {S with R := prepared S.R (sweepSetupPorts.trans p) L}
  change Exec _ _ _ _ (mk u {S with R := prepared S.R (sweepSetupPorts.trans p) (_*128)}) at setup
  rw [width] at setup
  have keep (i : Fin 37) (h₀ : i ≠ 0) (h₅ : i ≠ 5) (h₇ : i ≠ 7) : B.R (p i) = S.R (p i) := by
    change Function.update (Function.update (Function.update S.R (p 5) _) (p 0) _) (p 7) _ (p i) = _
    simp [h₀,h₅,h₇]
  obtain ⟨y,hy,clock⟩ := umul_exec body 128 (a := p 18) (b := p 21) (t := p 3)
    (by simp) (by simp) (by simp) u B ((keep 3 (by decide) (by decide) (by decide)).trans (blank 3 (by decide)))
  rw [keep 18 (by decide) (by decide) (by decide),bits,keep 21 (by decide) (by decide) (by decide),
    blank 21 (by decide),List.append_nil] at clock
  let F := {B with R := Function.update B.R (p 21) (List.replicate (128*H) tick)}
  have same (i : Fin 37) (h : i ≠ 21) : F.R (p i) = B.R (p i) := Function.update_of_ne (p.injective.ne h) _ _
  have count : (F.R (p 7)).length = M := by
    rw [same 7 (by decide)]
    change List.length (Function.update (β := fun _ => List (Fin (prime+4))) _ (p 7) (List.replicate (prime^L) (tick (A := prime))) (p 7)) = _
    simp [L,M,pow_mul]
  have fresh (i : Fin 37) (hi : i ∈ ([35,1,2,3,4,6,8] : List (Fin 37))) : F.R (p i) = [] := by
    rw [same i (by decide +revert),keep i (by decide +revert) (by decide +revert) (by decide +revert)]
    exact blank i (by decide +revert)
  obtain ⟨z,t,hz,ht,word⟩ := unaryBinaryWidth_exec (body := body)
    (src := p 7) (width := p 18) (dst := p 35) (a := p 1) (h := p 2) (par := p 3) (bits := p 4)
    (cnt := p 6) (saved := p 8) (by simp [List.nodup_cons]) M H (Nat.size_le.mpr fits) y F count
    (by rw [same 18 (by decide),keep 18 (by decide) (by decide) (by decide)]; exact bits)
    (by intro i hi; simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact fresh _ (by decide))
  refine ⟨z,k+(4*H+4+t),hz.trans (hy.trans hu),?_,Exec.seq setup (Exec.seq clock ?_)⟩
  · change k ≤ 8*w+8+22*M at hk; omega
  · simpa only [R,F,B,prepared,L,M,pow_mul,Function.Embedding.trans_apply,
      show sweepSetupPorts 11 = 5 from rfl,show sweepSetupPorts 10 = 0 from rfl,show sweepSetupPorts 4 = 7 from rfl] using word

/-- The coordinate modulus also supplies the radix leaf of the rank formula. -/
theorem setupSweepRadix_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (p : Fin 37 ↪ Fin T) (w H : ℕ) (pos : 0 < w) (fits : (prime^w)^128 < 2^H)
    (v : HS T Q prime U) (S : Stacks T prime) (unit : (S.R (p 29)).length = 1)
    (width : (S.R (p 10)).length = w) (bits : (S.R (p 18)).length = H)
    (blank : ∀ i ∈ ([1,2,3,4,6,8,23,34,36] : List (Fin 37)), S.R (p i) = []) :
    let base := prime^w
    ∃ z n, z.user = v.user ∧ n ≤ 45*base+18*H+36 ∧
      Exec body (.seq (expProg 0 prime (p 29) (p 10) (p 23) (p 1) (p 2) (p 3))
        (.seq (unaryBinaryWidth (p 23) (p 18) (p 36) (p 1) (p 2) (p 3) (p 4) (p 6) (p 8))
          (.seq (bcopy (p 36) (p 34) (p 1) (p 2)) (uclear (p 23)))))
        (mk v S) n (mk z {S with
          R := Function.update (Function.update S.R (p 36) (binSyms H base)) (p 34)
            (binSyms H (base : ZMod (base^128)).val)}) := by
  intro base
  obtain ⟨u,k,hu,hk,power⟩ := Cover.LabelCounts.power_exec body (one := p 29) (exponent := p 10) (dst := p 23)
    (t₁ := p 1) (t₂ := p 2) (t₃ := p 3) (by simp [List.nodup_cons]) v S unit (by
      intro i hi; simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl <;> exact blank _ (by decide))
  rw [width] at power hk
  let B := {S with R := Function.update S.R (p 23) (List.replicate base tick)}
  have keep (i : Fin 37) (hi : i ≠ 23) : B.R (p i) = S.R (p i) := Function.update_of_ne (p.injective.ne hi) _ _
  have big : base < base^128 := by
    have h : 1 < base := Nat.one_lt_pow (by omega) prime_prime.one_lt
    simpa only [pow_one] using (Nat.pow_lt_pow_right h (by decide : 1 < 128))
  obtain ⟨y,l,hy,hl,word⟩ := unaryBinaryWidth_exec (body := body)
    (src := p 23) (width := p 18) (dst := p 36) (a := p 1) (h := p 2) (par := p 3)
    (bits := p 4) (cnt := p 6) (saved := p 8) (by simp [List.nodup_cons]) base H
    (Nat.size_le.mpr (big.trans fits)) u B (by simp [B]) (by rwa [keep 18 (by decide)]) (by
      intro i hi; simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact (keep _ (by decide)).trans (blank _ (by decide)))
  let F := {B with R := Function.update B.R (p 36) (binSyms H base)}
  obtain ⟨t,ht,copy⟩ := bcopy_exec body (a := p 36) (c := p 34) (t₁ := p 1) (t₂ := p 2)
    (by simp [List.nodup_cons]) y F (by simp [F,B,blank]) (by simp [F,B,blank])
  simp only [F,B,Function.update_self,length_binSyms,Function.update_of_ne (show p 34 ≠ p 36 by simp),
    Function.update_of_ne (show p 34 ≠ p 23 by simp),blank 34 (by decide),List.append_nil] at copy
  let G := {F with R := Function.update F.R (p 34) (binSyms H base)}
  obtain ⟨z,hz,clear⟩ := uclear_exec body (p 23) t G
  have size : (G.R (p 23)).length = base := by simp [G,F,B]
  refine ⟨z,k+(l+(6*H+6+(2*(G.R (p 23)).length+2))),hz.trans (ht.trans (hy.trans hu)),?_,
    Exec.seq power (Exec.seq word (Exec.seq copy ?_))⟩
  · change k ≤ 22*base at hk; rw [size]; omega
  · rw [ZMod.val_natCast,Nat.mod_eq_of_lt big]
    apply clear.cast rfl
    apply congrArg (mk z)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases h : i = p 23 <;> simp_all [G,F,B,Function.update_apply]

end IntegerMultBounds.MathlibTM2.M6.BitNode
