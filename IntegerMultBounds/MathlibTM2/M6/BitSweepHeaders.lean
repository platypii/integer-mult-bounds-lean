module

public import IntegerMultBounds.MathlibTM2.M6.BitSweepClockSetup
public import IntegerMultBounds.MathlibTM2.Cover.LabelTraversal
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Initialize sweep clocks, both moduli, and the binary literals from unary headers. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks.Shared50ModularControl
open Host Stack Node RadixCounterData RadixDigits

noncomputable def sweepHeaderWords (w H : ℕ) : List (Fin 37 × List (Fin (prime+4))) :=
  let M := prime^w
  let N := M^128
  [(5,List.replicate (w*128) tick),(0,(zeros prime_prime.two_le (w*128)).map digitSymbol),
   (7,List.replicate N tick),(21,List.replicate (128*H) tick),(35,binSyms H N),
   (36,binSyms H M),(34,binSyms H (M : ZMod N).val),(20,binSyms H 0),(33,binSyms H 1)]

theorem sweepHeaders_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U) (p : Fin 37 ↪ Fin T) :
    ∃ program : Pr P T Q prime U, ∀ (w H : ℕ) (v : HS T Q prime U) (S : Stacks T prime),
    0 < w → (prime^w)^128 < 2^H → (S.R (p 10)).length = w → (S.R (p 18)).length = H →
    (S.R (p 29)).length = 1 →
    (∀ i ∈ ([0,1,2,3,4,5,6,7,8,20,21,23,33,34,35,36] : List (Fin 37)), S.R (p i) = []) →
    ∃ z t, z.user = v.user ∧ t ≤ 8*w+88*((prime^w)^128)+50*H+129 ∧
      Exec body program (mk v S) t (mk z {S with
        R := (sweepHeaderWords w H).foldl
          (fun R (kv : Fin 37 × List (Fin (prime+4))) => Function.update R (p kv.1) kv.2) S.R}) := by
  let radix : Pr P T Q prime U := .seq (expProg 0 prime (p 29) (p 10) (p 23) (p 1) (p 2) (p 3))
    (.seq (unaryBinaryWidth (p 23) (p 18) (p 36) (p 1) (p 2) (p 3) (p 4) (p 6) (p 8))
      (.seq (bcopy (p 36) (p 34) (p 1) (p 2)) (uclear (p 23))))
  let oneWord : Pr P T Q prime U := unaryBinaryWidth (p 29) (p 18) (p 33) (p 1) (p 2) (p 3) (p 4) (p 6) (p 8)
  refine ⟨.seq (setupSweepClocks p) (.seq radix (.seq (bzero (p 18) (p 20) (p 1)) oneWord)),?_⟩
  intro w H v S pos fits exponent width unit blank
  let M := prime^w
  let N := M^128
  have room : M ≤ N := Nat.le_self_pow (by decide : 128 ≠ 0) M
  have digits : Nat.size 1 ≤ H := Nat.size_le.mpr ((show 1 ≤ (prime^w)^128 from pow_pos (pow_pos prime_prime.pos w) 128).trans_lt fits)
  obtain ⟨u,k,hu,hk,clocks⟩ := setupSweepClocks_exec body p w H v S exponent width unit fits
    (fun i hi => blank i (by decide +revert))
  let B := {S with R := Function.update (Function.update (Function.update (Function.update (Function.update S.R
    (p 5) (List.replicate (w*128) tick)) (p 0) ((zeros prime_prime.two_le (w*128)).map digitSymbol))
    (p 7) (List.replicate N tick)) (p 21) (List.replicate (128*H) tick)) (p 35) (binSyms H N)}
  have keep (i : Fin 37) (hi : i ∉ ([5,0,7,21,35] : List (Fin 37))) : B.R (p i) = S.R (p i) := by
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hi
    simp [B,Function.update_of_ne (p.injective.ne hi.1),Function.update_of_ne (p.injective.ne hi.2.1),
      Function.update_of_ne (p.injective.ne hi.2.2.1),Function.update_of_ne (p.injective.ne hi.2.2.2.1),
      Function.update_of_ne (p.injective.ne hi.2.2.2.2)]
  obtain ⟨y,l,hy,hl,moduli⟩ := setupSweepRadix_exec body p w H pos fits u B
    (by rwa [keep 29 (by decide)]) (by rwa [keep 10 (by decide)]) (by rwa [keep 18 (by decide)])
    (fun i hi => (keep i (by decide +revert)).trans (blank i (by decide +revert)))
  let F := {B with R := Function.update (Function.update B.R (p 36) (binSyms H M)) (p 34) (binSyms H (M : ZMod N).val)}
  have same (i : Fin 37) (hi : i ∉ ([34,36,5,0,7,21,35] : List (Fin 37))) : F.R (p i) = S.R (p i) := by
    simp only [List.mem_cons,not_or] at hi
    rw [show F.R (p i) = B.R (p i) by simp [F,Function.update_of_ne (p.injective.ne hi.1),Function.update_of_ne (p.injective.ne hi.2.1)]]
    exact keep i (by simpa only [List.mem_cons,not_or] using hi.2.2)
  obtain ⟨a,ha,zeroBits⟩ := bzero_exec body (wR := p 18) (c := p 20) (t := p 1) (by simp [List.nodup_cons])
    y F ((same 1 (by decide)).trans (blank 1 (by decide)))
  rw [same 18 (by decide),width,same 20 (by decide),blank 20 (by decide),List.append_nil] at zeroBits
  let E := {F with R := Function.update F.R (p 20) (binSyms H 0)}
  have saved (i : Fin 37) (hi : i ∉ ([20,34,36,5,0,7,21,35] : List (Fin 37))) : E.R (p i) = S.R (p i) :=
    (Function.update_of_ne (p.injective.ne (by decide +revert)) _ _).trans (same i (by decide +revert))
  obtain ⟨z,t,hz,ht,oneBit⟩ := unaryBinaryWidth_exec (body := body) (src := p 29) (width := p 18) (dst := p 33)
    (a := p 1) (h := p 2) (par := p 3) (bits := p 4) (cnt := p 6) (saved := p 8)
    (by simp [List.nodup_cons]) 1 H digits a E (by rwa [saved 29 (by decide)]) (by rwa [saved 18 (by decide)]) (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact (saved _ (by decide)).trans (blank _ (by decide)))
  refine ⟨z,_,hz.trans (ha.trans (hy.trans hu)),?_,Exec.seq clocks (Exec.seq moduli (Exec.seq zeroBits oneBit))⟩
  change k ≤ 8*w+43*N+16*H+40 at hk
  change l ≤ 45*M+18*H+36 at hl
  change _ ≤ 8*w+88*N+50*H+129
  omega

def sweepHeaderPorts : List (Fin 37) := [5,0,7,21,35,36,34,20,33]

/-- Bracket a restoring output writer with header setup and cleanup. The
overhead is linear in the number of records. -/
theorem withSweepHeaders_writes {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (p : Fin 37 ↪ Fin T) (out : Fin T) (apart : ∀ i ∈ sweepHeaderPorts, out ≠ p i)
    (writer : Pr P T Q prime U) :
    ∃ program : Pr P T Q prime U, ∀ (w H cost : ℕ) (word : List (Fin (prime+4))) (ok : Regs T prime → Prop),
    0 < w → (prime^w)^128 < 2^H → H ≤ (prime^w)^128+1 →
    Cover.LabelTraversal.Writes body ok out writer word cost →
    Cover.LabelTraversal.Writes body (fun R => (R (p 10)).length = w ∧ (R (p 18)).length = H ∧
      (R (p 29)).length = 1 ∧
      (∀ i ∈ ([0,1,2,3,4,5,6,7,8,20,21,23,33,34,35,36] : List (Fin 37)), R (p i) = []) ∧
      ok ((sweepHeaderWords w H).foldl (fun B kv => Function.update B (p kv.1) kv.2) R))
      out program word (cost+1500*((prime^w)^128)) := by
  obtain ⟨setup,prepare⟩ := sweepHeaders_exec body p
  let ports := sweepHeaderPorts.map p
  refine ⟨.seq setup (.seq writer (Mult.ShortConv.clearWords ports)),?_⟩
  intro w H cost word ok pos fits field write v S ⟨exponent,bits,unit,blank,ready⟩
  obtain ⟨u,k,hu,hk,init⟩ := prepare w H v S pos fits exponent bits unit blank
  let B := {S with R := (sweepHeaderWords w H).foldl (fun R (kv : Fin 37 × List (Fin (prime+4))) => Function.update R (p kv.1) kv.2) S.R}
  have keep (j : Fin T) (off : j ∉ ports) : B.R j = S.R j := by
    simp only [ports,sweepHeaderPorts,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false,not_or] at off
    obtain ⟨a,b,c,d,e,f,g,h,l⟩ := off
    simp [B,sweepHeaderWords,a,b,c,d,e,f,g,h,l]
  have external : out ∉ ports := by
    intro eqn
    obtain ⟨i,mem,eqn⟩ := List.mem_map.mp eqn
    exact apart i mem eqn.symm
  obtain ⟨y,l,hy,hl,run⟩ := write u B ready
  rw [keep out external] at run
  let F := {B with R := Function.update B.R out (word ++ S.R out)}
  obtain ⟨z,hz,clear⟩ := Mult.ShortConv.clearWords_exec (body := body) ports
    (List.Nodup.map p.injective (by decide : sweepHeaderPorts.Nodup)) y F
  have lengthAt (i : Fin 37) (hi : i ∈ sweepHeaderPorts) :
      (F.R (p i)).length = (B.R (p i)).length := congrArg List.length (Function.update_of_ne (apart i hi).symm _ _)
  have sum : (ports.map fun j => (F.R j).length).sum = 256*w+(prime^w)^128+133*H := by
    have eqn : ports.map (fun j => (F.R j).length) = ports.map (fun j => (B.R j).length) := by
      apply List.map_congr_left
      intro j hj
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hj
      exact lengthAt i hi
    rw [eqn]
    simp [ports,sweepHeaderPorts,B,sweepHeaderWords,length_binSyms] <;> ring
  have final : {F with R := fun j => if j ∈ ports then [] else F.R j} =
      {S with R := Function.update S.R out (word ++ S.R out)} := by
    congr 1
    funext j
    by_cases h : j ∈ ports
    · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp h
      rw [if_pos h,Function.update_of_ne (apart i hi).symm]
      exact (blank i (by clear * - hi; decide +revert)).symm
    · rw [if_neg h]
      by_cases eqn : j = out <;> simp [F,Function.update_apply,eqn,keep j h]
  rw [final,sum,show ports.length = 9 by simp [ports,sweepHeaderPorts]] at clear
  have wn : w ≤ (prime^w)^128 := ((Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_left prime_prime.two_le w))).trans
    (Nat.le_self_pow (by decide : 128 ≠ 0) _)
  have positive := pow_pos (pow_pos prime_prime.pos w) 128
  exact ⟨z,_,hz.trans (hy.trans hu),by omega,Exec.seq init (Exec.seq run clear)⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
