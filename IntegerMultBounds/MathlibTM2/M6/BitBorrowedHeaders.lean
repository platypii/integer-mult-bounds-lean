module

public import IntegerMultBounds.MathlibTM2.M6.BitHelperParentSeeds

/-! Prepare adjacent digit exchanges with the borrowed label inside the trailing record. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Shared50ModularControl (prime)
open FlatCoordinateSchedule (bits)

def borrowedArchiveBank (i : Fin 127) : Fin 12 ↪ Fin 268 where
  toFun k := ⟨if k.val = 3 then 14+2*i.val else if k.val = 4 then 15+2*i.val
    else if k.val = 2 then 13 else k.val,by split_ifs <;> omega⟩
  inj' := by intro k l eq; apply Fin.ext; have h := congrArg Fin.val eq; dsimp at h; split_ifs at h <;> omega

/-- Register 13 already contains the product of the label count and the
trailing length. Use it as the suffix for every swap and register 1 as the gap. -/
theorem borrowedArchive_exec {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (bank : Fin 268 ↪ Fin T) (w L W : ℕ) (u : HS T Q prime U) (S : Stacks T prime)
    (seed : ∀ k, S.R (bank k) = helperArchiveSeed w L W k) :
    let ports := fun i => (borrowedArchiveBank i).trans bank
    let headers := fun i => helperHeaderPorts i (bank 1) (bank 3) (bank 1) (ports i 3) (ports i 4)
    ∃ z F t, z.user = u.user ∧ Exec body (helperHeaderSweep ports (List.finRange 127)) (mk u S) t (mk z F) ∧
      t ≤ ((List.finRange 127).map (helperHeaderTime w 1 (L*W))).sum+1 ∧ F.L = S.L ∧
      (∀ i j, F.R (headers i j) = (Routines.hdr (helperAdjacentView w 1 (L*W) i) j).map bitSymbol) ∧
      ∀ p, (∀ k, bank k ≠ p) → F.R p = S.R p := by
  intro ports headers
  have apart (i j : Fin 127) (hne : i ≠ j) (k : Fin 12) :
      ports j k ≠ ports i 3 ∧ ports j k ≠ ports i 4 := by
    have ne : i.val ≠ j.val := fun h => hne (Fin.ext h)
    constructor <;> intro eq <;> have h := congrArg Fin.val (bank.injective eq)
    all_goals simp only [borrowedArchiveBank,Function.Embedding.coeFn_mk] at h; split_ifs at h <;> omega
  obtain ⟨z,F,t,user,run,time,left,filled,off⟩ := helperHeaderSweep_exec body ports apart
    w 1 (L*W) (List.finRange 127) (List.nodup_finRange _) u S (by
      intro i _
      simp only [ports,Function.Embedding.trans_apply,seed,ite_self,one_mul]
      refine ⟨rfl,rfl,rfl,?_⟩
      intro k hk
      simp only [borrowedArchiveBank,Function.Embedding.coeFn_mk,helperArchiveSeed]
      split_ifs <;> first | rfl | omega)
  have retained (k : Fin 268) (low : k.val < 14) : F.R (bank k) = helperArchiveSeed w L W k := by
    rw [← seed]
    apply off
    intro i _
    constructor <;> intro eq <;> have h := congrArg Fin.val (bank.injective eq)
    all_goals simp [borrowedArchiveBank] at h; omega
  refine ⟨z,F,t,user,run,time,left,?_,fun p hp => off p (fun i _ => ⟨(hp _).symm,(hp _).symm⟩)⟩
  intro i j
  have unit : F.R (bank 1) = (bits 1).map bitSymbol := by rw [retained 1 (by decide),canonicalBits_symbols]; rfl
  have width : F.R (bank 3) = (bits w).map bitSymbol := by rw [retained 3 (by decide)]; rfl
  obtain ⟨pre,post⟩ := filled i (List.mem_finRange i)
  fin_cases j <;> first | exact unit | exact width | exact pre | exact post | skip
  simpa [headers,helperHeaderPorts,helperAdjacentView,Routines.hdr,RecursiveDimensionBank.values] using unit

def borrowedHeaders (T : ℕ) (i : Fin 127) : Fin 6 → Fin (T+273) :=
  let bank := parentArchive T
  helperHeaderPorts i (bank 1) (bank 3) (bank 1) (bank (borrowedArchiveBank i 3)) (bank (borrowedArchiveBank i 4))

theorem borrowedHeaders_apart {T : ℕ} (i : Fin 127) (j : Fin 6) (k : Fin T) :
    borrowedHeaders T i j ≠ k.castAdd 273 := by
  have apart (a : Fin 268) : parentArchive T a ≠ k.castAdd 273 := by
    intro eq
    have h := congrArg Fin.val eq
    change T+a.val = k.val at h
    omega
  fin_cases j <;> simpa [borrowedHeaders,helperHeaderPorts] using apart _

theorem prepareBorrowedHeaders_exec {T Q : ℕ} {P U : Type} (body : P → Pr P (T+273) Q prime U) (hdr : Fin 6 → Fin T)
    (regs : Fin 35 ↪ Fin T) (v : RecursiveInterchangeLayout.Descriptor) (w : ℕ)
    (pos : v.Positive) (u : HS (T+273) Q prime U) (S : Stacks (T+273) prime) :
    let W := v.beforeRows*v.rows*v.between*v.afterD
    let M := prime^(w+1)
    let V := M^128*(v.beforeH*W)
    let read := fun (k : Fin T) => S.R (k.castAdd 273)
    read (regs 2) = binSyms M.size M → read (regs 28) = binSyms 1 1 →
    (read (regs 33)).length = w →
    (∀ i, read (hdr i) = (M8.RevMachine.Routines.hdr v i).map bitSymbol) →
    (∀ j : Fin 273, S.L (j.natAdd T) = [] ∧ S.R (j.natAdd T) = []) →
    ∃ z F t, z.user = u.user ∧ Exec body (.seq (prepareHelperSeeds hdr regs) (helperHeaderSweep (fun i => (borrowedArchiveBank i).trans (parentArchive T)) (List.finRange 127))) (mk u S) t (mk z F) ∧
      t ≤ 152402000*V ∧
      (∀ i j, F.R (borrowedHeaders T i j) =
        (M8.RevMachine.Routines.hdr (helperAdjacentView (w+1) 1 (v.beforeH*W) i) j).map bitSymbol) ∧
      F.L = S.L ∧ ∀ k : Fin T, F.R (k.castAdd 273) = read k := by
  intro W M V read base unit clock words free
  obtain ⟨y,D,m,same,seed,charge,filled,dl,dr⟩ := prepareHelperSeeds_linear body hdr regs v w pos u S base unit clock words free
  obtain ⟨z,F,n,user,sweep,price,fl,ready,off⟩ := borrowedArchive_exec body (parentArchive T) (w+1) v.beforeH W y D filled
  have wp : 0 < W := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos pos.1 pos.2.1) pos.2.2.2.1) pos.2.2.2.2
  have bounded := price.trans (helperArchiveTime_le (w+1) 1 (v.beforeH*W) Nat.zero_lt_one (Nat.mul_pos pos.2.2.1 wp))
  refine ⟨z,F,m+n,user.trans same,Exec.seq seed sweep,?_,ready,fl.trans dl,?_⟩
  · simp only [one_mul] at bounded
    change n ≤ (127*1200000+1)*V at bounded
    change m ≤ 1999*V at charge
    omega
  · intro k
    apply (off _ ?_).trans (dr k)
    intro j e
    have h := congrArg Fin.val e
    change T+j.val = k.val at h
    omega

end IntegerMultBounds.MathlibTM2.M6.BitNode
