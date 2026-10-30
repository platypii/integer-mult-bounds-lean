module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Node

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

/-- Successive products borrow one base master and the preceding chain word. -/
def unaryPowerChain (base src tmp saved : Fin T) : List (Fin T) → Pr P T Q A U
  | [] => .act .done
  | dst::ds => .seq (unaryProduct base src dst tmp saved) (unaryPowerChain base dst tmp saved ds)

def unaryPowerChainR (K n : ℕ) : List (Fin T) → Regs T A → Regs T A
  | [],R => R
  | dst::ds,R => unaryPowerChainR K (n*K) ds (Function.update R dst (List.replicate (n*K) tick))

def unaryPowerChainCost (K n : ℕ) : ℕ → ℕ
  | 0 => 1
  | m+1 => (K*(4*n+9)+4)+unaryPowerChainCost K (n*K) m

def unaryPowerChainVolume (K n : ℕ) : ℕ → ℕ
  | 0 => 0
  | m+1 => n*K+unaryPowerChainVolume K (n*K) m

/-- The exact geometric volume controls generation cost linearly. -/
theorem unaryPowerChainCost_eq (K n m : ℕ) :
    unaryPowerChainCost K n m = 4*unaryPowerChainVolume K n m+(9*K+4)*m+1 := by
  induction m generalizing n with
  | zero => simp [unaryPowerChainCost,unaryPowerChainVolume]
  | succ m ih =>
    simp only [unaryPowerChainCost,unaryPowerChainVolume,ih]
    ring

theorem unaryPowerChainVolume_le {K : ℕ} (hK : 1 ≤ K) (n m : ℕ) :
    unaryPowerChainVolume K n m ≤ m*(n*K^m) := by
  induction m generalizing n with
  | zero => simp [unaryPowerChainVolume]
  | succ m ih =>
    have hh : n*K ≤ n*K*K^m := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left (n*K) (Nat.one_le_pow m K hK)
    have ht := ih (n*K)
    simp only [unaryPowerChainVolume,pow_succ]
    nlinarith only [hh,ht]

theorem unaryPowerChainCost_le {K : ℕ} (hK : 1 ≤ K) (n m : ℕ) :
    unaryPowerChainCost K n m ≤ m*(4*n*K^m+9*K+4)+1 := by
  rw [unaryPowerChainCost_eq]
  have hh := unaryPowerChainVolume_le hK n m
  nlinarith only [hh]

theorem unaryPowerChainR_off (K n : ℕ) (ds : List (Fin T)) (R : Regs T A) (i : Fin T)
    (hi : ∀ dst ∈ ds, dst ≠ i) : unaryPowerChainR K n ds R i = R i := by
  induction ds generalizing n R with
  | nil => rfl
  | cons dst ds ih =>
    rw [unaryPowerChainR,ih _ _ (by intro j hj; exact hi j (by simp [hj]))]
    exact Function.update_of_ne (hi dst (by simp)).symm _ _

theorem unaryPowerChainR_update_off (K n : ℕ) (ds : List (Fin T)) (R : Regs T A)
    (i : Fin T) (word : List (Fin (A+4))) (hi : i ∉ ds) :
    unaryPowerChainR K n ds (Function.update R i word) =
      Function.update (unaryPowerChainR K n ds R) i word := by
  induction ds generalizing n R with
  | nil => rfl
  | cons dst ds ih =>
    have hne : i ≠ dst := by intro he; exact hi (by simp [he])
    simp only [unaryPowerChainR]
    rw [Function.update_comm hne,ih _ _ (by intro hh; exact hi (by simp [hh]))]

theorem unaryPowerChainR_get (K n : ℕ) (ds : List (Fin T)) (hnd : ds.Nodup)
    (R : Regs T A) (i : ℕ) (hi : i < ds.length) :
    unaryPowerChainR K n ds R ds[i] = List.replicate (n*K^(i+1)) tick := by
  induction ds generalizing n R i with
  | nil => simp at hi
  | cons dst ds ih =>
    obtain ⟨hoff,hnd⟩ := List.nodup_cons.mp hnd
    cases i with
    | zero =>
      rw [List.getElem_cons_zero,unaryPowerChainR,unaryPowerChainR_off K (n*K) ds _ dst (by
        intro j hj he; exact hoff (he ▸ hj))]
      simp
    | succ i =>
      have hi' : i < ds.length := by simpa using hi
      simpa only [unaryPowerChainR,List.getElem_cons_succ,pow_succ,Nat.mul_assoc,
        Nat.mul_comm,Nat.mul_left_comm] using
        ih (n*K) hnd (Function.update R dst (List.replicate (n*K) tick)) i hi'


/-- Include the borrowed seed as power zero when reading a generated bank. -/
theorem unaryPowerChainR_seed_length (K n : ℕ) (seed : Fin T) (ds : List (Fin T))
    (hnd : ds.Nodup) (hseed : seed ∉ ds) (R : Regs T A) (hlen : (R seed).length = n)
    (i : ℕ) (hi : i < (seed::ds).length) :
    (unaryPowerChainR K n ds R (seed::ds)[i]).length = n*K^i := by
  cases i with
  | zero =>
    rw [List.getElem_cons_zero,unaryPowerChainR_off K n ds R seed (by
      intro j hj he; exact hseed (he ▸ hj)),hlen]
    simp
  | succ i =>
    have hi' : i < ds.length := by simpa using hi
    rw [List.getElem_cons_succ,unaryPowerChainR_get K n ds hnd R i hi',List.length_replicate]


theorem unaryPowerChainR_volume (K n : ℕ) (ds : List (Fin T)) (hnd : ds.Nodup)
    (R : Regs T A) :
    (ds.map (fun dst => (unaryPowerChainR K n ds R dst).length)).sum =
      unaryPowerChainVolume K n ds.length := by
  induction ds generalizing n R with
  | nil => rfl
  | cons dst ds ih =>
    have hhead : unaryPowerChainR K n (dst::ds) R dst = List.replicate (n*K) tick := by
      rw [unaryPowerChainR,unaryPowerChainR_off K (n*K) ds _ dst (by
        intro j hj he
        exact (List.nodup_cons.mp hnd).1 (he ▸ hj))]
      exact Function.update_self _ _ _
    simp only [List.map_cons,List.sum_cons,hhead,List.length_replicate,List.length_cons,unaryPowerChainVolume]
    exact congrArg (fun z => n*K+z) (ih (n*K) (List.nodup_cons.mp hnd).2 _)

/-- Erase exactly the owned power chain and restore the original register file. -/
theorem unaryPowerChain_release_exec (K n : ℕ) (ds : List (Fin T)) (hnd : ds.Nodup)
    (v : HS T Q A U) (S : Stacks T A) (hblank : ∀ dst ∈ ds, S.R dst = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (clearWords ds) (mk v {S with R := unaryPowerChainR K n ds S.R})
        (2*unaryPowerChainVolume K n ds.length+2*ds.length+1) (mk v' S) := by
  obtain ⟨v',hu,he⟩ := clearWords_exec (body := body) ds hnd v {S with R := unaryPowerChainR K n ds S.R}
  refine ⟨v',hu,he.cast (by rw [unaryPowerChainR_volume K n ds hnd]) ?_⟩
  apply congrArg (mk v')
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases hi : i ∈ ds
  · simp only [hi,ite_true]
    exact (hblank i hi).symm
  · simp only [hi,ite_false]
    exact unaryPowerChainR_off K n ds S.R i (by intro j hj he; exact hi (he ▸ hj))

/-- The full chain is proved once, not by separate concrete power cases. -/
theorem unaryPowerChain_exec (base src tmp saved : Fin T) (ds : List (Fin T))
    (hnd : ([base,tmp,saved,src]++ds).Nodup) (K n : ℕ)
    (v : HS T Q A U) (S : Stacks T A)
    (hbase : (S.R base).length = K) (hsrc : (S.R src).length = n)
    (hblank : ∀ dst ∈ ds, S.R dst = []) (htmp : S.R tmp = []) (hsaved : S.R saved = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ unaryPowerChainCost K n ds.length ∧
      Exec body (unaryPowerChain base src tmp saved ds) (mk v S) m
        (mk v' {S with R := unaryPowerChainR K n ds S.R}) := by
  induction ds generalizing src n v S with
  | nil =>
    exact ⟨v,1,rfl,by rfl,by simpa [unaryPowerChain,unaryPowerChainR] using Exec.act (body := body) .done (mk v S)⟩
  | cons dst ds ih =>
    have hreg : [base,src,dst,tmp,saved].Nodup := by
      simp only [List.cons_append,List.nil_append,List.nodup_cons,List.mem_cons,List.not_mem_nil,
        or_false,not_or] at hnd ⊢
      aesop
    have hnext : ([base,tmp,saved,dst]++ds).Nodup := by
      simp only [List.cons_append,List.nil_append,List.nodup_cons,List.mem_cons,List.not_mem_nil,
        or_false,not_or] at hnd ⊢
      aesop
    have hdst : dst ≠ base ∧ dst ≠ tmp ∧ dst ≠ saved := by
      simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hreg
      aesop
    obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := unaryProduct_exec (body := body) hreg v S htmp hsaved
    let M : Stacks T A := {S with R := Function.update S.R dst (List.replicate (n*K) tick)}
    have he₁' : Exec body (unaryProduct base src dst tmp saved) (mk v S) m₁ (mk v₁ M) := by
      simpa only [M,hbase,hsrc,hblank dst (by simp),List.append_nil,Nat.mul_comm] using he₁
    obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := ih dst hnext (n*K) v₁ M
      (by simpa only [M,Function.update_of_ne hdst.1.symm] using hbase)
      (by simp [M])
      (by
        intro j hj
        have hjd : j ≠ dst := by
          have hn : (dst::ds).Nodup := hnd.of_append_right
          intro he
          exact (List.nodup_cons.mp hn).1 (he ▸ hj)
        simpa only [M,Function.update_of_ne hjd] using hblank j (by simp [hj]))
      (by simpa only [M,Function.update_of_ne hdst.2.1.symm] using htmp)
      (by simpa only [M,Function.update_of_ne hdst.2.2.symm] using hsaved)
    refine ⟨v₂,m₁+m₂,hu₂.trans hu₁,?_,Exec.seq he₁' he₂⟩
    simp only [hbase,hsrc] at hm₁
    exact Nat.add_le_add hm₁ hm₂

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
