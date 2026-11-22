module

public import IntegerMultBounds.MathlibTM2.M6.BitHelperLabelRun

/-! Generate the two position-dependent powers in the PR589 packing headers. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open Shared50ModularControl (prime)
open FlatCoordinateSchedule (bits)
variable {T Q : ℕ} {P U : Type}

/-- Both power computations share their base and scratch. Their seeds and
outputs are separate so the prefix remains available after computing the suffix. -/
def helperPrefixPower : Fin 10 ↪ Fin 12 := ⟨![0,1,3,5,6,7,8,9,10,11],by decide⟩
def helperSuffixPower : Fin 10 ↪ Fin 12 := ⟨![0,2,4,5,6,7,8,9,10,11],by decide⟩

noncomputable def helperPowerHeaders (r : Fin 12 ↪ Fin T) (i : Fin 127) : Pr P T Q prime U :=
  .seq (swapPrefix (helperPrefixPower.trans r) i.val)
    (swapPrefix (helperSuffixPower.trans r) (126-i.val))

theorem helperPowerHeaders_exec (body : P → Pr P T Q prime U) (r : Fin 12 ↪ Fin T)
    (i : Fin 127) (w L W H J K : ℕ) (u : HS T Q prime U) (S : Stacks T prime) :
    let M := prime^w
    let a := if 16 ≤ i.val then L else 1
    let b := (if i.val < 15 then L else 1)*W
    let v := helperAdjacentView w L W i
    M < 2^H → a < 2^J → b < 2^K →
    S.R (r 0) = binSyms H M → S.R (r 1) = binSyms J a → S.R (r 2) = binSyms K b →
    (∀ k : Fin 12, 3 ≤ k.val → S.R (r k) = []) →
    ∃ z t, z.user = u.user ∧
      t ≤ dimensionTime H J i.val + (4*(i.val*H+J)+6) +
        (dimensionTime H K (126-i.val) + (4*((126-i.val)*H+K)+6)) ∧
      Exec body (helperPowerHeaders r i) (mk u S) t (mk z
        {S with R := Function.update (Function.update S.R (r 3) ((bits v.beforeH).map bitSymbol)) (r 4) ((bits v.afterD).map bitSymbol)}) := by
  intro M a b v hm ha hb base seedA seedB free
  obtain ⟨y,k,user,time,pre⟩ := scaledPrefix_exec body (helperPrefixPower.trans r) i.val H J M a
    hm ha u S base seedA (fun j lo hi => free (helperPrefixPower j) (by
      have : ∀ t : Fin 10, 2 ≤ t → t < 9 → 3 ≤ (helperPrefixPower t).val := by decide
      exact this j lo hi))
  let D := {S with R := Function.update S.R (r 3) ((bits v.beforeH).map bitSymbol)}
  change Exec body _ _ k (mk y D) at pre
  have keep (j : Fin 12) (ne : j ≠ 3) : D.R (r j) = S.R (r j) :=
    Function.update_of_ne (r.injective.ne ne) _ _
  obtain ⟨z,m,same,price,post⟩ := scaledPrefix_exec body (helperSuffixPower.trans r) (126-i.val) H K M b
    hm hb y D ((keep 0 (by decide)).trans base) ((keep 2 (by decide)).trans seedB) (fun j lo hi => by
      have facts : ∀ t : Fin 10, 2 ≤ t → t < 9 → helperSuffixPower t ≠ 3 ∧ 3 ≤ (helperSuffixPower t).val := by decide
      obtain ⟨ne,high⟩ := facts j lo hi
      exact (keep _ ne).trans (free _ high))
  have suffix : M^(126-i.val)*b = v.afterD := (Nat.mul_assoc ..).symm
  rw [suffix] at post
  exact ⟨z,k+m,same.trans user,Nat.add_le_add time price,Exec.seq pre post⟩

/-- The four remaining fields are aliases of existing canonical words. Only
the two powers require new output registers. -/
def helperHeaderPorts (i : Fin 127) (one width label pre post : Fin T) : Fin 6 → Fin T :=
  ![one,one,pre,width,if i.val = 15 then label else one,post]

theorem helperHeaderPorts_ready (r : Fin 12 ↪ Fin T) (i : Fin 127) (one width label : Fin T)
    (apart : ∀ t ∈ [one,width,label], t ≠ r 3 ∧ t ≠ r 4) (w L W : ℕ) (S : Stacks T prime)
    (unit : S.R one = (bits 1).map bitSymbol) (clock : S.R width = (bits w).map bitSymbol)
    (labels : S.R label = (bits L).map bitSymbol) :
    let v := helperAdjacentView w L W i
    let R := Function.update (Function.update S.R (r 3) ((bits v.beforeH).map bitSymbol)) (r 4) ((bits v.afterD).map bitSymbol)
    ∀ j, R (helperHeaderPorts i one width label (r 3) (r 4) j) = (M8.RevMachine.Routines.hdr v j).map bitSymbol := by
  intro v R
  have keep (t) (ht : t ∈ [one,width,label]) : R t = S.R t := by
    obtain ⟨a,b⟩ := apart t ht
    simp only [R,Function.update_of_ne b,Function.update_of_ne a]
  have u := (keep one (by simp)).trans unit
  have c := (keep width (by simp)).trans clock
  have l := (keep label (by simp)).trans labels
  have pre : R (r 3) = (bits v.beforeH).map bitSymbol := by simp [R,r.injective.eq_iff]
  have post : R (r 4) = (bits v.afterD).map bitSymbol := by simp [R]
  intro j
  fin_cases j <;> first | exact u | exact pre | exact c | exact post | skip
  change R (if i.val = 15 then label else one) = (bits (if i.val = 15 then L else 1)).map bitSymbol
  split <;> assumption

/-- The archive contains one shared arithmetic workspace, two alternative seed
registers, and one pair of stored powers for each adjacent position. -/
def helperArchivePort (i : Fin 127) (k : Fin 12) : Fin 268 :=
  ⟨if k.val = 3 then 14+2*i.val else if k.val = 4 then 15+2*i.val
   else if k.val = 1 ∧ 16 ≤ i.val then 12 else if k.val = 2 ∧ i.val < 15 then 13 else k.val,
   by split_ifs <;> omega⟩

def helperArchiveBank (i : Fin 127) : Fin 12 ↪ Fin 268 where
  toFun := helperArchivePort i
  inj' := by
    intro k l eq
    have h := congrArg Fin.val eq
    simp only [helperArchivePort] at h
    apply Fin.ext
    split_ifs at h <;> omega

theorem helperArchiveBank_apart (i j : Fin 127) (distinct : i ≠ j) (k : Fin 12) :
    helperArchiveBank j k ≠ helperArchiveBank i 3 ∧ helperArchiveBank j k ≠ helperArchiveBank i 4 := by
  have ne : i.val ≠ j.val := fun h => distinct (Fin.ext h)
  constructor <;> intro eq <;> have h := congrArg Fin.val eq
  all_goals
    change (helperArchivePort j k).val = _ at h
    simp only [helperArchiveBank,Function.Embedding.coeFn_mk,helperArchivePort] at h
    norm_num at h
    split_ifs at h <;> omega

noncomputable def helperHeaderSweep (ports : Fin 127 → Fin 12 ↪ Fin T) :
    List (Fin 127) → Pr P T Q prime U
  | [] => .act .done
  | i::is => .seq (helperPowerHeaders (ports i) i) (helperHeaderSweep ports is)

noncomputable def helperHeaderTime (w L W : ℕ) (i : Fin 127) : ℕ :=
  let H := (prime^w).size
  let J := (if 16 ≤ i.val then L else 1).size
  let K := ((if i.val < 15 then L else 1)*W).size
  dimensionTime H J i.val + (4*(i.val*H+J)+6) +
    (dimensionTime H K (126-i.val) + (4*((126-i.val)*H+K)+6))

/-- Generate each distinct header pair once. Different positions can share input
and scratch tapes; only their two output tapes are reserved. -/
theorem helperHeaderSweep_exec (body : P → Pr P T Q prime U) (ports : Fin 127 → Fin 12 ↪ Fin T)
    (apart : ∀ i j, i ≠ j → ∀ k, ports j k ≠ ports i 3 ∧ ports j k ≠ ports i 4)
    (w L W : ℕ) (is : List (Fin 127)) (unique : is.Nodup) :
    let M := prime^w
    let a := fun i : Fin 127 => if 16 ≤ i.val then L else 1
    let b := fun i : Fin 127 => (if i.val < 15 then L else 1)*W
    let cost := helperHeaderTime w L W
    ∀ (u : HS T Q prime U) (S : Stacks T prime),
      (∀ i ∈ is, S.R (ports i 0) = binSyms M.size M ∧
        S.R (ports i 1) = binSyms (a i).size (a i) ∧ S.R (ports i 2) = binSyms (b i).size (b i) ∧
        ∀ k : Fin 12, 3 ≤ k.val → S.R (ports i k) = []) →
      ∃ z F t, z.user = u.user ∧ Exec body (helperHeaderSweep ports is) (mk u S) t (mk z F) ∧
        t ≤ (is.map cost).sum+1 ∧ F.L = S.L ∧
        (∀ i ∈ is, let v := helperAdjacentView w L W i
          F.R (ports i 3) = (bits v.beforeH).map bitSymbol ∧ F.R (ports i 4) = (bits v.afterD).map bitSymbol) ∧
        ∀ p, (∀ i ∈ is, p ≠ ports i 3 ∧ p ≠ ports i 4) → F.R p = S.R p := by
  intro M a b cost
  induction is with
  | nil =>
    intro u S _
    exact ⟨u,S,1,rfl,Exec.act ..,by simp,rfl,by simp,fun _ _ => rfl⟩
  | cons i is ih =>
    intro u S ready
    obtain ⟨base,preSeed,postSeed,free⟩ := ready i (by simp)
    let v := helperAdjacentView w L W i
    let D := {S with R := Function.update (Function.update S.R (ports i 3)
      ((bits v.beforeH).map bitSymbol)) (ports i 4) ((bits v.afterD).map bitSymbol)}
    obtain ⟨y,k,user,paid,run⟩ := helperPowerHeaders_exec body (ports i) i w L W _ _ _ u S
      (Nat.lt_size_self M) (Nat.lt_size_self (a i)) (Nat.lt_size_self (b i)) base preSeed postSeed free
    have keep (p) (ne : p ≠ ports i 3 ∧ p ≠ ports i 4) : D.R p = S.R p := by
      simp only [D,Function.update_of_ne ne.2,Function.update_of_ne ne.1]
    have other (j) (hj : j ∈ is) : i ≠ j := fun e => unique.notMem (e ▸ hj)
    have next (j) (hj : j ∈ is) (k) := keep _ (apart i j (other j hj) k)
    obtain ⟨z,F,m,same,rest,bill,left,filled,off⟩ := ih unique.of_cons y D (fun j hj => by
      simpa only [next j hj] using ready j (List.mem_cons_of_mem _ hj))
    refine ⟨z,F,k+m,same.trans user,Exec.seq run rest,?_,left,?_,?_⟩
    · change k ≤ cost i at paid
      simp only [List.map_cons,List.sum_cons]
      omega
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | inside
      · have saved (l) := off (ports j l) (fun h hh => apart h j (other h hh).symm l)
        rw [saved,saved]
        simp [D,(ports j).injective.eq_iff,v]
      · exact filled j inside
    · intro p unused
      exact (off p (fun j hj => unused j (List.mem_cons_of_mem _ hj))).trans (keep p (unused i (by simp)))

/-- Six canonical seed words suffice for the archive: radix, one, exterior
volume, width, label size, and label size times exterior volume. -/
noncomputable def helperArchiveSeed (w L W : ℕ) (k : Fin 268) : List (Fin (prime+4)) :=
  if k.val = 0 then binSyms (prime^w).size (prime^w)
  else if k.val = 1 then binSyms 1 1
  else if k.val = 2 then binSyms W.size W
  else if k.val = 3 then (bits w).map bitSymbol
  else if k.val = 12 then binSyms L.size L
  else if k.val = 13 then binSyms (L*W).size (L*W)
  else []

theorem helperArchiveSeed_inputs (w L W : ℕ) (i : Fin 127) :
    let get := fun k => helperArchiveSeed w L W (helperArchiveBank i k)
    let a := if 16 ≤ i.val then L else 1
    let b := (if i.val < 15 then L else 1)*W
    get 0 = binSyms (prime^w).size (prime^w) ∧ get 1 = binSyms a.size a ∧
      get 2 = binSyms b.size b ∧ ∀ k : Fin 12, 3 ≤ k.val → get k = [] := by
  intro get a b
  have high : ∀ k : Fin 12, 3 ≤ k.val → get k = [] := by
    intro k hk
    simp only [get,helperArchiveSeed,helperArchiveBank,Function.Embedding.coeFn_mk,helperArchivePort]
    split_ifs <;> first | rfl | omega
  refine ⟨rfl,?_,?_,high⟩
  · by_cases h : 16 ≤ i.val <;> simp [get,a,helperArchiveBank,helperArchivePort,helperArchiveSeed,h]
  · by_cases h : i.val < 15 <;> simp [get,b,helperArchiveBank,helperArchivePort,helperArchiveSeed,h]

/-- From the six seeds, install every header read by the slot program on a
caller-selected archive. Both stacks outside that archive retain their contents. -/
theorem helperArchive_exec (body : P → Pr P T Q prime U) (bank : Fin 268 ↪ Fin T)
    (w L W : ℕ) (u : HS T Q prime U) (S : Stacks T prime)
    (seed : ∀ k, S.R (bank k) = helperArchiveSeed w L W k) :
    let ports := fun i => (helperArchiveBank i).trans bank
    let headers := fun i => helperHeaderPorts i (bank 1) (bank 3) (bank 12) (ports i 3) (ports i 4)
    ∃ z F t, z.user = u.user ∧ Exec body (helperHeaderSweep ports (List.finRange 127)) (mk u S) t (mk z F) ∧
      t ≤ ((List.finRange 127).map (helperHeaderTime w L W)).sum+1 ∧ F.L = S.L ∧
      (∀ i j, F.R (headers i j) = (M8.RevMachine.Routines.hdr (helperAdjacentView w L W i) j).map bitSymbol) ∧
      ∀ p, (∀ k, bank k ≠ p) → F.R p = S.R p := by
  intro ports headers
  have apart (i j : Fin 127) (ne : i ≠ j) (k : Fin 12) :=
    helperArchiveBank_apart i j ne k
  obtain ⟨z,F,t,user,run,time,left,filled,off⟩ := helperHeaderSweep_exec body ports
    (fun i j ne k => ⟨bank.injective.ne (apart i j ne k).1,bank.injective.ne (apart i j ne k).2⟩)
    w L W (List.finRange 127) (List.nodup_finRange _) u S (fun i _ => by
      simpa only [ports,Function.Embedding.trans_apply,seed] using helperArchiveSeed_inputs w L W i)
  have retained (k : Fin 268) (low : k.val < 14) : F.R (bank k) = helperArchiveSeed w L W k := by
    rw [← seed]
    apply off
    intro i _
    constructor <;> apply bank.injective.ne <;> intro eq <;> have h := congrArg Fin.val eq
    all_goals simp [helperArchiveBank,helperArchivePort] at h; omega
  refine ⟨z,F,t,user,run,time,left,?_,fun p hp => off p (fun i _ => ⟨(hp _).symm,(hp _).symm⟩)⟩
  intro i j
  have unit : F.R (bank 1) = (bits 1).map bitSymbol := by
    rw [retained 1 (by decide),canonicalBits_symbols]; rfl
  have width : F.R (bank 3) = (bits w).map bitSymbol := by rw [retained 3 (by decide)]; rfl
  have label : F.R (bank 12) = (bits L).map bitSymbol := by
    rw [retained 12 (by decide),canonicalBits_symbols]; rfl
  obtain ⟨pre,post⟩ := filled i (List.mem_finRange i)
  fin_cases j <;> first | exact unit | exact width | exact pre | exact post | skip
  change F.R (if i.val = 15 then bank 12 else bank 1) = (bits (if i.val = 15 then L else 1)).map bitSymbol
  split <;> assumption

local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

/-- Prepare the archive and run a slot change on the same physical owner.
The program depends only on the slot change and the caller's register layout. -/
theorem preparedHelperSlot_exec [M8.Machine.Net] (src dst : Option (Fin 56))
    (capacity : columnCapacity ≤ Q) (body : P → Pr P (T+M8.RevMachine.LeafCore.small) Q prime U)
    (bank : Fin 268 ↪ Fin T) (owner : Fin T) (apart : ∀ k, bank k ≠ owner) :
    ∃ (code : Pr P (T+M8.RevMachine.LeafCore.small) Q prime U) (C : ℝ),
    ∀ {w L W : ℕ} {v : RecursiveInterchangeLayout.Descriptor},
      RecursiveInterchangeLayout.volume prime v = (prime^w)^16*(L*((prime^w)^112*W)) →
      0 < RecursiveInterchangeLayout.volume prime v →
      ∀ (word : Fin (RecursiveInterchangeLayout.volume prime v) → ZMod 2) u S,
      (∀ k, S.R ((bank k).castAdd M8.RevMachine.LeafCore.small) = helperArchiveSeed w L W k) →
      RecordPayload (owner.castAdd M8.RevMachine.LeafCore.small) (fun _ => blank) 0 word S →
      (∀ j : Fin M8.RevMachine.LeafCore.small, S.L (j.natAdd T) = [] ∧ S.R (j.natAdd T) = []) →
      ∃ z F t, ∃ out : Fin (RecursiveInterchangeLayout.volume prime v) → ZMod 2,
        z.user = u.user ∧ Exec body code (mk u S) t (mk z F) ∧
        (t : ℝ) ≤ (((List.finRange 127).map (helperHeaderTime w L W)).sum+1 : ℕ) +
          C*((RecursiveInterchangeLayout.volume prime v : ℝ)*((max 1 w : ℕ) : ℝ)^M8.Machine.BudgetBound.tau) ∧
        RecordPayload (owner.castAdd M8.RevMachine.LeafCore.small) (fun _ => blank) 0 out F ∧
        (∀ c s (label : Fin L) (j : Fin W), M8.RevMachine.ext out (helperFieldCell (helperSlotField c dst w s) label j) =
          M8.RevMachine.ext word (helperFieldCell (helperSlotField c src w s) label j)) ∧
        (∀ j : Fin T, j ≠ owner → (∀ k, bank k ≠ j) →
          F.L (j.castAdd M8.RevMachine.LeafCore.small) = S.L (j.castAdd M8.RevMachine.LeafCore.small) ∧
          F.R (j.castAdd M8.RevMachine.LeafCore.small) = S.R (j.castAdd M8.RevMachine.LeafCore.small)) ∧
        ∀ j : Fin M8.RevMachine.LeafCore.small, F.L (j.natAdd T) = [] ∧ F.R (j.natAdd T) = [] := by
  let N := M8.RevMachine.LeafCore.small
  let head := fun (i : Fin 127) => helperHeaderPorts i (1 : Fin 268) 3 12 (helperArchiveBank i 3) (helperArchiveBank i 4)
  let headers := fun (i : ℕ) j => bank (head (Fin.ofNat 127 i) j)
  let full := bank.trans (Fin.castAddEmb N)
  let C := helperSlotRate src dst
  obtain ⟨pack,exec⟩ := helperLabelSlot_exec src dst capacity body headers owner (fun _ _ => apart _)
  refine ⟨.seq (helperHeaderSweep (fun i => (helperArchiveBank i).trans full) (List.finRange 127)) pack,C,?_⟩
  intro w L W v size pos word u S seed payload clean
  obtain ⟨y,D,k,user,setup,bill,left,stored,off⟩ := helperArchive_exec body full w L W u S seed
  have external (j : Fin N) (k : Fin 268) : full k ≠ j.natAdd T := by
    intro eq
    have h := congrArg Fin.val eq
    change (bank k).val = T+j.val at h
    omega
  have ownerFree (k : Fin 268) : full k ≠ owner.castAdd N := (Fin.castAddEmb N).injective.ne (apart k)
  obtain ⟨z,F,m,out,same,run,paid,result,read,keep,clear⟩ := exec size pos word y D (fun i j => by
    have eq : Fin.ofNat 127 i.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
    simp only [headers,eq]
    have h := stored i j
    fin_cases j <;> first | exact h | skip
    by_cases e : i.val = 15 <;> simpa [head,helperHeaderPorts,e,full] using h)
    (fun p => by change readAt blank (D.L (owner.castAdd N)) (D.R (owner.castAdd N)) _ = _; rw [left,off _ ownerFree]; exact payload p)
    (fun j => by simpa only [left,off _ (external j)] using clean j)
  refine ⟨z,F,k+m,out,same.trans user,Exec.seq setup run,?_,result,read,?_,clear⟩
  · rw [Nat.cast_add]
    exact add_le_add (by exact_mod_cast bill) paid
  · intro j other outside
    exact ⟨(keep j other).1.trans (congrFun left _),(keep j other).2.trans
      (off _ (fun k => (Fin.castAddEmb N).injective.ne (outside k)))⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
