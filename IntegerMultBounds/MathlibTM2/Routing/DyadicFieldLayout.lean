module

public import IntegerMultBounds.MathlibTM2.Routing.FiberScan

/-! Binary significance is structural: split the most significant bit, then
repeat inside each preceding-bit fiber. No finite permutation certificate. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.DyadicFieldLayout
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  FiberScan SmallFieldMove
variable {T Q A : ℕ} {P U β : Type} {body : P → Pr P T Q A U}

/-- The left/right branches are successive binary field digits, most significant first. -/
abbrev Field (β : Type) : ℕ → Type
  | 0 => β
  | k+1 => Field β k × Field β k

def word (encode : β → List (Fin (A+4))) : {k : ℕ} → Field β k → List (Fin (A+4))
  | 0, x => encode x
  | _+1, x => word encode x.1++word encode x.2

/-- Complete spectator rows in their existing prefix fibers. -/
def stream (encode : β → List (Fin (A+4))) {k : ℕ} (fibers : List (List (Field β k))) :
    List (Fin (A+4)) := fibers.flatMap fun rows => rows.flatMap (word encode)

def refineFibers {k : ℕ} (fibers : List (List (Field β (k+1)))) : List (List (Field β k)) :=
  fibers.flatMap fun rows => [rows.map Prod.fst,rows.map Prod.snd]

/-- The concrete block pairs supplied to the binary tape program. -/
def blockPairs (encode : β → List (Fin (A+4))) {k : ℕ} (rows : List (Field β (k+1))) :=
  rows.map fun x => (word encode x.1,word encode x.2)

theorem blockPairs_input (encode : β → List (Fin (A+4))) {k : ℕ} (rows : List (Field β (k+1))) :
    pairStream (blockPairs encode rows) = rows.flatMap (word encode) := by
  simp [pairStream,blockPairs,List.flatMap_map,word]

theorem blockPairs_output (encode : β → List (Fin (A+4))) {k : ℕ}
    (fibers : List (List (Field β (k+1)))) :
    (fibers.map (blockPairs encode)).flatMap splitPlanes = stream encode (refineFibers fibers) := by
  simp [stream,refineFibers,blockPairs,splitPlanes,List.flatMap_map,List.flatMap_assoc]

theorem refineFibers_length {k : ℕ} (fibers : List (List (Field β (k+1)))) :
    (refineFibers fibers).length = 2*fibers.length := by
  induction fibers with
  | nil => rfl
  | cons rows fibers ih => simp [refineFibers] at *; omega

theorem word_length (encode : β → List (Fin (A+4))) (W : ℕ)
    (hlen : ∀ x, (encode x).length = W) {k : ℕ} (x : Field β k) :
    (word encode x).length = 2^k*W := by
  induction k with
  | zero => simpa [word] using hlen x
  | succ k ih =>
    simp only [word,List.length_append,ih,Nat.pow_succ]
    ring

theorem refineFibers_row_length {k : ℕ} (fibers : List (List (Field β (k+1)))) (B : ℕ)
    (hlen : ∀ rows ∈ fibers, rows.length = B) :
    ∀ rows ∈ refineFibers fibers, rows.length = B := by
  intro rows hm
  obtain ⟨xs,hxs,hm⟩ := List.mem_flatMap.mp hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl <;> simpa only [List.length_map] using hlen xs hxs

theorem stream_length (encode : β → List (Fin (A+4))) (W B : ℕ)
    (hlen : ∀ x, (encode x).length = W) {k : ℕ} (fibers : List (List (Field β k)))
    (hrows : ∀ rows ∈ fibers, rows.length = B) :
    (stream encode fibers).length = fibers.length*(B*(2^k*W)) := by
  rw [stream,List.length_flatMap,List.map_eq_replicate_iff.mpr ?_,List.sum_replicate,smul_eq_mul]
  intro rows hm
  rw [List.length_flatMap,List.map_eq_replicate_iff.mpr ?_,List.sum_replicate,smul_eq_mul,hrows rows hm]
  intro x _
  exact word_length encode W hlen x

/-- Doubling the prefix count and halving the remaining field preserves the
entire tensor volume; no spectator field is padded. -/
theorem stream_refine_length (encode : β → List (Fin (A+4))) (W B : ℕ)
    (hlen : ∀ x, (encode x).length = W) {k : ℕ} (fibers : List (List (Field β (k+1))))
    (hrows : ∀ rows ∈ fibers, rows.length = B) :
    (stream encode (refineFibers fibers)).length = (stream encode fibers).length := by
  rw [stream_length encode W B hlen _ (refineFibers_row_length fibers B hrows),
    stream_length encode W B hlen _ hrows,refineFibers_length,Nat.pow_succ]
  ring

/-- One executable significance-preserving bit pass. Its endpoint is the next
binary frontier, so successive passes preserve both bit and spectator order. -/
theorem splitFieldLevel_exec
    (prefixCount prefixClock count clock volume fiberVolume src archive zeroBank oneBank tmp : Fin T)
    (hreg : [prefixCount,prefixClock,count,clock,volume,fiberVolume,src,archive,zeroBank,oneBank,tmp].Nodup)
    (encode : β → List (Fin (A+4))) (W B k : ℕ) (hlen : ∀ x, (encode x).length = W)
    (fibers : List (List (Field β (k+1)))) (hrows : ∀ rows ∈ fibers, rows.length = B)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hprefix : (S.R prefixCount).length = fibers.length)
    (hcount : (S.R count).length = B) (hvolume : (S.R volume).length = 2^k*W)
    (hfiber : (S.R fiberVolume).length = 2*(B*(2^k*W)))
    (hsrc : S.R src = stream encode fibers++tail)
    (hprefixClock : S.R prefixClock = []) (hclock : S.R clock = [])
    (harchive : S.R archive = []) (hzero : S.R zeroBank = [])
    (hone : S.R oneBank = []) (htmp : S.R tmp = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ fibers.length*(24*(B*(2^k*W))+15*B+21)+8 ∧
      Exec body (retainedSplitFibers prefixCount prefixClock count clock volume fiberVolume
        src archive zeroBank oneBank tmp) (mk v S) n
        (mk v' {S with R := Function.update S.R src (stream encode (refineFibers fibers)++tail)}) := by
  have hpairs : ∀ rows ∈ fibers.map (blockPairs encode), rows.length = B ∧
      ∀ r ∈ rows, r.1.length = 2^k*W ∧ r.2.length = 2^k*W := by
    intro rows hm
    obtain ⟨xs,hxs,rfl⟩ := List.mem_map.mp hm
    refine ⟨by simpa [blockPairs] using hrows xs hxs,?_⟩
    intro r hr
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hr
    exact ⟨word_length encode W hlen x.1,word_length encode W hlen x.2⟩
  obtain ⟨v',n,hu,hn,he⟩ := retainedSplitFibers_exec (body := body)
    prefixCount prefixClock count clock volume fiberVolume src archive zeroBank oneBank tmp hreg
    (fibers.map (blockPairs encode)) B (2^k*W) hpairs tail v S
    (by simpa only [List.length_map] using hprefix) hcount hvolume hfiber
    (by simpa only [List.flatMap_map,Function.comp_def,blockPairs_input,stream] using hsrc)
    hprefixClock hclock harchive hzero hone htmp
  rw [blockPairs_output encode fibers] at he
  exact ⟨v',n,hu,by simpa only [List.length_map] using hn,he⟩

end IntegerMultBounds.MathlibTM2.Routing.DyadicFieldLayout
