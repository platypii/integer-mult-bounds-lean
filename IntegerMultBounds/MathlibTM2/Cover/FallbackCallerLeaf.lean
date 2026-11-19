module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackLeafFrame

/-! Run the weighted stopped leaf on the caller's payload and release its private tapes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback.Record
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open M8 ActualAffineScaling FlatCoordinateLayout M8.Exchange IntegerMultBounds.Swap.Shear
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
variable [M8.Machine.Net] {P U : Type} {n d w W : ℕ}
local notation "fields" => d+1
local notation "N" => rowSwapBlock.tapes+35
local notation "M" => prime^(w+1)
local instance : NeZero M := ⟨(pow_pos prime_prime.pos _).ne'⟩

theorem callerPackedLeaf_exec (rank g : ℕ) (dim : fields = rank+g) (weight inv : Fin rank → ZMod M)
    (unit : ∀ i, weight i * inv i = 1) (H J : ℕ) (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (caller : Fin 58 ↪ Fin n)
    (original : Fin (M^(fields+fields)*W) → ZMod 2) :
    let coords := (List.finRange fields).filter (fun i => i.val < rank)
    let read := fun a : Fin coords.length => (⟨(coords.get a).val,
      of_decide_eq_true (List.mem_filter.mp (coords.get_mem a)).2⟩ : Fin rank)
    let k : Fin coords.length → Fin ((fields+d)+1) := fun a => (coords.get a).castAdd fields
    let t : Fin coords.length → Fin ((fields+d)+1) := fun a => (coords.get a).rev.natAdd fields
    let Q := leafCapacity ((fields+d)+1)
    let capacity : columnCapacity ≤ Q := le_max_left ..
    let signCapacity : ∀ a, (fieldSignProgram (k a) true).1 ≤ Q := fun a =>
      (Finset.le_sup (f := fun j => (fieldSignProgram j true).1) (Finset.mem_univ (k a))).trans (le_max_right ..)
    let width := fun a => 22+fieldSignSlots (k a)
    let total := Fintype.card (Σ a, Fin (width a))
    let host := ((Fin.castAddEmb (n := 62) (N-35)).trans (Fin.castAddEmb total)).trans (Fin.castAddEmb 1)
    let cost := fun a => exchangeTime U (read a).val 0 (k a) (t a) (width a) w W H J
    let prog := placedLeafProgram (P := Empty) (U := U) k t (fun a => (read a).val) capacity signCapacity
    let release := prog.seq (Node.usub (host 2) (host 61) (host 0))
    let budget := 1+((List.finRange coords.length).map cost).sum+1+(4*H+4)
    let T := 62+(N-35)+total+1
    let pos := lt_of_lt_of_le columnCapacity_pos capacity
    let port := host.trans (Fin.natAddEmb n)
    let src := fun i => (caller (leafHeaderSources i)).castAdd T
    let setup : Pr P (n+T) Q prime U := copyLeafHeaders src (leafHeaderTargets.trans port) (port 0) (port 1) (List.finRange 7)
    let bank := payloadBank (caller 24) (host 24)
    let run := setup.seq (statePlacedNormalized bank (le_refl Q) pos Empty.elim release)
    let work := (List.finRange (n+T)).filter fun i => n ≤ i.val
    let c := fun j => (caller j).castAdd T
    ∀ (body : P → Pr P (n+T) Q prime U) v (S : Stacks (n+T) prime) push,
      Fast.Main.mnProgPush run ≤ push → (∀ f, Fast.Main.mnProgPush (body f) ≤ push) →
      (∀ i : Fin (n+T), n ≤ i.val → S.L i = [] ∧ S.R i = []) →
      S.R (c 2) = binSyms H M → S.R (c 53) = binSyms J W → S.R (c 28) = binSyms 1 1 →
      S.R (c 44) = binSyms H (1 : ZMod M).val → (S.R (c 45)).length = w →
      S.R (c 56) = (List.ofFn fun i => binSyms H (inv i).val).flatten →
      (∀ k, readAt blank (S.L (c 24)) (S.R (c 24)) (k-0) = RadixToBinary.binaryEncoding.encode
        (putWord (fun _ => blank) 0 (List.ofFn (SparseRoleCircuit.encode ∘ original)) k)) →
      let ticks := 6*(3*H+J+1+w+rank*H)+43+(1+budget)
      ∃ z F l, ∃ after : Fin (M^(fields+fields)*W) → ZMod 2, z.user = v.user ∧
        l ≤ ticks+(4*work.length+1+work.length*(6*(push*ticks))) ∧
        Exec body (run.seq (clearWorkTapes work)) (mk v S) l (mk z F) ∧
        (∀ (hg tg : Fin g → ZMod M) (x : State (Fin rank) (ZMod M)) (j : Fin W),
          let addr := fun y => let t := childFields hg tg y
                               index (Fin.append (fun i : Fin fields => t.1 (i.cast dim))
                                 (fun i : Fin fields => t.2 (i.cast dim))) j
          after (addr (Weighted.child rank weight inv x)) = original (addr x)) ∧
        (∀ k, RadixToBinary.binaryEncoding.encode (putWord (fun _ => blank) 0
          (List.ofFn (SparseRoleCircuit.encode ∘ after)) k) =
          readAt blank (F.L (c 24)) (F.R (c 24)) (k-0)) ∧
        (∀ j : Fin n, j ≠ caller 24 → F.L (j.castAdd T) = S.L (j.castAdd T) ∧ F.R (j.castAdd T) = S.R (j.castAdd T)) ∧
        ∀ i : Fin (n+T), n ≤ i.val → F.L i = [] ∧ F.R i = [] := by
  intro coords read k t Q cap sign width total host cost prog release budget T pos port src setup bank run work c
    body v S push hp hb free base widthWord one padded clockLen archive payload ticks
  obtain ⟨u,D,hu,left,keep,loaded,empty,finish⟩ := privateLeaf_return (le_refl Q) pos caller host body release v S free
  obtain ⟨ready,stored,spare⟩ := privateLeaf_ready caller host H J SparseRoleCircuit.encode
    (fun _ => blank) original S D base widthWord one padded clockLen left keep loaded
    (fun j => (free (j.natAdd n) (Nat.le_add_right ..)).1) empty payload
  have inner := placedPackedLeaf_exec (P := Empty) (U := U) rank g dim weight inv unit H J hm hw hW
    [] [] (fun _ => blank) 0 (fun _ _ _ => rfl) original
  obtain ⟨z,F,l,after,hz,hl,exec,effect,out,_,_⟩ := inner Empty.elim (stateLiftDown pos (embDn bank u))
    (embStk bank D) (by simpa only [List.append_nil] using ready)
    (by simpa only [List.append_nil] using stored.trans archive)
    (fun j hj => spare j (fun i eq => by have h := congrArg Fin.val eq; change i.val = j.val at h; have := i.isLt; omega))
  obtain ⟨a,G,m,ha,hm',done,lhs,rhs,frame,clean⟩ := finish z F l push exec hp hb
  refine ⟨a,G,m,after,ha.trans (hz.trans hu),hm'.trans ?_,done,effect,?_,frame,clean⟩
  · have copyCost := leafHeaderCopy_cost (fun j => (S.R (c j)).length) H J w rank
      ((congrArg List.length base).trans (length_binSyms ..))
      ((congrArg List.length widthWord).trans (length_binSyms ..))
      ((congrArg List.length one).trans (length_binSyms ..))
      ((congrArg List.length padded).trans (length_binSyms ..)) clockLen
      (by simp [archive,List.length_flatten,List.map_ofFn,Function.comp_def,length_binSyms,List.ofFn_const])
    dsimp only [ticks]
    rw [← copyCost]
    gcongr
  · intro j
    change _ = readAt blank (G.L ((caller 24).castAdd T)) (G.R ((caller 24).castAdd T)) _
    rw [lhs,rhs]
    exact out j

end IntegerMultBounds.MathlibTM2.Cover.Fallback.Record
