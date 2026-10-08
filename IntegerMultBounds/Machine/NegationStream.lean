import IntegerMultBounds.Machine.BlockNegationReuse
import IntegerMultBounds.Machine.FiberShift

/-! Repeated coordinate negation on uniform fibers. The single physical scratch
interval is reused from the same origin on every iteration; every work clock,
descriptor, scratch cell and scratch head is restored. -/

namespace IntegerMultBounds.Machine.NegationStream

open BlockNegationReuse (bank)

def payload (fibers : List (List (List (Fin 4)))) : List (Fin 4) :=
  (fibers.map List.flatten).flatten

def outputPrefix (i : ℕ) (fibers : List (List (List (Fin 4)))) : List (Fin 4) :=
  ((fibers.take i).map (fun fiber => (BlockNegationData.negate fiber).flatten)).flatten

theorem uniform_payload (fibers : List (List (List (Fin 4)))) (Q B : ℕ)
    (hq : ∀ fiber ∈ fibers, fiber.length = Q)
    (hu : ∀ fiber ∈ fibers, BlockRotationData.Uniform B fiber) :
    BlockRotationData.Uniform (Q*B) (fibers.map List.flatten) := by
  intro xs hx
  obtain ⟨fiber,hf,rfl⟩ := List.mem_map.mp hx
  rw [BlockRotationData.uniform_volume B fiber (hu fiber hf),hq fiber hf]

theorem prefix_length (i Q B : ℕ) (fibers : List (List (List (Fin 4))))
    (hq : ∀ fiber ∈ fibers, fiber.length = Q)
    (hu : ∀ fiber ∈ fibers, BlockRotationData.Uniform B fiber) (hi : i ≤ fibers.length) :
    (outputPrefix i fibers).length = i*(Q*B) := by
  have hh : BlockRotationData.Uniform (Q*B)
      ((fibers.take i).map (fun fiber => (BlockNegationData.negate fiber).flatten)) := by
    intro xs hx
    obtain ⟨fiber,hf,rfl⟩ := List.mem_map.mp hx
    have hm := List.mem_of_mem_take hf
    rw [BlockNegationData.payload_length,BlockRotationData.uniform_volume B fiber (hu fiber hm),hq fiber hm]
  rw [outputPrefix,BlockRotationData.uniform_volume (Q*B) _ hh,List.length_map,
    List.length_take,Nat.min_eq_left hi]

theorem prefix_succ (i : ℕ) (fibers : List (List (List (Fin 4)))) (hi : i < fibers.length) :
    outputPrefix (i+1) fibers = outputPrefix i fibers ++ (BlockNegationData.negate fibers[i]).flatten := by
  simp only [outputPrefix,List.take_succ_eq_append_getElem hi,List.map_append,List.flatten_append,
    List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil,List.append_nil]

private theorem fiber_hoare (source dest scratch : ℤ → Fin 4) (p q r : ℤ)
    (fiber : List (List (Fin 4))) (Q B : ℕ) (hq : fiber.length = Q)
    (hu : BlockRotationData.Uniform B fiber) (hQ : 1 ≤ Q) (hB : 1 ≤ B)
    (b d c : List Bool) (hb : Counter.value b = B)
    (hd : Counter.value d = (Q-1)*B) (hc : Counter.value c = Q-1)
    (cb : GrowingCounterData.Canonical b) (cd : GrowingCounterData.Canonical d)
    (cc : GrowingCounterData.Canonical c)
    (hblank : ∀ z, r ≤ z → z < r+(((Q-1)*B : ℕ) : ℤ) → scratch z = blank) :
    HoareTime BlockNegationReuse.program
      (fun v => v = bank (putWord source p fiber.flatten) dest scratch b d c p q r)
      (fun v => v = bank (putWord source p fiber.flatten)
        (putWord dest q (BlockNegationData.negate fiber).flatten) scratch b d c
        (p+((Q*B : ℕ) : ℤ)) (q+((Q*B : ℕ) : ℤ)) r)
      (210*(Q*B)+219) := by
  cases fiber with
  | nil => simp only [List.length_nil] at hq; omega
  | cons first tail =>
    have hf : first.length = B := hu first (by simp)
    have ht : BlockRotationData.Uniform B tail := fun x hx => hu x (by simp [hx])
    have hn : tail.length = Q-1 := by simp only [List.length_cons] at hq; omega
    have hv := BlockRotationData.uniform_volume B (first::tail) hu
    rw [hq] at hv
    have h := BlockNegationReuse.negate_hoare_linear source dest scratch p q r first tail B hf ht hB
      b d c hb (by simpa only [hn] using hd) (by simpa only [hn] using hc) cb cd cc
      (by simpa only [BlockRotationData.uniform_volume B tail ht,hn] using hblank)
    simpa only [hv] using h

def state (source dest scratch : ℤ → Fin 4) (p q r : ℤ)
    (fibers : List (List (List (Fin 4)))) (Q B : ℕ) (b d c : List Bool) (i : ℕ) : Tapes 8 0 :=
  bank (putWord source p (payload fibers)) (putWord dest q (outputPrefix i fibers)) scratch b d c
    (p+((i*(Q*B) : ℕ) : ℤ)) (q+((i*(Q*B) : ℕ) : ℤ)) r

theorem body_hoare (source dest scratch : ℤ → Fin 4) (p q r : ℤ)
    (fibers : List (List (List (Fin 4)))) (Q B : ℕ)
    (hq : ∀ fiber ∈ fibers, fiber.length = Q)
    (hu : ∀ fiber ∈ fibers, BlockRotationData.Uniform B fiber) (hQ : 1 ≤ Q) (hB : 1 ≤ B)
    (b d c : List Bool) (hb : Counter.value b = B)
    (hd : Counter.value d = (Q-1)*B) (hc : Counter.value c = Q-1)
    (cb : GrowingCounterData.Canonical b) (cd : GrowingCounterData.Canonical d)
    (cc : GrowingCounterData.Canonical c)
    (hblank : ∀ z, r ≤ z → z < r+(((Q-1)*B : ℕ) : ℤ) → scratch z = blank)
    (i : ℕ) (hi : i < fibers.length) :
    HoareTime BlockNegationReuse.program
      (fun v => v = state source dest scratch p q r fibers Q B b d c i)
      (fun v => v = state source dest scratch p q r fibers Q B b d c (i+1))
      (210*(Q*B)+219) := by
  have hsrc := FiberShift.source_fiber source p (fibers.map List.flatten) (Q*B) i
    (uniform_payload fibers Q B hq hu) (by simpa only [List.length_map] using hi)
  simp only [List.getElem_map] at hsrc
  have h := fiber_hoare (putWord source p (payload fibers)) (putWord dest q (outputPrefix i fibers))
    scratch (p+((i*(Q*B) : ℕ) : ℤ)) (q+((i*(Q*B) : ℕ) : ℤ)) r fibers[i] Q B
    (hq _ (List.getElem_mem hi)) (hu _ (List.getElem_mem hi)) hQ hB b d c hb hd hc cb cd cc hblank
  change putWord (putWord source p (payload fibers)) _ _ = _ at hsrc
  rw [hsrc] at h
  have hout : putWord (putWord dest q (outputPrefix i fibers)) (q+((i*(Q*B) : ℕ) : ℤ))
      (BlockNegationData.negate fibers[i]).flatten = putWord dest q (outputPrefix (i+1) fibers) := by
    rw [← prefix_length i Q B fibers hq hu hi.le,putWord_append_forward,prefix_succ i fibers hi]
  rw [hout] at h
  have hlen : (i+1)*(Q*B) = i*(Q*B)+Q*B := by ring
  simpa only [state,payload,hlen,Nat.cast_add,add_assoc] using h

/-- A fixed ten-tape, 218-state machine, independent of all dimensions. -/
def program : Program 10 218 0 := CountedLoopReuse.program BlockNegationReuse.program

/-- Complete payload negation with physically restored scratch and all controls.
The immutable block, tail-volume, tail-count and fiber-count descriptors are
explicit prepared inputs. -/
theorem negate_hoare (source dest scratch : ℤ → Fin 4) (p q r : ℤ)
    (fibers : List (List (List (Fin 4)))) (Q B : ℕ)
    (hq : ∀ fiber ∈ fibers, fiber.length = Q)
    (hu : ∀ fiber ∈ fibers, BlockRotationData.Uniform B fiber) (hQ : 1 ≤ Q) (hB : 1 ≤ B)
    (b d c countBits : List Bool) (hb : Counter.value b = B)
    (hd : Counter.value d = (Q-1)*B) (hc : Counter.value c = Q-1)
    (hn : Counter.value countBits = fibers.length)
    (cb : GrowingCounterData.Canonical b) (cd : GrowingCounterData.Canonical d)
    (cc : GrowingCounterData.Canonical c)
    (hblank : ∀ z, r ≤ z → z < r+(((Q-1)*B : ℕ) : ℤ) → scratch z = blank) :
    HoareTime program
      (fun v => v = CountedLoopReuse.bank
        (bank (putWord source p (payload fibers)) dest scratch b d c p q r)
        CountedCopyReuse.empty (CountedCopyReuse.binary countBits) 1 1)
      (fun v => v = CountedLoopReuse.bank
        (bank (putWord source p (payload fibers))
          (putWord dest q (payload (fibers.map BlockNegationData.negate))) scratch b d c
          (p+((fibers.length*(Q*B) : ℕ) : ℤ)) (q+((fibers.length*(Q*B) : ℕ) : ℤ)) r)
        CountedCopyReuse.empty (CountedCopyReuse.binary countBits) 1 1)
      (fibers.length*(210*(Q*B)+225)+7*countBits.length+16) := by
  have h := CountedLoopReuse.loop_hoare BlockNegationReuse.program countBits fibers.length
    (state source dest scratch p q r fibers Q B b d c) (fun _ => 210*(Q*B)+219) hn
    (body_hoare source dest scratch p q r fibers Q B hq hu hQ hB b d c hb hd hc cb cd cc hblank)
  have hcost : (∑ _i ∈ Finset.range fibers.length, (210*(Q*B)+219))+6*fibers.length+
      7*countBits.length+16 = fibers.length*(210*(Q*B)+225)+7*countBits.length+16 := by
    simp only [Finset.sum_const,Finset.card_range,smul_eq_mul]
    ring
  rw [hcost] at h
  simpa only [program,state,outputPrefix,List.take_zero,List.map_nil,List.flatten_nil,
    putWord,zero_mul,Nat.cast_zero,add_zero,List.take_length,payload,List.map_map,Function.comp_def] using h

theorem linear_bound (L n width : ℕ) (hL : 1 ≤ L) (hw : width ≤ n+1) :
    n*(210*L+225)+7*width+16 ≤ 442*(n*L)+23 := by
  have hnl : n ≤ n*L := by nlinarith
  nlinarith

/-- Linear in the complete input payload, including outer count setup and cleanup. -/
theorem negate_hoare_linear (source dest scratch : ℤ → Fin 4) (p q r : ℤ)
    (fibers : List (List (List (Fin 4)))) (Q B : ℕ)
    (hq : ∀ fiber ∈ fibers, fiber.length = Q)
    (hu : ∀ fiber ∈ fibers, BlockRotationData.Uniform B fiber) (hQ : 1 ≤ Q) (hB : 1 ≤ B)
    (b d c countBits : List Bool) (hb : Counter.value b = B)
    (hd : Counter.value d = (Q-1)*B) (hc : Counter.value c = Q-1)
    (hn : Counter.value countBits = fibers.length)
    (cb : GrowingCounterData.Canonical b) (cd : GrowingCounterData.Canonical d)
    (cc : GrowingCounterData.Canonical c) (cn : GrowingCounterData.Canonical countBits)
    (hblank : ∀ z, r ≤ z → z < r+(((Q-1)*B : ℕ) : ℤ) → scratch z = blank) :
    HoareTime program
      (fun v => v = CountedLoopReuse.bank
        (bank (putWord source p (payload fibers)) dest scratch b d c p q r)
        CountedCopyReuse.empty (CountedCopyReuse.binary countBits) 1 1)
      (fun v => v = CountedLoopReuse.bank
        (bank (putWord source p (payload fibers))
          (putWord dest q (payload (fibers.map BlockNegationData.negate))) scratch b d c
          (p+((fibers.length*(Q*B) : ℕ) : ℤ)) (q+((fibers.length*(Q*B) : ℕ) : ℤ)) r)
        CountedCopyReuse.empty (CountedCopyReuse.binary countBits) 1 1)
      (442*(payload fibers).length+23) := by
  have hw := GrowingCounterData.canonical_width countBits cn
  have hl := Nat.log2_le_self (Counter.value countBits)
  have hbnd := linear_bound (Q*B) fibers.length countBits.length (by nlinarith) (by omega)
  have hv : (payload fibers).length = fibers.length*(Q*B) := by
    rw [payload,BlockRotationData.uniform_volume (Q*B) _ (uniform_payload fibers Q B hq hu),List.length_map]
  rw [← hv] at hbnd
  exact (negate_hoare source dest scratch p q r fibers Q B hq hu hQ hB b d c countBits
    hb hd hc hn cb cd cc hblank).consequence (fun _ h => h) (fun _ h => h) hbnd

end IntegerMultBounds.Machine.NegationStream
