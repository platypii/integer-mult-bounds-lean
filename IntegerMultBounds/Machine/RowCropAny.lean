import IntegerMultBounds.Machine.RowPaddingConstructed

/-! The physical row crop also accepts arbitrary discarded row contents.
No zero-padding promise is needed: every discarded cell is actually erased. -/
namespace IntegerMultBounds.Machine.RowCropAny
open CountedRawFill (filled)
open RowPaddingStream (consumed consumed_step current_view)

def kept (groups : List (List (Fin 4))) (n : ℕ) := groups.map (List.take n)

def state (source dest : ℤ → Fin 4) (p q : ℤ) (groups : List (List (Fin 4)))
    (valid padding : List Bool) (i : ℕ) : Tapes 5 0 :=
  RowPaddingBlock.bank (filled (putWord source p groups.flatten) p (consumed groups i).length blank)
    (putWord dest q (consumed (kept groups (Counter.value valid)) i))
    (p+(consumed groups i).length) (q+(consumed (kept groups (Counter.value valid)) i).length) valid padding

theorem loop_hoare (source dest : ℤ → Fin 4) (p q : ℤ)
    (groups : List (List (Fin 4))) (valid padding count : List Bool)
    (hv : ∀ xs ∈ groups, xs.length = Counter.value valid+Counter.value padding)
    (hc : Counter.value count = groups.length) :
    HoareTime RowPaddingStream.cropProgram
      (fun v => v = RowPaddingStream.bank (putWord source p groups.flatten) dest p q valid padding count)
      (fun v => v = RowPaddingStream.bank (filled (putWord source p groups.flatten) p groups.flatten.length blank)
        (putWord dest q (kept groups (Counter.value valid)).flatten)
        (p+groups.flatten.length) (q+(kept groups (Counter.value valid)).flatten.length) valid padding count)
      (groups.length*(7*Counter.value valid+7*valid.length+7*Counter.value padding+7*padding.length+39)
        +7*count.length+16) := by
  let cost := 7*Counter.value valid+7*valid.length+7*Counter.value padding+7*padding.length+33
  have hb : ∀ i < groups.length, HoareTime RowPaddingBlock.cropProgram
      (fun v => v = state source dest p q groups valid padding i)
      (fun v => v = state source dest p q groups valid padding (i+1)) cost := by
    intro i hi
    have hlen := hv groups[i] (List.getElem_mem hi)
    have ht : (groups[i].take (Counter.value valid)).length = Counter.value valid := by
      simp only [List.length_take]; omega
    let f := filled (putWord source p groups.flatten) p (consumed groups i).length blank
    let g := putWord dest q (consumed (kept groups (Counter.value valid)) i)
    have h := RowPaddingBlock.crop_hoare f g (p+(consumed groups i).length)
      (q+(consumed (kept groups (Counter.value valid)) i).length)
      (groups[i].take (Counter.value valid)) valid padding ht.symm
    have hp := consumed_step groups i hi
    have hk := consumed_step (kept groups (Counter.value valid)) i (by simpa [kept] using hi)
    simp only [kept,List.getElem_map] at hk
    change consumed (kept groups (Counter.value valid)) (i+1) =
      consumed (kept groups (Counter.value valid)) i ++ groups[i].take (Counter.value valid) at hk
    have hwhole := current_view source p groups i hi
    change putWord f (p+(consumed groups i).length) groups[i] = f at hwhole
    have hview := WordSegments.middle f (p+(consumed groups i).length) []
      (groups[i].take (Counter.value valid)) (groups[i].drop (Counter.value valid))
    simp only [List.nil_append,List.length_nil,Nat.cast_zero,add_zero,List.take_append_drop,hwhole] at hview
    rw [hview] at h
    simp only [f,CountedRawFill.filled_adjacent] at h
    have hg : putWord g (q+(consumed (kept groups (Counter.value valid)) i).length)
        (groups[i].take (Counter.value valid)) =
        putWord dest q (consumed (kept groups (Counter.value valid)) (i+1)) := by
      rw [hk]
      exact putWord_append_forward dest q _ _
    rw [hg] at h
    have hcost : 7*(groups[i].take (Counter.value valid)).length+7*valid.length+16+1+
        7*Counter.value padding+7*padding.length+16 = cost := by dsimp [cost]; rw [ht]; omega
    rw [hcost] at h
    simpa only [state,hp,hk,List.length_append,ht,hlen,Nat.cast_add,add_assoc] using h
  have h := CountedLoopReuse.loop_hoare RowPaddingBlock.cropProgram count groups.length
    (state source dest p q groups valid padding) (fun _ => cost) hc hb
  have hp : consumed groups groups.length = groups.flatten := by simp [consumed]
  have hk : consumed (kept groups (Counter.value valid)) groups.length =
      (kept groups (Counter.value valid)).flatten := by
    have hl : (kept groups (Counter.value valid)).length = groups.length := by simp [kept]
    rw [← hl]; simp [consumed]
  apply h.consequence ?_ ?_ ?_
  · intro v hvv; simpa [state,RowPaddingStream.bank,consumed,putWord] using hvv
  · intro v hvv; simpa only [state,hp,hk,RowPaddingStream.bank] using hvv
  · simp only [Finset.sum_const,Finset.card_range,smul_eq_mul]; dsimp [cost]; ring_nf; exact le_rfl

theorem physical_linear (source dest : ℤ → Fin 4) (p q : ℤ)
    (groups : List (List (Fin 4))) (valid padding count : List Bool)
    (hv : ∀ xs ∈ groups, xs.length = Counter.value valid+Counter.value padding)
    (hc : Counter.value count = groups.length) (cv : GrowingCounterData.Canonical valid)
    (cm : GrowingCounterData.Canonical padding) (cc : GrowingCounterData.Canonical count)
    (hspan : 0 < Counter.value valid+Counter.value padding) :
    HoareTime RowPaddingExecution.cropProgram
      (fun v => v = RowPaddingExecution.clockBank (putWord source p groups.flatten) dest
        p q valid padding count (fun _ => blank) 0)
      (fun v => v = RowPaddingExecution.clockBank (filled (putWord source p groups.flatten) p groups.flatten.length blank)
        (putWord dest q (kept groups (Counter.value valid)).flatten) p q valid padding count (fun _ => blank) 0)
      (148*groups.length*(Counter.value valid+Counter.value padding)+53) := by
  have hs := loop_hoare source dest p q groups valid padding count hv hc
  have hfull := RowPaddingExecution.flattened_length groups (Counter.value valid+Counter.value padding) hv
  have hkept := RowPaddingExecution.flattened_length (kept groups (Counter.value valid)) (Counter.value valid) (by
    intro xs hx
    obtain ⟨ys,hy,rfl⟩ := List.mem_map.mp hx
    simp only [List.length_take]
    have hlen := hv ys hy
    omega)
  have hkl : (kept groups (Counter.value valid)).length = groups.length := by simp [kept]
  rw [hkl] at hkept
  have hf : (groups.flatten.length : ℤ) = (groups.length : ℤ)*(Counter.value valid+Counter.value padding) := by exact_mod_cast hfull
  have hk : ((kept groups (Counter.value valid)).flatten.length : ℤ) =
      (groups.length : ℤ)*Counter.value valid := by exact_mod_cast hkept
  rw [hf,hk] at hs
  have hr := RowPaddingExecution.crop_reset_loop_hoare
    (filled (putWord source p groups.flatten) p groups.flatten.length blank)
    (putWord dest q (kept groups (Counter.value valid)).flatten) p q valid padding count
  rw [hc] at hr
  have h := (RowPaddingExecution.mark_hoare (putWord source p groups.flatten) dest p q valid padding count).seq
    (hs.seq (hr.seq (RowPaddingExecution.clear_hoare _ _ p q valid padding count)))
  have hcost := RowPaddingExecution.canonical_cost valid padding count cv cm cc hspan
  rw [hc] at hcost
  apply h.consequence (fun _ hh => hh) (fun _ hh => hh) _
  convert hcost using 1
  ring

theorem take_ofFn {α : Type*} {m n : ℕ} (h : m ≤ n) (f : Fin n → α) :
    (List.ofFn f).take m = List.ofFn (fun i : Fin m => f (Fin.castLE h i)) := by
  apply List.ext_getElem
  · simp only [List.length_take,List.length_ofFn,Nat.min_eq_left h]
  · intro i hi hi'
    simp only [List.getElem_take,List.getElem_ofFn]
    rfl

theorem kept_array (P N M L : ℕ) (hNM : N ≤ M) (x : Fin (P*M*L) → Fin 4) :
    (kept (RowPaddingWord.groups x) (N*L)).flatten =
      List.ofFn (RecursiveRowPadding.crop hNM x) := by
  rw [← RowPaddingWord.groups_flatten (RecursiveRowPadding.crop hNM x)]
  apply congrArg List.flatten
  unfold kept RowPaddingWord.groups
  rw [List.map_ofFn]
  congr 1
  funext a
  simp only [Function.comp_apply]
  rw [take_ofFn (Nat.mul_le_mul_right L hNM)]
  congr 1
  funext k
  obtain ⟨⟨r,b⟩,rfl⟩ := finProdFinEquiv.surjective k
  change x (RowPaddingWord.spanIndex a (Fin.castLE (Nat.mul_le_mul_right L hNM)
      (RecursiveInterchangeRows.pack r b))) =
    RecursiveRowPadding.crop hNM x (RowPaddingWord.spanIndex a (RecursiveInterchangeRows.pack r b))
  rw [RowPaddingWord.spanIndex_pack a r b,RecursiveRowPadding.crop_entry]
  apply congrArg x
  apply Fin.ext
  simp only [RowPaddingWord.spanIndex,Fin.val_cast,Fin.val_castLE,RecursiveInterchangeRows.pack_val]
  ring

private theorem placed_exact {s u t r cost : ℕ} {M : Program s r 0}
    (e : Fin (s+u) ≃ Fin t) (v w : Tapes t 0) (small small' : Tapes s 0)
    (ha : Placement.active e v = small) (hf : Placement.active e w = small')
    (he : Placement.extra e v = Placement.extra e w)
    (hh : HoareTime M (fun x => x = small) (fun x => x = small') cost) :
    HoareTime (Placement.placed M e) (fun x => x = v) (fun x => x = w) cost := by
  apply (Placement.hoare_at hh e v ha).consequence (fun _ h => h) _ le_rfl
  rintro x ⟨y,rfl,rfl⟩
  rw [Placement.replace,he,← hf]
  exact Placement.view _ _

/-- The same complete constructed-count crop program accepts any full row
array. All discarded row cells are erased regardless of their values. -/
theorem constructed_array_hoare (source dest : ℤ → Fin 4) (p q : ℤ)
    (ps ns ms ls : List Bool) (P N M L : ℕ) (x : Fin (P*M*L) → Fin 4)
    (hp : Counter.value ps = P) (hn : Counter.value ns = N) (hm : Counter.value ms = M)
    (hl : Counter.value ls = L) (cp : GrowingCounterData.Canonical ps)
    (cn : GrowingCounterData.Canonical ns) (cm : GrowingCounterData.Canonical ms)
    (cl : GrowingCounterData.Canonical ls) (hP : 0 < P) (hN : 0 < N)
    (hNM : N ≤ M) (hL : 0 < L) :
    HoareTime RowPaddingConstructed.cropProgram
      (fun v => v = RowPaddingConstructed.bank (putWord source p (List.ofFn x)) dest p q ps ns ms ls none none)
      (fun v => v = RowPaddingConstructed.bank
        (filled (putWord source p (List.ofFn x)) p (P*M*L) blank)
        (putWord dest q (List.ofFn (RecursiveRowPadding.crop hNM x))) p q ps ns ms ls none none)
      (413*P*(M*L)) := by
  have hM : 0 < M := lt_of_lt_of_le hN hNM
  let valid := RowPaddingSpanCounts.validBits N L
  let padding := RowPaddingSpanCounts.padBits N M L
  have hs := RowPaddingSpanCounts.span_sum N M L hNM
  have hh := physical_linear source dest p q (RowPaddingWord.groups x) valid padding ps
    (by intro xs hx; rw [RowPaddingWord.group_length x xs hx]; exact hs.symm)
    (hp.trans (RowPaddingWord.groups_length x).symm)
    (RowPaddingSpanCounts.valid_canonical N L) (RowPaddingSpanCounts.pad_canonical N M L) cp
    (by rw [hs]; exact Nat.mul_pos hM hL)
  rw [hs] at hh
  simp only [valid,padding,RowPaddingWord.groups_flatten,RowPaddingWord.groups_length,
    RowPaddingSpanCounts.valid_value,kept_array P N M L hNM x,List.length_ofFn] at hh
  have hphysical : HoareTime RowPaddingConstructed.physicalCropProgram
      (fun v => v = RowPaddingConstructed.bank (putWord source p (List.ofFn x)) dest p q ps ns ms ls
        (some valid) (some padding))
      (fun v => v = RowPaddingConstructed.bank (filled (putWord source p (List.ofFn x)) p (P*M*L) blank)
        (putWord dest q (List.ofFn (RecursiveRowPadding.crop hNM x))) p q ps ns ms ls (some valid) (some padding))
      (148*P*(M*L)+53) := by
    apply placed_exact RowPaddingConstructed.physicalPlacement _ _ _ _ _ _ _ hh
    · exact RowPaddingConstructed.physical_active _ _ _ _ _ _ _ _ _ _
    · exact RowPaddingConstructed.physical_active _ _ _ _ _ _ _ _ _ _
    · exact RowPaddingConstructed.physical_extra _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have h := (RowPaddingConstructed.construct_hoare (putWord source p (List.ofFn x)) dest
    p q ps ns ms ls N M L hn hm hl cn cm cl hNM hL).seq
    (hphysical.seq (RowPaddingConstructed.cleanup_hoare _ _ p q ps ns ms ls valid padding))
  exact h.consequence (fun _ hv => hv) (fun _ hv => hv)
    (RowPaddingConstructed.total_cost P N M L hP hNM hM hL)

end IntegerMultBounds.Machine.RowCropAny
