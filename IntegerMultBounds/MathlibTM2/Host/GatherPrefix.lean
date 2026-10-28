module

public import IntegerMultBounds.MathlibTM2.Host.GatherSpread

/-! One masked scan gathers arbitrary symbols and restores a borrowed source suffix. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2

variable {T Q A : ℕ} {U P : Type} (body : P → Pr P T Q A U)

def gatherSymbols {α : Type*} : List α → List Bool → List α
  | s::ss,m::ms => if m then s::gatherSymbols ss ms else gatherSymbols ss ms
  | _,_ => []

theorem length_gatherSymbols {α : Type*} : ∀ (ss : List α) (ms : List Bool),
    ss.length = ms.length → (gatherSymbols ss ms).length = ms.count true
  | [],[],_ => rfl
  | s::ss,m::ms,h => by
    have ih := length_gatherSymbols ss ms (by simpa using h)
    cases m <;> simp [gatherSymbols,ih]
  | [],_::_,h => by simp at h
  | _::_,[],h => by simp at h

def gatherPrefixR (R : Fin T → List (Fin (A+4))) (src mask ts tm dst : Fin T)
    (rest ss : List (Fin (A+4))) (ms : List Bool) (os : List (Fin (A+4))) : Fin T → List (Fin (A+4)) :=
  Function.update (Function.update (Function.update (Function.update (Function.update R mask [])
    src rest) tm ((ms.map bitSymbol).reverse++R tm)) ts (ss.reverse++R ts)) dst (os.reverse++R dst)

theorem gatherPrefix_loop {src mask ts tm dst cs : Fin T} (h : [src, mask, ts, tm, dst].Nodup) :
    ∀ (ms : List Bool) (ss rest : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A), ms.length = ss.length →
      S.R mask = ms.map bitSymbol → S.R src = ss++rest →
      v.flag = ms.head?.isSome →
      ∃ v' : HS T Q A U, v'.user = v.user ∧
        Exec body (.loop (·.flag) (.act (gatherStep src mask ts tm dst cs))) (mk v S)
          (2 * ms.length + 1)
          (mk v' { S with R := gatherPrefixR S.R src mask ts tm dst rest ss ms (gatherSymbols ss ms) }) := by
  have hn := h
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hn
  obtain ⟨⟨a1, a2, a3, a4⟩, ⟨b1, b2, b3⟩, ⟨c1, c2⟩, d1⟩ := hn
  intro ms
  induction ms with
  | nil =>
    intro ss rest v S hl hm hs hf
    obtain rfl : ss = [] := List.eq_nil_of_length_eq_zero (by simpa using hl.symm)
    refine ⟨v, rfl, Exec.cast (.loop_false (by simpa using hf)) (by simp) ?_⟩
    congr 1
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    simp only [gatherPrefixR]
    by_cases hk1 : k = dst
    · subst hk1; simp [gatherSymbols]
    by_cases hk2 : k = ts
    · subst hk2; simp [hk1]
    by_cases hk3 : k = tm
    · subst hk3; simp [hk1, hk2]
    by_cases hk4 : k = src
    · subst hk4; simp [hk1, hk2, hk3, hs]
    by_cases hk5 : k = mask
    · subst hk5; simp [hk1, hk2, hk3, hk4, hm]
    simp [hk1, hk2, hk3, hk4, hk5]
  | cons m ms ih =>
    intro ss rest v S hl hm hs hf
    obtain ⟨s, ss, rfl⟩ : ∃ s ss', ss = s :: ss' := by
      cases ss with
      | nil => simp at hl
      | cons s ss' => exact ⟨s, ss', rfl⟩
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    have hm' : S.R mask = bitSymbol m :: ms.map bitSymbol := hm
    have hs' : S.R src = s :: (ss++rest) := hs
    set R₁ := Function.update (Function.update (Function.update (Function.update S.R mask
      (ms.map bitSymbol)) src (ss++rest)) tm (bitSymbol m :: S.R tm)) ts
      (s :: S.R ts) with hR₁
    set R₂ := if m then Function.update R₁ dst (s :: S.R dst) else R₁ with hR₂
    have hrun : (gatherStep src mask ts tm dst cs : Act T Q A U).run (mk v S) =
        mk { v with
            sym := some (bitSymbol m)
            scan := Function.update v.scan cs s
            flag := ms.head?.isSome } { S with R := R₂ } := by
      cases m <;>
      simp [gatherStep, Action.run, peekR, update_rt, hm', hs', R₂, R₁,
        a1, b1, b2, b3, c1, Ne.symm a1, Ne.symm a2, Ne.symm a3, Ne.symm a4,
        Ne.symm b1, Ne.symm b2, Ne.symm b3, Ne.symm c2, Ne.symm d1]
    have hR₂m : R₂ mask = ms.map bitSymbol := by
      cases m <;> simp [R₂, R₁, Ne.symm a1, b1, b2, b3]
    have hR₂s : R₂ src = ss++rest := by
      cases m <;> simp [R₂, R₁, a2, a3, a4]
    obtain ⟨v', hu, he⟩ := ih ss rest { v with
        sym := some (bitSymbol m)
        scan := Function.update v.scan cs s
        flag := ms.head?.isSome } { S with R := R₂ } hl hR₂m hR₂s rfl
    refine ⟨v', hu, Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) (by simpa using hf)
      (hrun ▸ Exec.act (body := body) (gatherStep src mask ts tm dst cs) (mk v S)) he)
      (by simp; ring) ?_⟩
    congr 2
    funext k
    cases m <;>
    simp [gatherPrefixR, R₂, R₁, gatherSymbols, Function.update_apply, c2, d1, Ne.symm a4, Ne.symm b3,
      Ne.symm c1, Ne.symm c2, Ne.symm d1] <;> split_ifs <;> simp_all

/-- Gather an arbitrary-symbol prefix above a borrowed source suffix. The source
and mask restore exactly; the output gains the selected symbols in order. -/
theorem gatherPrefix_exec {src mask ts tm dst out cs : Fin T} (h : GSRegs src mask ts tm dst out)
    (ms : List Bool) (ss rest : List (Fin (A+4))) (hl : ms.length = ss.length) (v : HS T Q A U) (S : Stacks T A)
    (hm : S.R mask = ms.map bitSymbol) (hs : S.R src = ss++rest)
    (hts : S.R ts = []) (htm : S.R tm = []) (hdst : S.R dst = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ 8 * ms.length + 8 ∧
      Exec body (gather src mask ts tm dst out cs) (mk v S) m
        (mk v' { S with R := Function.update S.R out (gatherSymbols ss ms ++ S.R out) }) := by
  have hn := h
  simp only [GSRegs, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hn
  obtain ⟨⟨a1, a2, a3, a4, a5⟩, ⟨b1, b2, b3, b4⟩, ⟨c1, c2, c3⟩, ⟨d1, d2⟩, e1⟩ := hn
  have h5 : [src, mask, ts, tm, dst].Nodup := by
    simp [a1, a2, a3, a4, b1, b2, b3, c1, c2, d1]
  have a1' := Ne.symm a1; have a2' := Ne.symm a2; have a3' := Ne.symm a3
  have a4' := Ne.symm a4; have a5' := Ne.symm a5; have b1' := Ne.symm b1
  have b2' := Ne.symm b2; have b3' := Ne.symm b3; have b4' := Ne.symm b4
  have c1' := Ne.symm c1; have c2' := Ne.symm c2; have c3' := Ne.symm c3
  have d1' := Ne.symm d1; have d2' := Ne.symm d2; have e1' := Ne.symm e1
  obtain ⟨v₁, hu₁, he₁⟩ := gatherPrefix_loop body (cs := cs) h5 ms ss rest
    { v with flag := (S.R mask).head?.isSome } S hl hm hs (by rw [hm]; cases ms <;> rfl)
  set R₁ := gatherPrefixR S.R src mask ts tm dst rest ss ms (gatherSymbols ss ms) with hR₁
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body tm mask (Ne.symm b2) id v₁ { S with R := R₁ }
  set R₂ := movedR R₁ tm mask id (R₁ tm) with hR₂
  obtain ⟨v₃, hu₃, he₃⟩ := moveR_exec body ts src (Ne.symm a2) id v₂ { S with R := R₂ }
  set R₃ := movedR R₂ ts src id (R₂ ts) with hR₃
  obtain ⟨v₄, hu₄, he₄⟩ := moveR_exec body dst out e1 id v₃ { S with R := R₃ }
  have hg := length_gatherSymbols ss ms hl.symm
  have hcount := List.count_le_length (a := true) (l := ms)
  have ht₁ : R₁ tm = (ms.map bitSymbol).reverse := by
    simp [hR₁, gatherPrefixR, htm, d1, c1']
  have hs₁ : R₁ ts = ss.reverse := by
    simp [hR₁, gatherPrefixR, hts, c2]
  have hd₁ : R₁ dst = (gatherSymbols ss ms).reverse := by
    simp [hR₁, gatherPrefixR, hdst]
  have hs₂ : R₂ ts = ss.reverse := by
    simp [hR₂, movedR, Ne.symm b1, hs₁, c1]
  have hd₃ : R₃ dst = (gatherSymbols ss ms).reverse := by
    simp [hR₃, hR₂, movedR, Ne.symm a4, Ne.symm b3, hd₁, a1, a3, c1, b1', c2', d1']
  refine ⟨v₄, 1 + (2 * ms.length + 1) + ((2 * (R₁ tm).length + 2) + ((2 * (R₂ ts).length + 2) +
    (2 * (R₃ dst).length + 2))), by rw [hu₄, hu₃, hu₂, hu₁], ?_,
    Exec.seq (Exec.seq (peekR_run mask v S ▸ Exec.act (body := body) (peekR mask) (mk v S)) he₁)
      (Exec.seq he₂ (Exec.seq he₃ (Exec.cast he₄ rfl ?_)))⟩
  · rw [ht₁, hs₂, hd₃]
    simp only [List.length_reverse, List.length_map]
    omega
  · congr 2
    funext k
    simp [hR₃, hR₂, hR₁, movedR, gatherPrefixR, Function.update_apply, hts, htm, hdst, a1, a2,
      a3, a4, b1, b2, b3, c1, c2, d1, Ne.symm a1,
      Ne.symm a4, Ne.symm a5, Ne.symm b1, Ne.symm b3, Ne.symm b4, Ne.symm c1,
      Ne.symm c2, Ne.symm c3, Ne.symm d1, Ne.symm d2, Ne.symm e1]
    split_ifs <;> simp_all


end IntegerMultBounds.MathlibTM2.Host
