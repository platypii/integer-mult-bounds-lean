module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpRawGatherData
public import IntegerMultBounds.MathlibTM2.Mult.ChirpGatherMode

/-! # Gather all chirp windows directly from the raw line

Counter generation, cyclic extension, the shared sweep and all generated-word cleanup
are composed here. Shared mode also borrows a retained advance schedule.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

def chirpRawGatherWith (shared : Bool) (rg : TblR 10 → Fin T) (r : ChirpRawReg → Fin T) : Pr P T Q A U :=
  .seq (chirpCyclicSetup rg (chirpRawCounters r)) <|
  .seq (cyclicCopy (r (.counter 0)) (r (.counter 1)) (r (.counter 2)) (r .saved)
    (r (.counter 3)) (r .raw) (r .front) (r .back) (r .acc) (r .expanded)
    (r .extension) (r .buf) (r .tmp)) <|
  .seq (chirpGatherMode shared rg (r .dst) (r .control) (r .saved) (r .advance) (r (.counter 4))
    (r .extension) (r .acc) (r .current) (r .savedSource) (r .buf) (r .tmp) (r .count))
    (clearWords (chirpRawClearRoles.map r))

/-- The original caller generates and releases its own schedule. -/
def chirpRawGather (rg : TblR 10 → Fin T) (r : ChirpRawReg → Fin T) : Pr P T Q A U :=
  chirpRawGatherWith false rg r

/-- The grouped caller borrows and restores the same schedule on every line. -/
def chirpRawGatherShared (rg : TblR 10 → Fin T) (r : ChirpRawReg → Fin T) : Pr P T Q A U :=
  chirpRawGatherWith true rg r

def chirpRawGatherWithCost (shared : Bool) (W e s t m w M : ℕ) : ℕ :=
  chirpRawSetupCost W e s m w + chirpRawCopyCost s m w +
    chirpGatherModeCost shared W e s t m w M +
    (2 * (chirpCyclicCounterTotal s m w + (s + 3 * m) * w) + 13)

/-- Raw source, dimensions and any shared schedule are retained; generated setup is erased.
Only the ordered window destination changes. -/
theorem chirpRawGatherWith_exec (shared : Bool) {rg : TblR 10 → Fin T} {r : ChirpRawReg → Fin T}
    (hrg : Function.Injective rg) (hr : Function.Injective r) (hsep : ∀ q b, rg b ≠ r q)
    {W e : ℕ} (wl nl : List (Fin (A + 4))) (hwl : wl.length = W) (hnl : nl.length = e) (heW : e ≤ W)
    (st : TblSt 10 A) (s t m w M : ℕ)
    (hs : st.val 0 = s) (htval : st.val 1 = t) (hm : st.val 2 = m) (hw : st.val 3 = w)
    (hs0 : 0 < s) (hst : s ≤ t) (ht : 0 < t)
    (hsize : s + 3 * m + 1 < 2 ^ W) (hvolume : (s + 3 * m + 1) * w < 2 ^ W)
    (hk : ∀ j < M, (j + 1) * m < 2 ^ W)
    (hnum : ∀ j < M, s * ((j + 1) * m) < 2 ^ W) (hwidth : m * w < 2 ^ W)
    (hzero : ∀ i : Fin 10, 4 ≤ i.val → st.val i = 0) (hfit : ∀ i, st.val i < 2 ^ W)
    (u : ZMod s → GaussianInt) (hvalid : ∀ j < M, j * m < t)
    (v : HS T Q A U) (S : Stacks T A) (hS : tblHolds rg S (tblRho W wl nl st))
    (hsrc : S.R (r .raw) = cstream A w (chirpLine s u)) (hcount : (S.R (r .count)).length = M)
    (hcontrol : S.R (r .control) = if shared then gatherControls A (chirpAdvancesFrom s t m w 0 M) else [])
    (hclean : ∀ q, q ≠ .raw → q ≠ .dst → q ≠ .count → q ≠ .control → S.R (r q) = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ chirpRawGatherWithCost shared W e s t m w M ∧
      Exec body (chirpRawGatherWith shared rg r) (mk v S) n
        (mk v' { S with R := (Function.update S.R (r .dst)
          ((List.range M).flatMap (fun j => cstream A w (chirpWindow s t m j u)) ++ S.R (r .dst))) }) := by
  have hcounters := chirpRawCounters_injective hr
  have hcyclic : [r (.counter 0), r (.counter 1), r (.counter 2), r .saved, r (.counter 3), r .raw,
      r .front, r .back, r .acc, r .expanded, r .extension, r .buf, r .tmp].Nodup := by
    simpa only [chirpRawCyclicRoles, List.map_cons, List.map_nil] using chirpRawCyclicRoles_nodup.map hr
  have hsweep : [r .dst, r .control, r .saved, r .advance, r (.counter 4), r .extension,
      r .acc, r .current, r .savedSource, r .buf, r .tmp, r .count].Nodup := by
    simpa only [chirpRawSweepRoles, List.map_cons, List.map_nil] using chirpRawSweepRoles_nodup.map hr
  obtain ⟨v₁, n₁, hu₁, hn₁, he₁⟩ := chirpCyclicSetup_exec (body := body) hrg (chirpRawCounters r)
    (fun i b => hsep (.counter i) b) wl nl hwl hnl heW st s m w hs hm hw hs0 hsize hvolume hzero hfit v S hS
  let S₁ : Stacks T A := { S with R := (unaryCopiesR (chirpCyclicValues s m w) S.R
    (chirpCyclicAssignments (chirpRawCounters r))) }
  have off₁ (k : Fin T) (hoff : ∀ i, r (.counter i) ≠ k) : S₁.R k = S.R k := by
    apply unaryCopiesR_off
    intro p hp
    obtain ⟨i, rfl⟩ := (chirpCyclicAssignments_mem (chirpRawCounters r) p).mp hp
    exact hoff i
  have offRole₁ (q : ChirpRawReg) (hq : ∀ i, ChirpRawReg.counter i ≠ q) : S₁.R (r q) = S.R (r q) :=
    off₁ _ (fun i => hr.ne (hq i))
  have counters₁ (i : Fin 5) : S₁.R (r (.counter i)) = List.replicate (chirpCyclicCount s m w i) tick := by
    change unaryCopiesR (chirpCyclicValues s m w) S.R (chirpCyclicAssignments (chirpRawCounters r))
      (chirpRawCounters r i) = _
    rw [chirpCyclicCounters_at (chirpRawCounters r) hcounters]
    change List.replicate (chirpCyclicCount s m w i) tick ++ S.R (r (.counter i)) = _
    rw [hclean (.counter i) (by simp) (by simp) (by simp) (by simp), List.append_nil]
  have clean₁ (q : ChirpRawReg) (hqc : ∀ i, ChirpRawReg.counter i ≠ q)
      (hqr : q ≠ .raw) (hqd : q ≠ .dst) (hqn : q ≠ .count) (hqo : q ≠ .control) : S₁.R (r q) = [] :=
    (offRole₁ q hqc).trans (hclean q hqr hqd hqn hqo)
  have hb₁ : tblHolds rg S₁ (tblRho W wl nl st) := by
    intro b
    rw [off₁ _ (fun i => (hsep (.counter i) b).symm)]
    exact hS b
  obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := chirpCyclic_exec (body := body) hcyclic s m w hs0 u v₁ S₁
    (by rw [offRole₁ .raw (by intro i; simp)]; exact hsrc)
    (by simp only [counters₁, List.length_replicate]; rfl)
    (by simp only [counters₁, List.length_replicate]; rfl)
    (by simp only [counters₁, List.length_replicate]; rfl)
    (by simp only [counters₁, List.length_replicate]; rfl) (by
      intro k hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        apply clean₁ <;> simp)
  let ext := cstream A w (chirpExtended s m u)
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R (r .extension) (ext ++ S₁.R (r .extension)) }
  have hext₁ : S₁.R (r .extension) = [] := clean₁ .extension (by intro i; simp) (by simp) (by simp) (by simp) (by simp)
  have hext₂ : S₂.R (r .extension) = ext := by simp [S₂, hext₁]
  have off₂ (k : Fin T) (hoff : k ≠ r .extension) : S₂.R k = S₁.R k := by simp [S₂, hoff]
  have hb₂ : tblHolds rg S₂ (tblRho W wl nl st) := by
    intro b
    rw [off₂ _ (hsep .extension b)]
    exact hb₁ b
  have hready : ChirpControlReady st s t m w 0 :=
    ⟨hs, htval, hm, hw, by simpa using hzero 4 (by decide), by simpa using hzero 5 (by decide)⟩
  obtain ⟨v₃, n₃, hu₃, hn₃, he₃⟩ := chirpGatherMode_exec (body := body) shared hrg hsweep
    (hsep .count) (hsep .saved) (hsep .acc) (hsep .control) wl nl hwl hnl heW s t m w M hs0 hst ht
    hk hnum hwidth st hready hzero hfit u hvalid v₂ S₂ hb₂
    (by rw [off₂ _ (hr.ne (by decide)), offRole₁ .count (by intro i; simp)]; exact hcount)
    hext₂ (by rw [off₂ _ (hr.ne (by decide)), counters₁ 4]; simp [chirpCyclicCount])
    (by rw [off₂ _ (hr.ne (by decide)), offRole₁ .control (by intro i; simp)]; exact hcontrol) (by
      intro k hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        rw [off₂ _ (hr.ne (by decide))] <;> apply clean₁ <;> simp)
  let rows := (List.range M).flatMap (fun j => cstream A w (chirpWindow s t m j u))
  let S₃ : Stacks T A := { S₂ with R := Function.update S₂.R (r .dst) (rows ++ S₂.R (r .dst)) }
  have counters₃ (i : Fin 5) : S₃.R (r (.counter i)) = List.replicate (chirpCyclicCount s m w i) tick := by
    simp only [S₃, Function.update_of_ne (hr.ne (by simp : ChirpRawReg.counter i ≠ .dst))]
    rw [off₂ _ (hr.ne (by simp)), counters₁]
  have hext₃ : S₃.R (r .extension) = ext := by
    simpa only [S₃, Function.update_of_ne (hr.ne (by decide : ChirpRawReg.extension ≠ .dst))] using hext₂
  have hclearSize : ((chirpRawClearRoles.map r).map (fun k => (S₃.R k).length)).sum =
      chirpCyclicCounterTotal s m w + (s + 3 * m) * w := by
    simp only [chirpRawClearRoles, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      counters₃, List.length_replicate, hext₃, ext, length_cstream, length_chirpExtended]
    have hsum := chirpCyclicCount_sum hs0 m w
    simp only [List.sum_cons, List.sum_nil] at hsum
    omega
  obtain ⟨v₄, hu₄, he₄⟩ := clearWords_exec (body := body) (chirpRawClearRoles.map r)
    (chirpRawClearRoles_nodup.map hr) v₃ S₃
  have hclearLen : (chirpRawClearRoles.map r).length = 6 := by simp [chirpRawClearRoles]
  rw [hclearSize, hclearLen] at he₄
  change n₁ ≤ chirpRawSetupCost W e s m w at hn₁
  change n₂ ≤ chirpRawCopyCost s m w at hn₂
  change n₃ ≤ chirpGatherModeCost shared W e s t m w M at hn₃
  refine ⟨v₄, _, hu₄.trans (hu₃.trans (hu₂.trans hu₁)), ?_,
    (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄))).cast rfl ?_⟩
  · unfold chirpRawGatherWithCost
    omega
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    have hdstOff : r .dst ∉ chirpRawClearRoles.map r := by
      intro h
      obtain ⟨q, hq, he⟩ := List.mem_map.mp h
      have hq' : q = .dst := hr he
      subst q
      simp [chirpRawClearRoles] at hq
    have offSetup (k : Fin T) (hoff : k ∉ chirpRawClearRoles.map r) : S₂.R k = S.R k := by
      rw [off₂ _ (by intro he; subst k; exact hoff (List.mem_map.mpr ⟨.extension, by simp [chirpRawClearRoles], rfl⟩))]
      apply off₁
      intro i he
      apply hoff
      exact List.mem_map.mpr ⟨.counter i, (chirpRawClearRoles_mem _).mpr (Or.inl ⟨i, rfl⟩), he⟩
    by_cases hmem : k ∈ chirpRawClearRoles.map r
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hmem
      have hqd : q ≠ .dst := by intro he; subst q; simp [chirpRawClearRoles] at hq
      have hblank : S.R (r q) = [] := by
        rcases (chirpRawClearRoles_mem q).mp hq with ⟨i, rfl⟩ | rfl <;> apply hclean <;> simp
      simp only [ite_eq_left hmem, Function.update_of_ne (hr.ne hqd), hblank]
    · simp only [ite_eq_right hmem]
      by_cases hkd : k = r .dst
      · subst k
        simp only [S₃, Function.update_self, offSetup _ hdstOff, rows]
      · simp only [S₃, Function.update_of_ne hkd]
        exact offSetup k hmem

theorem chirpRawGather_exec {rg : TblR 10 → Fin T} {r : ChirpRawReg → Fin T}
    (hrg : Function.Injective rg) (hr : Function.Injective r) (hsep : ∀ q b, rg b ≠ r q)
    {W e : ℕ} (wl nl : List (Fin (A + 4))) (hwl : wl.length = W) (hnl : nl.length = e) (heW : e ≤ W)
    (st : TblSt 10 A) (s t m w M : ℕ)
    (hs : st.val 0 = s) (htval : st.val 1 = t) (hm : st.val 2 = m) (hw : st.val 3 = w)
    (hs0 : 0 < s) (hst : s ≤ t) (ht : 0 < t)
    (hsize : s + 3 * m + 1 < 2 ^ W) (hvolume : (s + 3 * m + 1) * w < 2 ^ W)
    (hk : ∀ j < M, (j + 1) * m < 2 ^ W)
    (hnum : ∀ j < M, s * ((j + 1) * m) < 2 ^ W) (hwidth : m * w < 2 ^ W)
    (hzero : ∀ i : Fin 10, 4 ≤ i.val → st.val i = 0) (hfit : ∀ i, st.val i < 2 ^ W)
    (u : ZMod s → GaussianInt) (hvalid : ∀ j < M, j * m < t)
    (v : HS T Q A U) (S : Stacks T A) (hS : tblHolds rg S (tblRho W wl nl st))
    (hsrc : S.R (r .raw) = cstream A w (chirpLine s u)) (hcount : (S.R (r .count)).length = M)
    (hclean : ∀ q, q ≠ .raw → q ≠ .dst → q ≠ .count → S.R (r q) = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ chirpRawGatherCost W e s t m w M ∧
      Exec body (chirpRawGather rg r) (mk v S) n
        (mk v' { S with R := (Function.update S.R (r .dst)
          ((List.range M).flatMap (fun j => cstream A w (chirpWindow s t m j u)) ++ S.R (r .dst))) }) := by
  exact chirpRawGatherWith_exec (body := body) false hrg hr hsep wl nl hwl hnl heW
    st s t m w M hs htval hm hw hs0 hst ht hsize hvolume hk hnum hwidth hzero hfit
    u hvalid v S hS hsrc hcount (hclean .control (by simp) (by simp) (by simp))
    (fun q hqr hqd hqn _ => hclean q hqr hqd hqn)

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
