module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNaturalAdvanceControls
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloAdvanceSchedule
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAdvanceBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloOriginPackets
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightWidth

/-! Generate delimited natural-group advances from its computed binary origin
packets. The small table is constructed from unary width sources and released;
origins, count and all borrowed suffixes are restored. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

def preparedHaloAdvanceCost (V s t band a b L w : ℕ) : ℕ :=
  (32*V+41) + (w*(4*V+10)+6*V+10) +
    ((haloLengthGroup s t band a b L).length*(3*tblC V V+29*V+30)+8*s*w+11) + (38*V+39)

theorem preparedHaloAdvanceControls_exec (P q w s t u band a b L : ℕ)
    (hst : s ≤ t) (hgroup : 0 < (haloLengthGroup s t band a b L).length)
    (v : HS 117 Q A U) (S : Stacks 117 A) (suffix : List (Fin (A+4)))
    (hV : (S.R 115).length = weightWorkspaceWidth P q w t u) (hw : (S.R 94).length = w)
    (hsrc : S.R 109 = haloOriginPackets A (weightWorkspaceWidth P q w t u) s t band a b L ++ suffix)
    (hcount : S.R 116 = List.replicate (haloLengthGroup s t band a b L).length tick)
    (hblank : ∀ k : Fin 117, k.val < 19 → S.R k = [])
    (hfresh : ∀ k ∈ [(88 : Fin 117), 89, 90, 106], S.R k = []) :
    ∃ v' S' n, v'.user = v.user ∧
      n ≤ preparedHaloAdvanceCost (weightWorkspaceWidth P q w t u) s t band a b L w ∧
      Exec body preparedNaturalAdvanceControls (mk v S) n (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      S'.R = Function.update S.R 91 (haloGatherControls A s t band a b L w ++ S.R 91) := by
  let V := weightWorkspaceWidth P q w t u
  obtain ⟨hwV, hsV⟩ := weightWorkspaceWidth_symbolVolume P q w s t u hst
  have hB := hgroup
  have hL : 0 < L := ((mem_haloLengthGroup s t band a b L _).mp
    (haloGroupPhase_mem s t band a b L ⟨0, hB⟩)).2.1
  have hcoords : ∀ origin ∈ haloOrigins s t band a b L, origin < 2^V := by
    intro origin ho
    obtain ⟨phase, hp, rfl⟩ := List.mem_map.mp ho
    obtain ⟨_, _, he⟩ := (mem_haloLengthGroup s t band a b L phase).mp hp
    have hstop := haloStop_le s t band b phase
    have hlt : haloStart s t band a phase < s := by
      dsimp only [haloLength] at he
      omega
    have hsW : s < 2^V := (coefficientWorkspaceWidth_bound P (w+q+2) s t u 0 t hst).2.2.1
    exact hlt.trans hsW
  have hunits : ∀ origin ∈ haloOrigins s t band a b L, origin*w < 2^V := by
    intro origin ho
    exact (Nat.mul_le_mul_right w (by have hh := haloOrigins_fit s t band a b L origin ho; omega)).trans_lt hsV
  obtain ⟨v₁, hu₁, he₁, hh₁⟩ := initializeAdvanceBank_exec (body := body) V v S hV
    (hfresh 106 (by simp)) (fun r => hblank _ (advanceReg_range r))
  let S₁ : Stacks 117 A := { S with R := chirpBankLoadR advanceReg (fun _ => 106) V V (fun _ => 0) S.R }
  have hoff₁ (k : Fin 117) (hk : 19 ≤ k.val) : S₁.R k = S.R k := by
    apply chirpBankLoad_off
    intro r he
    have hr := advanceReg_range r
    rw [he] at hk
    omega
  have hhigh (k : Fin 117) (hk : 19 ≤ k.val) : ∀ r, advanceReg r ≠ k := by
    intro r he
    have hr := advanceReg_range r
    rw [he] at hr
    omega
  obtain ⟨v₂, S₂, n₂, hu₂, hn₂, he₂, hh₂, hf₂⟩ := tbl_load1_runs (body := body)
    advanceReg_injective (List.replicate V tick) (List.replicate V tick) (by simp)
    (hhigh 94 (by decide)) 2 (⟨fun _ => 0, []⟩ : TblSt 4 A) w v₁ S₁
    (by rw [hoff₁ 94 (by decide)]; exact hw) hh₁
  have hh₂' : tblHolds advanceReg S₂ (tblRho V (List.replicate V tick) (List.replicate V tick)
      (advanceHeaderState A w)) := hh₂
  have hoff₂ (k : Fin 117) (hk : 19 ≤ k.val) : S₂.R k = S.R k :=
    (hf₂.2.2.2 k (hhigh k hk)).trans (hoff₁ k hk)
  have hfit : ∀ i, (advanceHeaderState A w).val i < 2^V := by
    intro i
    simp only [advanceHeaderState, Function.update_apply]
    split_ifs <;> first | exact hwV | positivity
  have ho : (0::haloOrigins s t band a b L).Pairwise (· ≤ ·) :=
    List.pairwise_cons.mpr ⟨by simp, haloOrigins_ordered s t band a b L⟩
  obtain ⟨st₃, v₃, S₃, n₃, hw₃, ha₃, hb₃, hu₃, hn₃, he₃, hh₃, hout₃, hi₃, ho₃, hl₃, hf₃⟩ :=
    originAdvanceControls_exec (body := body) le_rfl (haloOrigins s t band a b L) ho hcoords hunits
      (advanceHeaderState A w) (by simp [advanceHeaderState]) (by simp [advanceHeaderState]) hfit
      (List.replicate (haloLengthGroup s t band a b L).length tick) suffix (by simp)
      v₂ S₂ hh₂' (by rw [hoff₂ 116 (by decide)]; exact hcount) (by
        rw [hoff₂ 109 (by decide)]
        simpa [haloOrigins, haloOriginPackets, List.flatMap_map] using hsrc)
      (by rw [hoff₂ 88 (by decide)]; exact hfresh 88 (by simp))
      (by rw [hoff₂ 89 (by decide)]; exact hfresh 89 (by simp))
      (by rw [hoff₂ 90 (by decide)]; exact hfresh 90 (by simp))
  have ha : st₃.acc = [] := ha₃
  have hh₃' : tblHolds advanceReg S₃ (tblRho V (List.replicate V tick) (List.replicate V tick) ⟨st₃.val, []⟩) := by
    have heq : st₃ = ⟨st₃.val, []⟩ := by cases st₃; simp_all
    rw [← heq]
    exact hh₃
  obtain ⟨v₄, n₄, hu₄, hn₄, he₄⟩ := releaseAdvanceBank_exec (body := body) V st₃.val v₃ S₃ hh₃'
  let S₄ : Stacks 117 A := { S₃ with R := fun k => if k.val < 19 then [] else S₃.R k }
  have hoff₃ (k : Fin 117) (hk : 19 ≤ k.val) (hk91 : k ≠ 91) : S₃.R k = S.R k :=
    (hf₃ k hk91 (hhigh k hk)).trans (hoff₂ k hk)
  refine ⟨v₄, S₄, (32*V+41)+(n₂+(n₃+n₄)), hu₄.trans (hu₃.trans (hu₂.trans hu₁)), ?_,
    Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄)), hi₃.trans hf₂.1,
    ho₃.trans hf₂.2.1, hl₃.trans hf₂.2.2.1, ?_⟩
  · have hvol := haloOriginAdvances_volume s t band a b L w
    simp only [haloOrigins_length] at hn₃
    unfold preparedHaloAdvanceCost
    dsimp only [V] at *
    nlinarith only [hn₂, hn₃, hn₄, hvol]
  · funext k
    by_cases hk91 : k = 91
    · subst k
      simpa [S₄, originAdvances_haloControls A s t band a b L w hgroup, hoff₂ 91 (by decide)] using hout₃
    by_cases hk : k.val < 19
    · simp [S₄, hk, hk91, hblank k hk]
    simp [S₄, hk, hk91, hoff₃ k (by omega) hk91]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
