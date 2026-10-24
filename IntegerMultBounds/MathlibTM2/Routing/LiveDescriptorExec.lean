module

public import IntegerMultBounds.MathlibTM2.Routing.LiveAffineDescriptor
public import IntegerMultBounds.MathlibTM2.Routing.LiveGroupedDescriptor

/-! Every common-bank job executes its actual backend, with a live row-count
check covering empty descriptors. There are no per-job execution premises. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

variable {N J Q A : ℕ} {P U : Type}

theorem liveDescriptorBackend_exec (body : P → Pr P (liveDescriptorT N J) Q A U)
    (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K) (hGK : p.G < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)
    (mode : Fin J → LiveDescriptorMode) (w : LiveDescriptorWidths) (j : Fin J) (out : Fin N)
    (v : HS (liveDescriptorT N J) Q A U) (S : Stacks (liveDescriptorT N J) A)
    (h : LiveDescriptorReady p X hG hK active s mode w S.R)
    (hpositive : 0 < repairCompactRows p (mode j).key) :
    ∃ (v' : HS (liveDescriptorT N J) Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ (mode j).backendCost p X hG hK active s w.indexBits w.groupBits w.strideBits w.selectorBits w.widthBits ∧
      Exec body (liveDescriptorBackend (mode j) j out) (mk v S) steps
        (mk v' { S with R := Function.update S.R (liveDescriptorCore out) (repairDescriptorWord p X hG hK active s (mode j).key ++ S.R (liveDescriptorCore out)) }) := by
  cases hm : mode j with
  | affine key hkey =>
    obtain ⟨v', steps, hu, ht, he⟩ := liveAffineDescriptor_exec body p X hG hK active s mode w j out key hkey hm
      (by simpa only [hm, LiveDescriptorMode.key] using hpositive) v S h
    refine ⟨v', steps, hu, by simpa only [hm] using ht, ?_⟩
    simpa only [hm, liveDescriptorBackend, LiveDescriptorMode.key] using he
  | grouped k =>
    obtain ⟨v', steps, hu, ht, he⟩ := liveGroupedDescriptor_exec body p X hG hK hGK active s mode w j out k hm
      (by simpa only [hm, LiveDescriptorMode.key, repairCompactRows, selectiveTargetWidth] using hpositive) v S h
    refine ⟨v', steps, hu, by simpa only [hm] using ht, ?_⟩
    simpa only [hm, liveDescriptorBackend, LiveDescriptorMode.key] using he

def liveDescriptorCost (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) (w : LiveDescriptorWidths) (mode : LiveDescriptorMode) : ℕ :=
  14 * w.coordinateBits + 16 + mode.backendCost p X hG hK active s
    w.indexBits w.groupBits w.strideBits w.selectorBits w.widthBits

theorem liveDescriptorCost_le (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (hGK : p.G < p.K) (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)
    (w : LiveDescriptorWidths) (mode : LiveDescriptorMode)
    (hfit : repairCompactRows p mode.key < 2 ^ w.coordinateBits) :
    liveDescriptorCost p X hG hK active s w mode ≤ 14 * w.coordinateBits + 16 +
      mode.backendBound p X w.indexBits w.groupBits w.strideBits w.selectorBits w.widthBits :=
  Nat.add_le_add_left (mode.backendCost_le p X hG hK hGK active s
    w.indexBits w.groupBits w.strideBits w.selectorBits w.widthBits hfit) _

theorem liveDescriptor_exec (body : P → Pr P (liveDescriptorT N J) Q A U)
    (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K) (hGK : p.G < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)
    (mode : Fin J → LiveDescriptorMode) (w : LiveDescriptorWidths) (j : Fin J) (out : Fin N)
    (v : HS (liveDescriptorT N J) Q A U) (S : Stacks (liveDescriptorT N J) A)
    (h : LiveDescriptorReady p X hG hK active s mode w S.R) :
    ∃ (v' : HS (liveDescriptorT N J) Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ liveDescriptorCost p X hG hK active s w (mode j) ∧
      Exec body (liveDescriptorProgram (mode j) j out) (mk v S) steps
        (mk v' { S with R := Function.update S.R (liveDescriptorCore out) (repairDescriptorWord p X hG hK active s (mode j).key ++ S.R (liveDescriptorCore out)) }) := by
  exact repairDescriptorGuard_exec body p X hG hK active s (mode j).key
    (liveDescriptorAux (.rows j)) (liveBankProfile j (.coordinate (.arithmetic .dst)))
    (liveBankProfile j (.coordinate (.arithmetic .tx))) (liveBankProfile j (.coordinate (.arithmetic .ty)))
    (liveBankProfile j (.coordinate (.arithmetic .tz))) (liveBankProfile j (.coordinate .gap)) (liveDescriptorCore out)
    (by simp [List.nodup_cons, liveBankProfile, liveProfileRole, liveDescriptorAux_injective.eq_iff])
    (by simp [liveBankProfile, liveProfileRole, liveDescriptorAux_injective.eq_iff])
    (by simp [liveBankProfile, liveProfileRole, liveDescriptorAux_injective.eq_iff])
    w.coordinateBits ((mode j).backendCost p X hG hK active s w.indexBits w.groupBits w.strideBits w.selectorBits w.widthBits)
    (h.bounds j).coordinate_fits (liveDescriptorBackend (mode j) j out) v S (h.rows j)
    (h.profile_blank j _ (by simp [groupedProfileLive])) (h.profile_blank j _ (by simp [groupedProfileLive]))
    (h.profile_blank j _ (by simp [groupedProfileLive])) (h.profile_blank j _ (by simp [groupedProfileLive]))
    (fun v hp => liveDescriptorBackend_exec body p X hG hK hGK active s mode w j out v S h hp)

end
end IntegerMultBounds.MathlibTM2.Routing
