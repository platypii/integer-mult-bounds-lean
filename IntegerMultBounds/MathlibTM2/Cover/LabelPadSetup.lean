module

public import IntegerMultBounds.MathlibTM2.Cover.LabelDimensions
public import IntegerMultBounds.MathlibTM2.Cover.LabelCountBank
public import IntegerMultBounds.MathlibTM2.Cover.LabelPadProgram

/-! Padding initialized from the six unary descriptor fields and the atom width. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.LabelPadSetup
noncomputable section
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open Host Node LabelTraversal LabelStock LabelTransport LabelMask
open RecursiveInterchangeLayout (Descriptor volume)
variable {T Q A : ℕ} {P U : Type}

def dimensions (r : Fin 19 ↪ Fin T) : Fin 13 ↪ Fin T :=
  ⟨fun i => r (Fin.castLE (by decide) i),fun _ _ h => Fin.ext (congrArg (Fin.val (n := 19)) (r.injective h))⟩

private theorem cost_le (v : Descriptor) (hp : v.Positive) {m w B : ℕ} (hm : 0 < m)
    (hv : v.beforeH = B*prime^(m*(w*m))) :
    14*volume prime v + (60+10*(m*m))*records v + 37*payload v + 13*w + 26*prime^(w-1)+44 ≤
      (194+10*(m*m))*volume prime v := by
  have hprime := IntegerMultBounds.Networks.Shared50ModularControl.prime_prime
  have hR : 0 < records v := Nat.mul_pos (Nat.mul_pos hp.1 hp.2.1) hp.2.2.1
  have hP : 0 < payload v := by
    unfold payload
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (pow_pos hprime.pos _) hp.2.2.2.1)
      (pow_pos hprime.pos _)) hp.2.2.2.2
  have hV : records v * payload v = volume prime v := by unfold records payload volume; ring
  have hRV := hV ▸ Nat.le_mul_of_pos_right (records v) hP
  have hPV := hV ▸ Nat.le_mul_of_pos_left (payload v) hR
  have hpow : prime^(w-1) ≤ prime^(m*(w*m)) := by
    apply Nat.pow_le_pow_right hprime.pos
    exact (Nat.sub_le _ _).trans ((Nat.le_mul_of_pos_right w hm).trans (Nat.le_mul_of_pos_left _ hm))
  have hb : 0 < B := by by_contra! h; have := hp.2.2.1; simp [show B = 0 by omega] at hv; omega
  have hbefore : v.beforeH ≤ records v := Nat.le_mul_of_pos_left _ (Nat.mul_pos hp.1 hp.2.1)
  have hH := hpow.trans ((hv ▸ Nat.le_mul_of_pos_left _ hb).trans (hbefore.trans hRV))
  have he : w ≤ m*(w*m) := (Nat.le_mul_of_pos_right w hm).trans (Nat.le_mul_of_pos_left _ hm)
  have hwV := (he.trans (Nat.lt_pow_self hprime.one_lt).le).trans
    ((hv ▸ Nat.le_mul_of_pos_left _ hb).trans (hbefore.trans hRV))
  have hn := Nat.mul_le_mul_left (60+10*(m*m)) hRV
  nlinarith only [hn,hPV,hwV,hH,hRV,hR]

theorem realizes (body : P → Pr P T Q A U) (r : Fin 19 ↪ Fin T) (m : ℕ) (hm : 0 < m)
    (rs : List (Pair T)) (hk : rs.length = m*m) (hd : (slots rs).Nodup)
    (apart : ∀ i, r i ∉ slots rs) :
    ∃ p : Pr P T Q A U, ∀ (v : Descriptor) (w B : ℕ), 0 < w → v.Positive →
      v.beforeH = B*prime^(m*(w*m)) → ∀ (bit : ℕ → Bool) (u : HS T Q A U) (S : Stacks T A),
      LabelDimensions.inputs (dimensions r) S.R v w → S.R (r 6) = List.replicate w tick →
      (S.R (r 14)).length = 1 → (∀ i : Fin 19, 7 ≤ i.val → i.val ≤ 16 → i ≠ 14 → S.R (r i) = []) →
      (∀ k ∈ slots rs, S.R k = []) →
      let xs := List.range (volume prime v)
      let keep := live m w (payload v)
      S.R (r 17) = ((xs.filter keep).map bit).map bitSymbol →
      ∃ z F c, z.user = u.user ∧
        F.R (r 18) = (xs.map (fun i => bitSymbol (if keep i then bit i else false))) ++ S.R (r 18) ∧
        F.R (r 17) = S.R (r 17) ∧ F.R (r 16) = (xs.map keep).map bitSymbol ∧
        c ≤ (194+10*(m*m))*volume prime v ∧
        Exec body p (mk u S) c (mk z F) := by
  have hslots (i j : Fin 19) (hij : i ≠ j) : (r i :: r j :: slots rs).Nodup := by
    simp [hij,apart,hd]
  have ht : (r 7 :: r 9 :: (slots rs ++ [r 15])).Nodup := by
    simp [List.nodup_append,apart,hd]
    exact fun k h e => apart 15 (e ▸ h)
  obtain ⟨pad,hpad⟩ := LabelPadProgram.realizes body m rs hk (r 7) (r 9) (r 15) (r 8)
    (r 10) (r 11) (r 12) (r 16) (r 17) (r 18) ht (by simp)
  refine ⟨.seq (LabelDimensions.program m (dimensions r)) (.seq
    (.seq (LabelCounts.highCount (r 14) (r 6) (r 13) (r 9) (r 10) (r 11))
      (scanR (r 13) (r 9) (LabelCountBank.pushAll (rs.map Prod.fst)))) pad), ?_⟩
  intro v w B hw hp hv bit u S hin hwidth hone hf hs
  dsimp only
  intro hx
  obtain ⟨u₁,c₁,hu₁,hc₁,he₁⟩ := LabelDimensions.runs body (dimensions r) m w B hm v hp hv u S hin
    (fun i hi => hf (Fin.castLE (by decide) i) hi (by change i.val ≤ 16; omega)
      (by intro h; have e := congrArg Fin.val h; change i.val = 14 at e; omega))
  let M : Stacks T A := {S with R := Function.update (Function.update S.R (r 7)
    (List.replicate (v.beforeRows*v.rows*B) tick)) (r 8) (List.replicate (payload v) tick)}
  have same (i : Fin 19) (h7 : i ≠ 7) (h8 : i ≠ 8) : M.R (r i) = S.R (r i) := by simp [M,h7,h8]
  obtain ⟨hready,u₂,c₂,hu₂,hc₂,he₂⟩ := LabelCountBank.prepare_exec body rs (r 14) (r 6) (r 13)
    (r 9) (r 10) (r 11) (by simp) (hslots _ _ (by decide)) u₁ M w hw
    ((same 6 (by decide) (by decide)).trans hwidth)
    ((congrArg List.length (same 14 (by decide) (by decide))).trans hone) (by
      intro k h
      rcases List.mem_append.mp h with h | h
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at h
        rcases h with rfl | rfl | rfl | rfl <;> exact (same _ (by decide) (by decide)).trans (hf _ (by decide) (by decide) (by decide))
      · have ne (i : Fin 19) : k ≠ r i := fun e => apart i (e ▸ h)
        simpa [M,ne] using hs k h)
  let N : Stacks T A := {M with R := LabelCountBank.fill (rs.map Prod.fst) (prime^(w-1)) (Function.update M.R (r 13) (List.replicate (prime^(w-1)) tick))}
  have same' (i : Fin 19) (hi : i ≠ 13) : N.R (r i) = M.R (r i) := by
    have hn : r i ∉ rs.map Prod.fst := by
      intro h
      obtain ⟨a,ha,e⟩ := List.mem_map.mp h
      exact apart i (List.mem_flatMap.mpr ⟨a,ha,by simp [e]⟩)
    simp [N,LabelCountBank.fill,hn,hi]
  have orig (i : Fin 19) (h7 : i ≠ 7) (h8 : i ≠ 8) (h13 : i ≠ 13) :=
    (same' i h13).trans (same i h7 h8)
  obtain ⟨z,c₃,hu₃,hc₃,he₃⟩ := hpad v w B hw hv bit u₂ N hready
    ((orig 9 (by decide) (by decide) (by decide)).trans (hf _ (by decide) (by decide) (by decide)))
    (by rw [same' 7 (by decide)]; simp [M]) (by rw [same' 8 (by decide)]; simp [M])
    (by intro k h; simp only [List.mem_cons,List.not_mem_nil,or_false] at h
        rcases h with rfl | rfl | rfl | rfl | rfl <;>
          exact (orig _ (by decide) (by decide) (by decide)).trans (hf _ (by decide) (by decide) (by decide)))
    ((orig 17 (by decide) (by decide) (by decide)).trans hx)
  refine ⟨z,_,c₁+(c₂+c₃),hu₃.trans (hu₂.trans hu₁),?_,?_,?_,?_,Exec.seq he₁ (Exec.seq he₂ he₃)⟩
  · simp [orig]
  · simp [orig]
  · simp
  · refine le_trans ?_ (cost_le v hp hm hv)
    nlinarith only [hc₁,hc₂,hc₃]

end
end IntegerMultBounds.MathlibTM2.Cover.LabelPadSetup
