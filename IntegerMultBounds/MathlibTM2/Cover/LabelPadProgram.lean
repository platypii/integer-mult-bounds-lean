module

public import IntegerMultBounds.MathlibTM2.Cover.LabelTraversal

/-! Initialize padded stock from compact bits and unary dimensions. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.LabelPadProgram
noncomputable section

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
open RecursiveInterchangeLayout (Descriptor volume)
open Host LabelTraversal LabelMask LabelStock LabelTransport
variable {T Q A : ℕ} {P U : Type}

theorem selector_cost (v : Descriptor) (m w B : ℕ) (hw : 0 < w)
    (hv : v.beforeH = B*prime^(m*(w*m))) :
    (v.beforeRows*v.rows*B)*(time (prime^(w-1)) (m*m) 1+5)+4 ≤
      (6+10*(m*m))*records v+4 := by
  have hp : prime^(w-1)*prime = prime^w := by rw [← pow_succ]; congr 1; omega
  have ht := time_le (pow_pos prime_prime.pos (w-1)) (m*m) 1
  rw [hp, ← pow_mul, show w*(m*m) = m*(w*m) by ring] at ht
  let N := prime^(m*(w*m))
  have hN : 0 < N := pow_pos prime_prime.pos _
  have h : time (prime^(w-1)) (m*m) 1 + 5 ≤ (6+10*(m*m))*N := by
    change _ ≤ (1+10*(m*m))*N at ht
    nlinarith
  have := Nat.mul_le_mul_left (v.beforeRows*v.rows*B) h
  unfold records
  rw [hv]
  dsimp [N] at *
  nlinarith only [this]

theorem realizes (body : P → Pr P T Q A U) (m : ℕ) (rs : List (Pair T)) (hk : rs.length = m*m)
    (count saved labels width ts tm dst mask src out : Fin T)
    (ht : (count :: saved :: (slots rs ++ [labels])).Nodup)
    (hr : [labels,width,ts,tm,dst,mask,src,out].Nodup) :
    ∃ p : Pr P T Q A U, ∀ (v : Descriptor) (w B : ℕ), 0 < w →
      v.beforeH = B*prime^(m*(w*m)) → ∀ (bit : ℕ → Bool) (u : HS T Q A U) (S : Stacks T A),
      ready (prime^(w-1)) S.R rs → S.R saved = [] → (S.R count).length = v.beforeRows*v.rows*B →
      (S.R width).length = payload v → (∀ k ∈ [labels,ts,tm,dst,mask], S.R k = []) →
      let xs := List.range (volume prime v)
      let keep := live m w (payload v)
      S.R src = ((xs.filter keep).map bit).map bitSymbol →
      let R := Function.update S.R labels ((selectors m w (records v)).map bitSymbol)
      let R' := Function.update R mask ((xs.map keep).map bitSymbol)
      ∃ u' n, u'.user = u.user ∧ n ≤ 14*volume prime v + (16+10*(m*m))*records v + 18 ∧
        Exec body p (mk u S) n (mk u' { S with R := Function.update R' out ((xs.map (fun i => bitSymbol (if keep i then bit i else false))) ++ S.R out) }) := by
  obtain ⟨gen, hg⟩ := record_writes (body := body) m rs hk labels count saved ht
  refine ⟨.seq gen (.seq (expandMask labels width ts tm dst mask symBit) (spread src mask ts tm dst out)), ?_⟩
  intro v w B hw hv bit u S hready hs hc hwidth hf
  dsimp only
  intro hx
  obtain ⟨u₁, n₁, hu₁, hn₁, he₁⟩ := hg v w B hw hv u S ⟨hready,hs,hc⟩
  simp only [hf labels (by simp), List.append_nil] at he₁
  let S₁ : Stacks T A := {S with R := Function.update S.R labels ((selectors m w (records v)).map bitSymbol)}
  regs_ne hr
  have fresh (k) (hk : k ∈ [ts,tm,dst]) : S₁.R k = [] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl <;> simp [S₁, ne_comm, *, hf k (by simp)]
  obtain ⟨u₂, n₂, hu₂, hn₂, he₂⟩ := pad_exec body (labels := labels) (width := width) (ts := ts) (tm := tm) (dst := dst)
    (mask := mask) (src := src) (out := out) (by simp_all)
    (by simp_all [GSRegs,ne_comm]) v m w bit u₁ S₁ (Function.update_self ..)
    (by simpa [S₁,Ne.symm ‹labels ≠ width›] using hwidth) fresh
    (by simpa [S₁,Ne.symm ‹labels ≠ mask›] using hf mask (by simp))
    (by simpa [S₁,Ne.symm ‹labels ≠ src›] using hx)
  refine ⟨u₂, n₁+n₂, hu₂.trans hu₁, ?_, ?_⟩
  · have := hn₁.trans (selector_cost v m w B hw hv)
    nlinarith only [this, hn₂]
  · simpa only [S₁,Function.update_of_ne (Ne.symm ‹labels ≠ out›)] using Exec.seq he₁ he₂

end
end IntegerMultBounds.MathlibTM2.Cover.LabelPadProgram
