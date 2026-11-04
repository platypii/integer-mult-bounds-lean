module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBinaryHeaderFormat

/-! One computed scalar supplies every consumer's binary format. Reuse the
ordinary header-copy endpoint, including its read and frame lemmas. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type}

/-- Pairs contain a retained width ruler and a fresh destination. -/
def copyBinaryFormats (src saved tmp : Fin T) : List (Fin T × Fin T) → Pr P T Q A U
  | [] => .act .done
  | (count,dst)::rs => .seq (copyPrefix count src dst saved tmp) (copyBinaryFormats src saved tmp rs)

def binaryFormatsCost (width : Fin T → ℕ) (rs : List (Fin T × Fin T)) : ℕ :=
  (rs.map (fun r => 10*width r.1+10)).sum+1

theorem copyBinaryFormats_native (src saved tmp : Fin T) (rs : List (Fin T × Fin T)) :
    mnNativePushBound 3 (copyBinaryFormats (P := P) (Q := Q) (A := A) (U := U) src saved tmp rs) := by
  induction rs with
  | nil => exact Nat.zero_le _
  | cons r rs ih => exact ⟨copyBinaryHeader_native _ _ _ _ _,ih⟩

theorem copyBinaryFormats_exec (body : P → Pr P T Q A U)
    (src saved tmp : Fin T) (rs : List (Fin T × Fin T))
    (hregs : ∀ r ∈ rs, [r.1,src,r.2,saved,tmp].Nodup)
    (hsep : ∀ r ∈ rs, ∀ p ∈ rs, r.2 ≠ p.1)
    (hnd : (rs.map Prod.snd).Nodup) (D x : ℕ) (width : Fin T → ℕ)
    (hfit : ∀ r ∈ rs, width r.1 ≤ D)
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = binSyms D x)
    (hcount : ∀ r ∈ rs, (S.R r.1).length = width r.1)
    (hblank : ∀ r ∈ rs, S.R r.2 = []) (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (copyBinaryFormats src saved tmp rs) (mk v S) (binaryFormatsCost width rs)
        (mk v' {S with R := copyWordHeadersR (fun k => binSyms (width k) x) rs S.R}) := by
  induction rs generalizing v S with
  | nil =>
    exact ⟨v,rfl,by simpa [copyBinaryFormats,binaryFormatsCost,copyWordHeadersR] using (Exec.act (body := body) .done (mk v S))⟩
  | cons r rs ih =>
    have hr := hregs r (by simp)
    regs_ne hr
    obtain ⟨v₁,hu₁,hw₁⟩ := copyBinaryHeader_exec_within body r.1 src r.2 saved tmp
      (hregs r (by simp)) (width r.1) D x (hfit r (by simp)) v S
      (hcount r (by simp)) hsrc (hblank r (by simp)) hsaved htmp 0
    let M : Stacks T A := {S with R := Function.update S.R r.2 (binSyms (width r.1) x)}
    have htail : ∀ p ∈ rs, p.2 ≠ r.2 := by
      intro p hp he
      exact (List.nodup_cons.mp hnd).1 (List.mem_map.mpr ⟨p,hp,he⟩)
    obtain ⟨v₂,hu₂,he₂⟩ := ih (fun p hp => hregs p (by simp [hp]))
      (fun p hp q hq => hsep p (by simp [hp]) q (by simp [hq]))
      (List.nodup_cons.mp hnd).2 (fun p hp => hfit p (by simp [hp])) v₁ M
      (by simpa [M,‹src ≠ r.2›] using hsrc)
      (by intro p hp; simpa [M,(hsep r (by simp) p (by simp [hp])).symm] using hcount p (by simp [hp]))
      (by intro p hp; simpa [M,htail p hp] using hblank p (by simp [hp]))
      (by simpa [M,‹r.2 ≠ saved›.symm] using hsaved)
      (by simpa [M,‹r.2 ≠ tmp›.symm] using htmp)
    refine ⟨v₂,hu₂.trans hu₁,(Exec.seq hw₁.toExec he₂).cast ?_ ?_⟩
    · simp [binaryFormatsCost]; omega
    · simp only [copyWordHeadersR,hblank r (by simp),List.append_nil]; rfl

theorem copyBinaryFormats_exec_within (body : P → Pr P T Q A U)
    (src saved tmp : Fin T) (rs : List (Fin T × Fin T))
    (hregs : ∀ r ∈ rs, [r.1,src,r.2,saved,tmp].Nodup)
    (hsep : ∀ r ∈ rs, ∀ p ∈ rs, r.2 ≠ p.1)
    (hnd : (rs.map Prod.snd).Nodup) (D x : ℕ) (width : Fin T → ℕ)
    (hfit : ∀ r ∈ rs, width r.1 ≤ D)
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = binSyms D x)
    (hcount : ∀ r ∈ rs, (S.R r.1).length = width r.1)
    (hblank : ∀ r ∈ rs, S.R r.2 = []) (hsaved : S.R saved = []) (htmp : S.R tmp = []) (depth : ℕ) :
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+3*binaryFormatsCost width rs) depth
        (copyBinaryFormats src saved tmp rs) (mk v S) (binaryFormatsCost width rs)
        (mk v' {S with R := copyWordHeadersR (fun k => binSyms (width k) x) rs S.R}) := by
  obtain ⟨v',hu,he⟩ := copyBinaryFormats_exec body src saved tmp rs hregs hsep hnd D x width hfit
    v S hsrc hcount hblank hsaved htmp
  exact ⟨v',hu,mn_native_exec_within he 3 (copyBinaryFormats_native _ _ _ _) depth _ (by omega)⟩

/-- Numerical initialization, exposure and routing consume three formats. -/
def classHaloFormats (count dst : Fin 3 → Fin T) : List (Fin T × Fin T) :=
  List.ofFn (fun j => (count j,dst j))

theorem classHaloFormats_cost (count dst : Fin 3 → Fin T) (width : Fin T → ℕ) :
    binaryFormatsCost width (classHaloFormats count dst) =
      10*(width (count 0)+width (count 1)+width (count 2))+31 := by
  simp [binaryFormatsCost,classHaloFormats,List.ofFn_succ]; omega

/-- Export the same computed halo to all three consumers, restoring every
source, ruler and scratch port. No halo value is supplied as an output word. -/
theorem classHaloFormats_exec_within (body : P → Pr P T Q A U)
    (src saved tmp : Fin T) (count dst : Fin 3 → Fin T)
    (hregs : ∀ j, [count j,src,dst j,saved,tmp].Nodup)
    (hsep : ∀ i j, dst i ≠ count j) (hdst : Function.Injective dst)
    (D x : ℕ) (width : Fin T → ℕ) (hfit : ∀ j, width (count j) ≤ D)
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = binSyms D x)
    (hcount : ∀ j, (S.R (count j)).length = width (count j))
    (hblank : ∀ j, S.R (dst j) = []) (hsaved : S.R saved = []) (htmp : S.R tmp = []) (depth : ℕ) :
    let F := {S with R := copyWordHeadersR (fun k => binSyms (width k) x) (classHaloFormats count dst) S.R}
    let cost := 10*(width (count 0)+width (count 1)+width (count 2))+31
    ∃ v', v'.user = v.user ∧
      (∀ j, F.R (dst j) = binSyms (width (count j)) x) ∧
      (∀ k, (∀ j, dst j ≠ k) → F.R k = S.R k) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+3*cost) depth
        (copyBinaryFormats src saved tmp (classHaloFormats count dst)) (mk v S) cost (mk v' F) := by
  dsimp only
  have hnd : ((classHaloFormats count dst).map Prod.snd).Nodup := by
    simpa only [classHaloFormats,List.map_ofFn,Function.comp_def] using List.nodup_ofFn.mpr hdst
  obtain ⟨v',hu,he⟩ := copyBinaryFormats_exec_within body src saved tmp (classHaloFormats count dst)
    (by intro r hr; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hr; exact hregs j)
    (by intro r hr p hp; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
        obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hp; exact hsep i j)
    hnd D x width
    (by intro r hr; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hr; exact hfit j) v S hsrc
    (by intro r hr; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hr; exact hcount j)
    (by intro r hr; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hr; exact hblank j) hsaved htmp depth
  rw [classHaloFormats_cost] at he
  refine ⟨v',hu,?_,?_,he⟩
  · intro j
    have hget := copyWordHeadersR_get (fun k => binSyms (width k) x) (classHaloFormats count dst)
      hnd S.R (count j,dst j) (List.mem_ofFn.mpr ⟨j,rfl⟩)
    simpa only [hblank j,List.append_nil] using hget
  · intro k hk
    exact copyWordHeadersR_off _ _ _ k (by
      intro r hr; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hr; exact hk j)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
