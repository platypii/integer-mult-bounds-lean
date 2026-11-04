module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBinaryHeaderFormats
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareCommonClassMasters

/-! Initialize and retire a class with independently formatted halo headers.
A shared computed halo supplies every consumer; all owned words return to blank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv CommonClassGeometry
variable {T Q A : ℕ} {P U : Type}

theorem retireBinaryFormats_exec_within (body : P → Pr P T Q A U)
    (rs : List (Fin T × Fin T)) (hnd : (rs.map Prod.snd).Nodup)
    (bits : Fin T → ℕ) (x : ℕ) (output : Fin T)
    (hout : ∀ r ∈ rs, r.2 ≠ output) (ys : List (Fin (A+4)))
    (v : HS T Q A U) (S : Stacks T A) (hblank : ∀ r ∈ rs, S.R r.2 = []) (depth : ℕ) :
    let M := {S with R := copyWordHeadersR (fun k => binSyms (bits k) x) rs S.R}
    let F := {M with R := Function.update M.R output ys}
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v F)+depth+0) depth
        (clearWords (rs.map Prod.snd)) (mk v F)
        (2*(rs.map (fun r => bits r.1)).sum+2*rs.length+1)
        (mk v' {S with R := Function.update S.R output ys}) := by
  dsimp only
  let M : Stacks T A := {S with R := copyWordHeadersR (fun k => binSyms (bits k) x) rs S.R}
  let F : Stacks T A := {M with R := Function.update M.R output ys}
  have hword (r) (hr : r ∈ rs) : F.R r.2 = binSyms (bits r.1) x := by
    rw [show F.R r.2 = M.R r.2 from Function.update_of_ne (hout r hr) _ _]
    simpa only [hblank r hr,List.append_nil] using
      copyWordHeadersR_get (fun k => binSyms (bits k) x) rs hnd S.R r hr
  obtain ⟨v',hu,he⟩ := clearWords_exec (body := body) (rs.map Prod.snd) hnd v F
  have hvolume : ((rs.map Prod.snd).map (fun k => (F.R k).length)).sum =
      (rs.map (fun r => bits r.1)).sum := by
    rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro r hr
    simp only [Function.comp_apply,hword r hr,length_binSyms]
  rw [hvolume,List.length_map] at he
  have hend : {F with R := fun k => if k ∈ rs.map Prod.snd then [] else F.R k} =
      {S with R := Function.update S.R output ys} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk : k ∈ rs.map Prod.snd
    · obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hk
      simp only [ite_eq_left (List.mem_map.mpr ⟨r,hr,rfl⟩),Function.update_of_ne (hout r hr),hblank r hr]
    · have hM : M.R k = S.R k := copyWordHeadersR_off _ rs S.R k
        (by intro r hr heq; exact hk (List.mem_map.mpr ⟨r,hr,heq⟩))
      simp [hk,F,hM,Function.update_apply]
  rw [hend] at he
  exact ⟨v',hu,mn_native_exec_within he 0 (clearWords_native _) depth _
    (by simp only [Nat.zero_mul,Nat.add_zero]; exact le_rfl)⟩

def formattedClassLoaded (core halo : Fin T) (D : ℕ) (clipped : Bool) (s width radius : ℕ)
    (bits : Fin T → ℕ) (rs : List (Fin T × Fin T)) (S : Stacks T A) : Stacks T A :=
  let M := masterLoaded core halo D clipped s width radius S
  {M with R := copyWordHeadersR (fun k => binSyms (bits k) (haloRows clipped s width radius)) rs M.R}

theorem prepareFormattedClass_exec_within (body : P → Pr P T Q A U) (rg : TblR 13 → Fin T) (hinj : Function.Injective rg)
    (globals : Fin 11 → Fin T) (zero widthMaster core halo : Fin T)
    (hwidthOff : ∀ r, rg r ≠ widthMaster) (hzeroOff : ∀ r, rg r ≠ zero)
    (hglobalOff : ∀ j r, rg r ≠ globals j) (hoff : ∀ j, globals j ≠ zero)
    (hne : core ≠ halo) (hcoreOff : ∀ r, rg r ≠ core) (hhaloOff : ∀ r, rg r ≠ halo)
    (rs : List (Fin T × Fin T)) (saved tmp : Fin T) (bits : Fin T → ℕ)
    (hregs : ∀ r ∈ rs, [r.1,halo,r.2,saved,tmp].Nodup)
    (hsep : ∀ r ∈ rs, ∀ p ∈ rs, r.2 ≠ p.1) (hnd : (rs.map Prod.snd).Nodup)
    (hheaderOff : ∀ r ∈ rs, r.2 ≠ core ∧ r.2 ≠ halo)
    (hworkOff : ∀ k ∈ rs.map Prod.fst ++ [saved,tmp], k ≠ core ∧ k ≠ halo)
    (clipped : Bool) (D p u l target s t B W N radius width : ℕ) (value : Fin T → ℕ)
    (hbitsFit : ∀ r ∈ rs, bits r.1 ≤ D)
    (hvalues : ∀ j, value (globals j) = globalValues p u l target s t B W N radius width j)
    (hfit : ∀ j, value (globals j) < 2^D) (hwidth : 0 < width) (hgeometryFit : width+2*radius < 2^D)
    (v : HS T Q A U) (S : Stacks T A)
    (hwidthWord : (S.R widthMaster).length = D) (hzero : S.R zero = [])
    (hwords : ∀ j, S.R (globals j) = binSyms D (value (globals j)))
    (hblank : ∀ r, S.R (rg r) = []) (hcore : S.R core = []) (hhalo : S.R halo = [])
    (hheaders : ∀ r ∈ rs, S.R r.2 = [])
    (hcounts : ∀ r ∈ rs, (S.R r.1).length = bits r.1)
    (hsaved : S.R saved = []) (htmp : S.R tmp = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ prepareMastersTimeCost D+binaryFormatsCost bits rs ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+(prepareMastersStock D+3*binaryFormatsCost bits rs)) depth
        (.seq (prepareMasters rg globals zero widthMaster clipped core halo) (copyBinaryFormats halo saved tmp rs)) (mk v S) n
        (mk v' (formattedClassLoaded core halo D clipped s width radius bits rs S)) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := prepareMasters_exec_within body rg hinj globals zero widthMaster
    core halo hwidthOff hzeroOff hglobalOff hoff hne hcoreOff hhaloOff clipped D p u l target s t B W N
    radius width value hvalues hfit hwidth hgeometryFit v S hwidthWord hzero hwords hblank hcore hhalo depth
  let M := masterLoaded core halo D clipped s width radius S
  have hframe (k : Fin T) (hk : k ≠ core ∧ k ≠ halo) : M.R k = S.R k := by
    simp only [M,masterLoaded,Function.update_of_ne hk.1,Function.update_of_ne hk.2]
  obtain ⟨v₂,hu₂,he₂⟩ := copyBinaryFormats_exec_within body halo saved tmp rs hregs hsep hnd
    D (haloRows clipped s width radius) bits hbitsFit v₁ M (by simp [M,masterLoaded])
    (by intro r hr; rw [hframe r.1 (hworkOff r.1 (List.mem_append_left _ (List.mem_map.mpr ⟨r,hr,rfl⟩)))]
        exact hcounts r hr)
    (by intro r hr; exact (hframe r.2 (hheaderOff r hr)).trans (hheaders r hr))
    ((hframe saved (hworkOff saved (by simp))).trans hsaved)
    ((hframe tmp (hworkOff tmp (by simp))).trans htmp) depth
  refine ⟨v₂,n₁+binaryFormatsCost bits rs,hu₂.trans hu₁,Nat.add_le_add_right hn₁ _,?_⟩
  simpa only [formattedClassLoaded,M] using mn_seq_within_add he₁ he₂

theorem retireFormattedClass_exec_within (body : P → Pr P T Q A U)
    (core halo output : Fin T) (hne : core ≠ halo) (houtCore : output ≠ core) (houtHalo : output ≠ halo)
    (rs : List (Fin T × Fin T)) (hnd : (rs.map Prod.snd).Nodup)
    (hoff : ∀ r ∈ rs, r.2 ≠ core ∧ r.2 ≠ halo) (hout : ∀ r ∈ rs, r.2 ≠ output)
    (bits : Fin T → ℕ) (D : ℕ) (clipped : Bool) (s width radius : ℕ)
    (ys : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hcore : S.R core = []) (hhalo : S.R halo = []) (hblank : ∀ r ∈ rs, S.R r.2 = []) (depth : ℕ) :
    let M := formattedClassLoaded core halo D clipped s width radius bits rs S
    let F := {M with R := Function.update M.R output ys}
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v F)+depth+0) depth
        (.seq (clearWords (rs.map Prod.snd)) (clearWords [core,halo])) (mk v F)
        ((2*(rs.map (fun r => bits r.1)).sum+2*rs.length+1)+(4*D+5))
        (mk v' {S with R := Function.update S.R output ys}) := by
  dsimp only
  let M := masterLoaded core halo D clipped s width radius S
  obtain ⟨v₁,hu₁,he₁⟩ := retireBinaryFormats_exec_within body rs hnd bits
    (haloRows clipped s width radius) output hout ys v M
    (by intro r hr; simpa only [M,masterLoaded,Function.update_of_ne (hoff r hr).1,
        Function.update_of_ne (hoff r hr).2] using hblank r hr) depth
  obtain ⟨v₂,hu₂,he₂⟩ := master_retire_exec_within body core halo output hne houtCore houtHalo
    D clipped s width radius ys v₁ S hcore hhalo depth
  exact ⟨v₂,hu₂.trans hu₁,by simpa only [formattedClassLoaded,M,Nat.add_zero] using mn_seq_within_add he₁ he₂⟩

/-- Five owned words: two masters and the three independently sized headers. -/
theorem classHaloFormats_retireCost (D : ℕ) (count dst : Fin 3 → Fin T) (bits : Fin T → ℕ) :
    (2*((classHaloFormats count dst).map (fun r => bits r.1)).sum+
      2*(classHaloFormats count dst).length+1)+(4*D+5) =
      4*D+2*(bits (count 0)+bits (count 1)+bits (count 2))+12 := by
  simp [classHaloFormats,List.ofFn_succ]; omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
