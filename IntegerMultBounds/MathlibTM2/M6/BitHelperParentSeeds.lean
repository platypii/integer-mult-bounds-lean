module

public import IntegerMultBounds.MathlibTM2.M6.BitHelperLabelHeaders

/-! Compute the helper's spectator volume and its labelled volume from the parent's row factors. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open Shared50ModularControl (prime)
variable {T Q : ℕ} {P U : Type}

private theorem seedProduct_exec (body : P → Pr P T Q prime U) (r : Fin 11 ↪ Fin T)
    (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (u : HS T Q prime U) (S : Stacks T prime)
    (x : S.R (r 0) = binSyms a.size a) (y : S.R (r 1) = binSyms b.size b)
    (z : S.R (r 2) = binSyms c.size c) (free : ∀ i : Fin 11, 3 ≤ i → i < 10 → S.R (r i) = []) :
    ∃ v t, v.user = u.user ∧ t ≤ 432*(a*b*c) ∧ Exec body (middleRowDescriptor r) (mk u S) t
      (mk v {S with R := Function.update S.R (r 4) (binSyms (a*b*c).size (a*b*c))}) := by
  obtain ⟨bs,v,t,canonical,value,user,paid,run⟩ :=
    middleRowDescriptor_exec body r a b c ha hb hc u S x y z free
  have eq := BinaryCanonicalData.value_injective bs _ canonical (FlatCoordinateSchedule.bits_canonical (a*b*c))
    (value.trans (FlatCoordinateSchedule.bits_value _).symm)
  rw [eq,canonicalBits_symbols] at run
  exact ⟨v,t,user,paid,run⟩

/-- Slots 268 through 271 hold the parent row factors. Slot 272 holds their
partial product outside the 268-register packing archive. -/
def helperRowFactors : Fin 11 ↪ Fin 273 := ⟨![268,269,270,5,272,6,7,8,9,10,11],by decide⟩
def helperExteriorFactors : Fin 11 ↪ Fin 273 := ⟨![272,271,1,5,2,6,7,8,9,10,11],by decide⟩
def helperLabelFactors : Fin 11 ↪ Fin 273 := ⟨![12,2,1,5,13,6,7,8,9,10,11],by decide⟩

noncomputable def helperParentProducts (r : Fin 273 ↪ Fin T) : Pr P T Q prime U :=
  .seq (middleRowDescriptor (helperRowFactors.trans r))
    (.seq (middleRowDescriptor (helperExteriorFactors.trans r)) (middleRowDescriptor (helperLabelFactors.trans r)))

theorem helperParentProducts_exec (body : P → Pr P T Q prime U) (r : Fin 273 ↪ Fin T)
    (a rows g d L : ℕ) (ha : 0 < a) (hr : 0 < rows) (hg : 0 < g) (hd : 0 < d) (hl : 0 < L)
    (u : HS T Q prime U) (S : Stacks T prime) :
    let W := a*rows*g*d
    let word := fun x : ℕ => binSyms (A := prime) x.size x
    S.R (r 268) = word a → S.R (r 269) = word rows → S.R (r 270) = word g →
    S.R (r 271) = word d → S.R (r 12) = word L → S.R (r 1) = word 1 →
    (∀ k : Fin 273, k.val ∈ [2,5,6,7,8,9,10,13,272] → S.R (r k) = []) →
    ∃ y n, y.user = u.user ∧ n ≤ 432*(a*rows*g)+432*W+432*(L*W) ∧
      Exec body (helperParentProducts r) (mk u S) n (mk y
        {S with R := Function.update (Function.update (Function.update S.R (r 272) (word (a*rows*g)))
          (r 2) (word W)) (r 13) (word (L*W))}) := by
  intro W word ax rx gx dx lx one empty
  have scratch (f : Fin 11 ↪ Fin 273)
      (ok : ∀ i : Fin 11, 3 ≤ i → i < 10 → (f i).val ∈ [2,5,6,7,8,9,10,13,272]) :=
    fun i lo hi => empty _ (ok i lo hi)
  obtain ⟨v,k,user,paid,first⟩ := seedProduct_exec body (helperRowFactors.trans r) a rows g ha hr hg u S
    ax rx gx (scratch _ (by decide))
  let A := {S with R := Function.update S.R (r 272) (word (a*rows*g))}
  have kept (i : Fin 273) (h : i ≠ 272) : A.R (r i) = S.R (r i) :=
    Function.update_of_ne (r.injective.ne h) _ _
  have pos := Nat.mul_pos (Nat.mul_pos ha hr) hg
  obtain ⟨v',m,same,cost,second⟩ := seedProduct_exec body (helperExteriorFactors.trans r) (a*rows*g) d 1
    pos hd (by decide) v A (Function.update_self ..) ((kept _ (by decide)).trans dx)
    ((kept _ (by decide)).trans one) (fun i lo hi => by
      have h : ∀ i : Fin 11, 3 ≤ i → i < 10 → helperExteriorFactors i ≠ 272 := by decide
      exact (kept _ (h i lo hi)).trans (scratch helperExteriorFactors (by decide) i lo hi))
  simp only [Nat.mul_one] at second cost
  let B := {A with R := Function.update A.R (r 2) (word W)}
  have saved (i : Fin 273) (h : i ≠ 2) (h' : i ≠ 272) : B.R (r i) = S.R (r i) :=
    (Function.update_of_ne (r.injective.ne h) _ _).trans (kept i h')
  obtain ⟨y,n,last,bill,third⟩ := seedProduct_exec body (helperLabelFactors.trans r) L W 1
    hl (Nat.mul_pos pos hd) (by decide) v' B ((saved _ (by decide) (by decide)).trans lx)
    (Function.update_self ..) ((saved _ (by decide) (by decide)).trans one) (fun i lo hi => by
      have h : ∀ i : Fin 11, 3 ≤ i → i < 10 → helperLabelFactors i ≠ 2 ∧ helperLabelFactors i ≠ 272 := by decide
      exact (saved _ (h i lo hi).1 (h i lo hi).2).trans (scratch helperLabelFactors (by decide) i lo hi))
  simp only [Nat.mul_one] at third bill
  exact ⟨y,k+(m+n),last.trans (same.trans user),by dsimp only [W] at *; omega,Exec.seq first (Exec.seq second third)⟩

/-- Starting with the radix, unit, width and parent's label word in the archive,
the parent row factors supply exactly the two missing packing seeds. -/
theorem helperParentSeed_exec (body : P → Pr P T Q prime U) (r : Fin 273 ↪ Fin T)
    (v : RecursiveInterchangeLayout.Descriptor) (rows w : ℕ) (pos : v.Positive) (hr : 0 < rows)
    (u : HS T Q prime U) (S : Stacks T prime) :
    let W := v.beforeRows*rows*v.between*v.afterD
    let word := fun x : ℕ => binSyms (A := prime) x.size x
    (∀ k : Fin 268, S.R (r (k.castAdd 5)) = helperArchiveSeed w v.beforeH 0 k) →
    S.R (r 268) = word v.beforeRows → S.R (r 269) = word rows → S.R (r 270) = word v.between →
    S.R (r 271) = word v.afterD → S.R (r 272) = [] →
    ∃ y F t, y.user = u.user ∧ Exec body (helperParentProducts r) (mk u S) t (mk y F) ∧
      t ≤ 432*(v.beforeRows*rows*v.between)+432*W+432*(v.beforeH*W) ∧ F.L = S.L ∧
      (∀ k : Fin 268, F.R (r (k.castAdd 5)) = helperArchiveSeed w v.beforeH W k) ∧
      ∀ p, p ≠ r 2 → p ≠ r 13 → p ≠ r 272 → F.R p = S.R p := by
  intro W word archive ax rx gx dx free
  have start (k : Fin 273) (low : k.val < 268) :
      S.R (r k) = helperArchiveSeed w v.beforeH 0 ⟨k.val,low⟩ := archive ⟨k.val,low⟩
  obtain ⟨y,t,user,time,run⟩ := helperParentProducts_exec body r _ _ _ _ _ pos.1 hr pos.2.2.2.1
    pos.2.2.2.2 pos.2.2.1 u S ax rx gx dx (start 12 (by decide)) (start 1 (by decide)) (fun k used => by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at used
      rcases used with h|h|h|h|h|h|h|h|h
      all_goals first | exact (Fin.ext h : k = 272) ▸ free |
        (rw [start k (by omega)]; simp [helperArchiveSeed,h,binSyms]))
  refine ⟨y,_,t,user,run,time,rfl,?_,?_⟩
  · intro k
    by_cases two : k.val = 2
    · have eq : k.castAdd 5 = (2 : Fin 273) := Fin.ext two
      simp [eq,Function.update_of_ne,r.injective.eq_iff,helperArchiveSeed,two,W]
    · by_cases thirteen : k.val = 13
      · have eq : k.castAdd 5 = (13 : Fin 273) := Fin.ext thirteen
        simp [eq,helperArchiveSeed,thirteen,W]
      · have ne (j : Fin 273) (h : k.val ≠ j.val) := r.injective.ne (fun e : k.castAdd 5 = j => h (congrArg Fin.val e))
        simp only [Function.update_of_ne (ne 13 thirteen),Function.update_of_ne (ne 2 two),
          Function.update_of_ne (ne 272 (by have := k.isLt; change k.val ≠ 272; omega)),archive]
        simp [helperArchiveSeed,two,thirteen]
  · intro p a b c
    simp only [Function.update_of_ne a,Function.update_of_ne b,Function.update_of_ne c]

/-- The row descriptor supplies the label size and all four spectator factors.
The radix, unit and atom width come from the caller's arithmetic registers. -/
def helperParentSources (hdr : Fin 6 → Fin T) (regs : Fin 35 ↪ Fin T) : Fin 7 → Fin T :=
  ![regs 2,regs 28,hdr 2,hdr 0,hdr 1,hdr 4,hdr 5]

def helperParentTargets : Fin 7 ↪ Fin 273 := ⟨![0,1,12,268,269,270,271],by decide⟩

def helperClockPorts (clock : Fin T) : Fin 8 ↪ Fin (T+273) where
  toFun := Fin.cases (clock.castAdd 273) (fun i : Fin 7 => ((![3,5,6,7,8,9,10] i : Fin 273).natAdd T))
  inj' := by
    intro i j eq
    induction i using Fin.cases <;> induction j using Fin.cases
    · rfl
    · have h := congrArg Fin.val eq
      simp [Fin.val_natAdd] at h
      omega
    · have h := congrArg Fin.val eq
      simp [Fin.val_natAdd] at h
      omega
    · rename_i i j
      have inj : Function.Injective (![3,5,6,7,8,9,10] : Fin 7 → Fin 273) := by decide
      exact congrArg Fin.succ (inj ((Fin.natAddEmb T).injective eq))

noncomputable def prepareHelperSeeds (hdr : Fin 6 → Fin T) (regs : Fin 35 ↪ Fin T) :
    Pr P (T+273) Q prime U :=
  let r := Fin.natAddEmb T (m := 273)
  let src := fun i => ((helperParentSources hdr regs) i).castAdd 273
  .seq (Record.copyLeafHeaders src (helperParentTargets.trans r) (r 5) (r 6) (List.finRange 7))
    (.seq (swapExponent (helperClockPorts (regs 33))) (helperParentProducts r))

theorem prepareHelperSeeds_exec (body : P → Pr P (T+273) Q prime U) (hdr : Fin 6 → Fin T)
    (regs : Fin 35 ↪ Fin T) (v : RecursiveInterchangeLayout.Descriptor) (w : ℕ)
    (pos : v.Positive) (u : HS (T+273) Q prime U) (S : Stacks (T+273) prime) :
    let W := v.beforeRows*v.rows*v.between*v.afterD
    let read := fun (k : Fin T) => S.R (k.castAdd 273)
    read (regs 2) = binSyms (prime^(w+1)).size (prime^(w+1)) → read (regs 28) = binSyms 1 1 →
    (read (regs 33)).length = w →
    (∀ i, read (hdr i) = (M8.RevMachine.Routines.hdr v i).map bitSymbol) →
    (∀ j : Fin 273, S.L (j.natAdd T) = [] ∧ S.R (j.natAdd T) = []) →
    ∃ z F t, z.user = u.user ∧ Exec body (prepareHelperSeeds hdr regs) (mk u S) t (mk z F) ∧
      t ≤ (((List.finRange 7).map fun i => 6*(read (helperParentSources hdr regs i)).length+6).sum+1) +
        ((21*(w+1)+12) + (432*(v.beforeRows*v.rows*v.between)+432*W+432*(v.beforeH*W))) ∧
      (∀ k : Fin 268, F.R ((k.castAdd 5).natAdd T) = helperArchiveSeed (w+1) v.beforeH W k) ∧
      F.L = S.L ∧ ∀ k : Fin T, F.R (k.castAdd 273) = read k := by
  intro W read base one clock words free
  let src := helperParentSources hdr regs
  let r := Fin.natAddEmb T (m := 273)
  obtain ⟨y,D,user,copy,left,keep,loaded,off⟩ := Record.loadPrivateHeaders_exec
    (Function.Embedding.refl (Fin T)) (Function.Embedding.refl (Fin 273)) src helperParentTargets 5 6
    (by decide) body u S free
  have get (i : Fin 7) : D.R (r (helperParentTargets i)) = read (src i) := loaded i
  have blankAt (k : Fin 273) (unused : ∀ i, helperParentTargets i ≠ k) : D.R (r k) = [] := off k unused
  let ports := helperClockPorts (regs 33)
  obtain ⟨y',k,same,price,convertClock⟩ := swapExponent_exec body ports w y D
    (by change (D.R ((regs 33).castAdd 273)).length = w; rw [keep]; exact clock)
    (by intro i ne; induction i using Fin.cases with
        | zero => exact (ne rfl).elim
        | succ i =>
          exact blankAt _ (show ∀ j, helperParentTargets j ≠ (![3,5,6,7,8,9,10] i : Fin 273) from
            (by decide : ∀ i : Fin 7, ∀ j, helperParentTargets j ≠ (![3,5,6,7,8,9,10] i : Fin 273)) i))
  let E := {D with R := Function.update D.R (r 3) ((FlatCoordinateSchedule.bits (w+1)).map bitSymbol)}
  have saved (j : Fin 273) (ne : j ≠ 3) : E.R (r j) = D.R (r j) := Function.update_of_ne (r.injective.ne ne) _ _
  have canon (i : Fin 6) := (words i).trans (canonicalBits_symbols _)
  have archive (j : Fin 268) : E.R (r (j.castAdd 5)) = helperArchiveSeed (w+1) v.beforeH 0 j := by
    by_cases h3 : j.val = 3
    · exact (Fin.ext h3 : j = 3) ▸ Function.update_self ..
    rw [saved _ (fun h => h3 (congrArg Fin.val h))]
    by_cases h0 : j.val = 0
    · exact (Fin.ext h0 : j = 0) ▸ (get 0).trans base
    by_cases h1 : j.val = 1
    · exact (Fin.ext h1 : j = 1) ▸ (get 1).trans one
    by_cases h12 : j.val = 12
    · exact (Fin.ext h12 : j = 12) ▸ (get 2).trans (canon 2)
    rw [blankAt _ (by intro i eq; have h := congrArg Fin.val eq; fin_cases i <;>
                              simp [helperParentTargets] at h <;> omega)]
    simp [helperArchiveSeed,h0,h1,h3,h12,binSyms]
  obtain ⟨z,F,m,last,prod,cost,left',filled,rest⟩ := helperParentSeed_exec body r v v.rows (w+1) pos pos.2.1 y' E
    archive ((saved 268 (by decide)).trans ((get 3).trans (canon 0)))
    ((saved 269 (by decide)).trans ((get 4).trans (canon 1)))
    ((saved 270 (by decide)).trans ((get 5).trans (canon 4)))
    ((saved 271 (by decide)).trans ((get 6).trans (canon 5)))
    ((saved 272 (by decide)).trans (blankAt 272 (by decide)))
  refine ⟨z,F,_,last.trans (same.trans user),Exec.seq copy (Exec.seq convertClock prod),
    Nat.add_le_add_left (Nat.add_le_add price cost) _,filled,left'.trans left,?_⟩
  intro j
  have ne (i : Fin 273) : j.castAdd 273 ≠ r i := by
    intro e; have h := congrArg Fin.val e; change j.val = T+i.val at h; omega
  exact (rest _ (ne 2) (ne 13) (ne 272)).trans ((Function.update_of_ne (ne 3) _ _).trans (keep j))

/-- Even when the spectator has many bits, preparing the archive costs only
a fixed multiple of the volume of the helper word. -/
theorem helperArchiveTime_le (w L W : ℕ) (labels : 0 < L) (live : 0 < W) :
    let V := (prime^w)^128*(L*W)
    ((List.finRange 127).map (helperHeaderTime w L W)).sum+1 ≤ (127*1200000+1)*V := by
  intro V
  let M := prime^w
  have pos : 0 < M := pow_pos Shared50ModularControl.prime_prime.pos _
  have p : M ≤ M^128 := by simpa only [pow_one] using (Nat.pow_le_pow_right pos (by decide : 1 ≤ 128))
  have sq : M*M ≤ M^128 := by simpa only [pow_two] using (Nat.pow_le_pow_right pos (by decide : 2 ≤ 128))
  have base : M.size ≤ M := Nat.size_le.mpr Nat.lt_two_pow_self
  have lw := Nat.mul_pos labels live
  have scale : M^128 ≤ V := Nat.le_mul_of_pos_right _ lw
  have h : M.size ≤ V := base.trans (p.trans scale)
  have square : M.size*M.size ≤ V := (Nat.mul_le_mul base base).trans (sq.trans scale)
  have vpos : 1 ≤ V := Nat.mul_pos (pow_pos pos _) lw
  have part (d x : ℕ) (degree : d ≤ 128) (seed : x ≤ L*W) :
      dimensionTime M.size x.size d + (4*(d*M.size+x.size)+6) ≤ 600000*V := by
    have width : x.size ≤ L*W := (Nat.size_le.mpr Nat.lt_two_pow_self).trans seed
    have tail : x.size ≤ V := width.trans (Nat.le_mul_of_pos_left _ (pow_pos pos 128))
    have cross : M.size*x.size ≤ V := Nat.mul_le_mul (base.trans p) width
    calc
      _ ≤ 6*x.size+6+128*((12*M.size+18)*(128*M.size+x.size)+20*M.size+26)+
          (4*(128*M.size+x.size)+6) := by
            grw [dimensionTime_le,degree]
      _ ≤ _ := by nlinarith only [tail,h,square,cross,vpos]
  have each (i : Fin 127) : helperHeaderTime w L W i ≤ 1200000*V := by
    have a : (if 16 ≤ i.val then L else 1) ≤ L*W := by split <;> first | exact Nat.le_mul_of_pos_right _ live | exact lw
    have b : (if i.val < 15 then L else 1)*W ≤ L*W := by split <;> simp [Nat.le_mul_of_pos_left W labels]
    exact (Nat.add_le_add (part i.val _ (by omega) a) (part (126-i.val) _ (by omega) b)).trans_eq (by ring)
  have total := List.sum_le_length_nsmul ((List.finRange 127).map (helperHeaderTime w L W)) (1200000*V)
    (fun _ hx => by obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx; exact each i)
  simp only [List.length_map,List.length_finRange,nsmul_eq_mul] at total
  omega

def parentArchive (T : ℕ) : Fin 268 ↪ Fin (T+273) := (Fin.castAddEmb 5).trans (Fin.natAddEmb T)

def parentHelperHeaders (T : ℕ) (i : Fin 127) : Fin 6 → Fin (T+273) :=
  let bank := parentArchive T
  helperHeaderPorts i (bank 1) (bank 3) (bank 12) (bank (helperArchiveBank i 3)) (bank (helperArchiveBank i 4))

noncomputable def prepareHelperHeaders (hdr : Fin 6 → Fin T) (regs : Fin 35 ↪ Fin T) : Pr P (T+273) Q prime U :=
  .seq (prepareHelperSeeds hdr regs)
    (helperHeaderSweep (fun i => (helperArchiveBank i).trans (parentArchive T)) (List.finRange 127))

/-- The seven caller words and the row clock generate all headers at linear cost
in the owner volume, preserving the input on every original caller tape. -/
theorem prepareHelperHeaders_exec (body : P → Pr P (T+273) Q prime U) (hdr : Fin 6 → Fin T)
    (regs : Fin 35 ↪ Fin T) (v : RecursiveInterchangeLayout.Descriptor) (w : ℕ)
    (pos : v.Positive) (u : HS (T+273) Q prime U) (S : Stacks (T+273) prime) :
    let W := v.beforeRows*v.rows*v.between*v.afterD
    let M := prime^(w+1)
    let V := M^128*(v.beforeH*W)
    let read := fun (k : Fin T) => S.R (k.castAdd 273)
    read (regs 2) = binSyms M.size M → read (regs 28) = binSyms 1 1 →
    (read (regs 33)).length = w →
    (∀ i, read (hdr i) = (M8.RevMachine.Routines.hdr v i).map bitSymbol) →
    (∀ j : Fin 273, S.L (j.natAdd T) = [] ∧ S.R (j.natAdd T) = []) →
    ∃ z F t, z.user = u.user ∧ Exec body (prepareHelperHeaders hdr regs) (mk u S) t (mk z F) ∧
      t ≤ 152402000*V ∧
      (∀ i j, F.R (parentHelperHeaders T i j) =
        (M8.RevMachine.Routines.hdr (helperAdjacentView (w+1) v.beforeH W i) j).map bitSymbol) ∧
      F.L = S.L ∧ ∀ k : Fin T, F.R (k.castAdd 273) = read k := by
  intro W M V read base unit clock words free
  obtain ⟨y,D,m,same,seed,charge,filled,dl,dr⟩ := prepareHelperSeeds_exec body hdr regs v w pos u S base unit clock words free
  obtain ⟨z,F,n,user,sweep,price,fl,ready,off⟩ := helperArchive_exec body (parentArchive T) (w+1) v.beforeH W y D filled
  have wp : 0 < W := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos pos.1 pos.2.1) pos.2.2.2.1) pos.2.2.2.2
  have mp : 0 < M := pow_pos Shared50ModularControl.prime_prime.pos _
  have lp := Nat.mul_pos pos.2.2.1 wp
  have vol : 1 ≤ V := Nat.mul_pos (pow_pos mp _) lp
  have lw : v.beforeH*W ≤ V := Nat.le_mul_of_pos_left _ (pow_pos mp _)
  have ww : W ≤ V := (Nat.le_mul_of_pos_left W pos.2.2.1).trans lw
  have mm : M ≤ V := (by simpa only [pow_one] using
    (Nat.pow_le_pow_right mp (by decide : 1 ≤ 128)) : M ≤ M^128).trans (Nat.le_mul_of_pos_right _ lp)
  have atom : w+1 ≤ V := (Nat.le_of_lt (Nat.lt_pow_self Shared50ModularControl.prime_prime.one_lt)).trans mm
  have prefixBound := (Nat.le_mul_of_pos_right (v.beforeRows*v.rows*v.between) pos.2.2.2.2).trans ww
  have factors : ∀ j : Fin 7, (read (helperParentSources hdr regs j)).length ≤ V := by
    have sizeBound (x : ℕ) (hx : x ≤ V) : x.size ≤ V := (Nat.size_le.mpr Nat.lt_two_pow_self).trans hx
    have row := (Nat.le_mul_of_pos_right (v.beforeRows*v.rows) pos.2.2.2.1).trans prefixBound
    have vals (i : Fin 6) := (words i).trans (canonicalBits_symbols _)
    intro j
    fin_cases j
    · change (read (regs 2)).length ≤ V; rw [base,length_binSyms]; exact sizeBound M mm
    · change (read (regs 28)).length ≤ V; rw [unit,length_binSyms]; exact vol
    all_goals change (read (hdr _)).length ≤ V
    all_goals rw [vals,length_binSyms]; apply sizeBound
    · exact (Nat.le_mul_of_pos_right _ wp).trans lw
    · exact (Nat.le_mul_of_pos_right _ pos.2.1).trans row
    · exact (Nat.le_mul_of_pos_left _ pos.1).trans row
    · exact (Nat.le_mul_of_pos_left _ (Nat.mul_pos pos.1 pos.2.1)).trans prefixBound
    · exact (Nat.le_mul_of_pos_left _ (Nat.mul_pos (Nat.mul_pos pos.1 pos.2.1) pos.2.2.2.1)).trans ww
  let lengths := (List.finRange 7).map fun i => 6*(read (helperParentSources hdr regs i)).length+6
  have total := List.sum_le_length_nsmul lengths (6*V+6) (fun a ha => by
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp ha
    exact Nat.add_le_add_right (Nat.mul_le_mul_left 6 (factors j)) 6)
  have count : lengths.length = 7 := by simp [lengths]
  rw [count,nsmul_eq_mul] at total
  change m ≤ (lengths.sum+1)+((21*(w+1)+12)+(432*(v.beforeRows*v.rows*v.between)+432*W+432*(v.beforeH*W))) at charge
  have bounded := price.trans (helperArchiveTime_le (w+1) v.beforeH W pos.2.2.1 wp)
  refine ⟨z,F,m+n,user.trans same,Exec.seq seed sweep,?_,ready,fl.trans dl,?_⟩
  · change n ≤ (127*1200000+1)*V at bounded
    omega
  · intro k
    apply (off _ ?_).trans (dr k)
    intro j e
    have h := congrArg Fin.val e
    change T+j.val = k.val at h
    omega

end IntegerMultBounds.MathlibTM2.M6.BitNode
