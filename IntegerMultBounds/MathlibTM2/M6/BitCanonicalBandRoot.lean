module

public import IntegerMultBounds.MathlibTM2.M6.BitCompactMoveEntry

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open RecursiveInterchangeLayout
open Shared50ModularControl (prime)

/-- Six contractions by the maximum PR589 rank suffice in the seven-atom band. -/
def bandHeight (width cutoff : ℕ) : ℕ :=
  6-Nat.findGreatest (fun k => width*42^(6-k) ≤ cutoff*64^(6-k)) 6

theorem bandHeight_spec (w cutoff : ℕ) (band : 7*(w+1) ≤ cutoff) :
    let width := 64*(w+1)
    let h := bandHeight width cutoff
    width*42^h ≤ cutoff*64^h ∧ ∀ n, width*42^n ≤ cutoff*64^n → h ≤ n := by
  intro width h
  have six : width*42^6 ≤ cutoff*64^6 := by dsimp [width]; omega
  have start : width*42^(6-0) ≤ cutoff*64^(6-0) := six
  refine ⟨Nat.findGreatest_spec (P := fun k => width*42^(6-k) ≤ cutoff*64^(6-k)) (by decide : 0 ≤ 6) start,?_⟩
  intro n stop
  by_cases within : n ≤ 6
  · have eq : 6-(6-n) = n := by omega
    have best := Nat.le_findGreatest (P := fun k => width*42^(6-k) ≤ cutoff*64^(6-k))
      (Nat.sub_le 6 n) (by simpa only [eq] using stop)
    dsimp only [h,bandHeight]
    omega
  · exact (Nat.sub_le 6 _).trans (by omega)

/-- Put the row and label factors required by the recursive machine in their
own fields and all remaining spectator coordinates in the trailing field. -/
noncomputable def bandRoot (width cutoff spectators : ℕ) : Descriptor :=
  let rows := 142080^(bandHeight width cutoff+1)
  let labels := prime^(64*width)
  ⟨1,rows,labels,width,1,spectators/(rows*labels)⟩

private theorem rowsAfterPath (v : Descriptor) (path : List (Fin nodeChildren5.length)) :
    (path.foldl (scheduledChild prime) v).rows = v.rows/142080^path.length := by
  induction path generalizing v with
  | nil => simp
  | cons i path ih =>
    rw [List.foldl_cons,ih]
    change v.rows/142080/142080^path.length = _
    rw [Nat.div_div_eq_div_mul,List.length_cons,pow_succ']

/-- The remaining aligned depth of the actual node suffices for the least
stopping height computed from the flat header. -/
private theorem nodeAlignment (c : CutoffNodeInput) (active : c.cutoff < c.node.width)
    (rows : 142080^(c.depth+1) ∣ c.root.rows) :
    let n := c.depth-c.path.length
    64^n ∣ c.node.width ∧ 142080^(n+1) ∣ c.node.rows ∧ c.node.width*42^n ≤ c.cutoff*64^n := by
  intro n
  have stop : c.root.width*42^c.depth ≤ c.cutoff*64^c.depth := by
    rw [c.rootWidth]; simpa only [Nat.mul_comm,Nat.mul_assoc,Nat.mul_left_comm] using Nat.mul_le_mul_left (64^c.depth) c.stop
  have short := scheduledPath_length_lt prime c.root c.depth c.cutoff stop c.path active
  have len : n+c.path.length = c.depth := by dsimp [n]; omega
  have width := (scheduledPath_alignment prime c.root c.path n (len ▸ ⟨c.b,c.rootWidth⟩)
    (len ▸ (pow_dvd_pow 142080 (Nat.le_succ _)).trans rows)).1
  obtain ⟨a,stock⟩ := rows
  have row : 142080^(n+1) ∣ c.node.rows := by
    change _ ∣ (c.path.foldl _ c.root).rows
    rw [rowsAfterPath,stock,show c.depth+1 = c.path.length+(n+1) by omega,pow_add 142080 c.path.length (n+1),Nat.mul_assoc,
      Nat.mul_div_cancel_left _ (by positivity)]
    exact dvd_mul_right _ _
  refine ⟨width,row,?_⟩
  have path := scheduledPath_width_le prime c.root c.path
  apply Nat.le_of_mul_le_mul_right _ (show 0 < 64^c.path.length by positivity)
  calc
    _ = (c.node.width*64^c.path.length)*42^n := by ring
    _ ≤ (c.root.width*42^c.path.length)*42^n := Nat.mul_le_mul_right _ path
    _ = c.root.width*42^c.depth := by rw [← len,pow_add]; ring
    _ ≤ c.cutoff*64^c.depth := stop
    _ = _ := by rw [← len,pow_add]; ring

/-- Above the cutoff the recurrence uses only width and volume. Once the
maximum-rank branch stops, additional fuel leaves the bill unchanged. -/
theorem cutoffTreeBudget_relayout [M8.Machine.Net] (D R : ℝ) (cut h extra : ℕ) (v z : Descriptor)
    (width : v.width = z.width) (mass : volume prime v = volume prime z)
    (aligned : 64^h ∣ v.width) (rows : 142080^h ∣ v.rows) (rows' : 142080^h ∣ z.rows)
    (stop : v.width*42^h ≤ cut*64^h) :
    cutoffTreeBudget D R cut h v = cutoffTreeBudget D R cut (h+extra) z := by
  induction h generalizing v z with
  | zero =>
    have leaf : z.width ≤ cut := by simpa only [pow_zero,Nat.mul_one,width] using stop
    cases extra <;> simp [cutoffTreeBudget,width,mass,Nat.not_lt_of_ge leaf]
  | succ h ih =>
    rw [Nat.succ_add]
    simp only [cutoffTreeBudget,width,mass]
    split
    · congr 1
      apply Finset.sum_congr rfl
      intro i _
      have wa : 64 ∣ v.width := (dvd_pow_self 64 (Nat.succ_ne_zero h)).trans aligned
      have ra : 142080 ∣ v.rows := (dvd_pow_self 142080 (Nat.succ_ne_zero h)).trans rows
      have rb : 142080 ∣ z.rows := (dvd_pow_self 142080 (Nat.succ_ne_zero h)).trans rows'
      have left := scheduledChild_measures prime v wa ra i
      have right := scheduledChild_measures prime z (width ▸ wa) rb i
      have childWidth : (scheduledChild prime v i).width = (scheduledChild prime z i).width := by
        change nodeChildren5[i.val]*(v.width/64) = nodeChildren5[i.val]*(z.width/64)
        rw [width]
      have childMass := Nat.eq_of_mul_eq_mul_right (by decide : 0 < 142080) (left.2.trans (mass.trans right.2.symm))
      obtain ⟨w,r⟩ := scheduledChild_alignment prime v h aligned rows i
      apply ih _ _ childWidth childMass w r (scheduledChild_alignment prime z h (width ▸ aligned) rows' i).2
      apply Nat.le_of_mul_le_mul_right _ (by decide : 0 < 64)
      calc
        _ = ((scheduledChild prime v i).width*64)*42^h := by ring
        _ ≤ (42*v.width)*42^h := Nat.mul_le_mul_right _ (left.1.trans_le (Nat.mul_le_mul_right _ (nodeChildren5_le i)))
        _ = v.width*42^(h+1) := by rw [pow_succ]; ring
        _ ≤ _ := stop
        _ = _ := by rw [pow_succ]; ring
    · rfl

/-- The twelve compact MOVE inputs expressed in terms of the flat record. -/
noncomputable def bandSeedWords (width cutoff spectators : ℕ) : Fin 12 → List (Fin (prime+4)) :=
  let atom := width/64
  let idle := spectators/142080^2
  let archive := fun j => Fin.addCases (motive := fun _ => List (Fin (prime+4)))
    (fun i : Fin 6 => (Routines.hdr (bandRoot width cutoff spectators) i).map bitSymbol)
    (![binSyms (prime^atom).size (prime^atom), binSyms 1 1, List.replicate (atom-1) blank] : Fin 3 → _) j
  fun j => Fin.addCases (motive := fun _ => List (Fin (prime+4)))
    (Fin.cons (binSyms width.size cutoff) archive)
    (![binSyms idle.size idle, List.replicate atom blank] : Fin 2 → _) j

/-- The canonical descriptor is reconstructed from three scalar values. It has
the exact row stock for its stopping height and the original spectator count. -/
theorem canonicalBandInput (a : ActiveBandRecord) :
    let c := a.input
    let w := c.node.width
    let n := CopyChildLayout.spectators c.node
    let h := bandHeight w c.cutoff
    let v := bandRoot w c.cutoff n
    ∃ b : ActiveBandRecord, b.input.root = v ∧ b.input.path = [] ∧ b.input.depth = h ∧
      b.input.cutoff = c.cutoff ∧ b.input.w = c.w ∧ b.input.cells = c.cells ∧
      CopyChildLayout.spectators v = n ∧ nodeSeedWords b.input = bandSeedWords w c.cutoff n ∧
      ∀ D R, let _ := BinaryRadixEqualShared.supplierNet
        cutoffTreeBudget D R c.cutoff h v =
          cutoffTreeBudget D R c.cutoff (c.depth-c.path.length) c.node := by
  intro c w n h v
  obtain ⟨widthAlign,rowAlign,stop⟩ := nodeAlignment c a.active a.rows
  have spec := bandHeight_spec c.w c.cutoff a.band
  rw [← c.width] at spec
  have fits := spec.2 _ stop
  change h ≤ c.depth-c.path.length at fits
  have hpos : 0 < h := by
    by_contra! e
    have hz : bandHeight w c.cutoff = 0 := Nat.eq_zero_of_le_zero e
    have bound := spec.1
    change w*42^h ≤ c.cutoff*64^h at bound
    rw [show h = 0 from hz] at bound
    have live := a.active
    change c.cutoff < w at live
    omega
  obtain ⟨b,width⟩ := (pow_dvd_pow 64 fits).trans widthAlign
  obtain ⟨g,groups⟩ := (pow_dvd_pow 142080 (Nat.add_le_add_right fits 1)).trans rowAlign
  let box := prime^(64*w)
  let rows := 142080^(h+1)
  have label : c.node.beforeH = c.B*box := by
    dsimp only [box,w]; rw [c.width,Nat.mul_comm 64 (c.w+1)]; exact c.label
  let tail := c.node.beforeRows*g*c.B*c.node.between*c.node.afterD
  have factors : n = (rows*box)*tail := by
    dsimp only [n,CopyChildLayout.spectators,tail,rows]
    rw [groups,label]
    ring
  have quotient : n/(rows*box) = tail := by
    rw [factors,Nat.mul_div_cancel_left _ (by dsimp [rows,box]; have := Shared50ModularControl.prime_prime.pos; positivity)]
  have spos : 0 < n := by
    have hrows := Nat.mul_pos (by decide : 0 < 142080) (Nat.mul_pos (by decide : 0 < 142080) c.positive.2.1)
    rw [← c.rows] at hrows
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos c.positive.1 hrows) c.positive.2.2.1)
      c.positive.2.2.2.1) c.positive.2.2.2.2
  have tpos : 0 < tail := Nat.pos_of_mul_pos_left (factors ▸ spos)
  have vpos : v.Positive := by
    change 0 < 1 ∧ 0 < rows ∧ 0 < box ∧ 0 < 1 ∧ 0 < n/(rows*box)
    rw [quotient]
    exact ⟨by decide,by dsimp [rows]; positivity,pow_pos Shared50ModularControl.prime_prime.pos _,by decide,tpos⟩
  have count : CopyChildLayout.spectators v = n := by
    change 1*rows*box*1*(n/(rows*box)) = n
    rw [quotient,one_mul,mul_one,factors]
  have mass : volume prime v = volume prime c.node := by
    have eq (x : Descriptor) : volume prime x = prime^x.width*prime^x.width*CopyChildLayout.spectators x := by
      dsimp only [volume,CopyChildLayout.spectators]; ring
    rw [eq,eq c.node,count]; rfl
  have endAt : 42^h*b ≤ c.cutoff := by
    apply Nat.le_of_mul_le_mul_right _ (show 0 < 64^h by positivity)
    calc
      _ = w*42^h := by change c.node.width = 64^h*b at width; dsimp only [w]; rw [width]; ring
      _ ≤ _ := spec.1
  have base : 0 < b := by
    have wp : 0 < c.node.width := c.width ▸ Nat.mul_pos (by decide) (Nat.succ_pos _)
    exact Nat.pos_of_mul_pos_left (width ▸ wp)
  obtain ⟨z,root,path,depth,_,cut⟩ := activeCutoffNodeInput v h b c.cutoff 1 vpos hpos base width
    (dvd_refl rows) (one_mul box).symm endAt [] a.active
  have zn : z.node = v := by simp [CutoffNodeInput.node,root,path]
  have atom : z.w = c.w := by
    have zw := z.width
    change z.node.width = 64*(z.w+1) at zw
    rw [zn] at zw
    change c.node.width = 64*(z.w+1) at zw
    rw [c.width] at zw
    omega
  have size : z.cells = c.cells := Nat.eq_of_mul_eq_mul_right (by decide : 0 < 142080)
    (z.cells_share.trans ((congrArg (volume prime) zn).trans (mass.trans c.cells_share.symm)))
  refine ⟨⟨z,1,root ▸ vpos,by rw [depth,root]; exact dvd_refl rows,
    by rw [root]; exact (one_mul box).symm,by rw [cut,zn]; exact a.active,by rw [atom,cut]; exact a.band⟩,
    root,path,depth,cut,atom,size,count,?_,?_⟩
  · have slots : n = z.idleWidth*142080^2 := by
      calc
        n = CopyChildLayout.spectators z.node := by rw [zn,count]
        _ = _ := by
          dsimp only [CopyChildLayout.spectators,CutoffNodeInput.idleWidth]
          rw [show z.node.rows = _ from z.rows]
          ring
    have atoms : w/64 = z.w+1 := by
      dsimp only [w]
      rw [c.width,atom,Nat.mul_div_cancel_left _ (by decide)]
    change nodeSeedWords z = bandSeedWords w c.cutoff n
    unfold nodeSeedWords sweepSeedWords bandSeedWords
    rw [parentArchiveSeed_words,zn,root,cut,atoms,
      show n/142080^2 = z.idleWidth by rw [slots,Nat.mul_div_cancel _ (by decide)]]
    rfl
  intro D R inst
  have rowV : 142080^h ∣ v.rows := pow_dvd_pow 142080 (Nat.le_succ h)
  have eq := cutoffTreeBudget_relayout D R c.cutoff h (c.depth-c.path.length-h) v c.node rfl mass
    ⟨b,width⟩ rowV ((pow_dvd_pow 142080 (fits.trans (Nat.le_succ _))).trans rowAlign) spec.1
  simpa only [show h+(c.depth-c.path.length-h) = c.depth-c.path.length by omega] using eq

/-- Execute the packed transpose from canonical headers with the original node's bill. -/
theorem canonicalBandMove {U : Type} :
    let _ := BinaryRadixEqualShared.supplierNet
    ∃ states : ℕ, ∀ {Q : ℕ}, states ≤ Q → ∃ minimum leafRate : ℝ, ∀ D, minimum ≤ D →
      ∃ B : ℕ, ∀ {H : ℕ} (place : Fin B ↪ Fin H) (ports : Fin 4 ↪ Fin H) (headers : Fin 12 → Fin H),
      (∀ i j, place i ≠ ports j) → (∀ i j, place i ≠ headers j) →
      ∃ (P : Type) (table : P → Pr P H Q prime U) (code : Pr P H Q prime U) (rate : ℕ),
      ∀ a : ActiveBandRecord, let p := a.input
      let wide := packedDescriptor p.node.width (CopyChildLayout.spectators p.node)
      ∀ (x : Fin (volume prime wide) → ZMod 2) u (S : Stacks H prime),
        RecordPayload (ports 0) (fun _ => blank) 0 x S →
        (∀ i : Fin 12, S.R (headers i) = bandSeedWords p.node.width p.cutoff (CopyChildLayout.spectators p.node) i) →
        S.R (ports 1) = [] → S.R (ports 2) = [] → S.L (ports 3) = [] → S.R (ports 3) = [] →
        ∃ z F n, Exec table code (mk u S) n (mk z F) ∧ z.user = u.user ∧
          CleanupBound S F n (cutoffTreeBudget D leafRate p.cutoff (p.depth-p.path.length) p.node+
            rate*p.cells+1000000034*volume prime wide+
            (prime+8)*((frameSlots place).map (fun j => (S.L j).length+(S.R j).length+2)).sum) ∧
          RecordPayload (ports 0) (fun _ => blank) 0
            (Shared50RecursiveNodeRows.transpose (v := wide) (one_dvd wide.rows) x) F ∧
          ∀ j, j ≠ ports 0 → F.L j = S.L j ∧ F.R j = S.R j := by
  intro inst
  classical
  choose child spec using canonicalBandInput
  obtain ⟨q,compile⟩ := compactBandMove (Config := ActiveBandRecord) (U := U)
  refine ⟨q,?_⟩
  intro Q enough
  obtain ⟨minimum,R,build⟩ := compile enough
  refine ⟨minimum,R,?_⟩
  intro D paid
  obtain ⟨B,placeChild⟩ := build D paid (fun a => (child a).input) (fun a => (child a).blocks)
    (fun a => (child a).band) (fun a => (child a).positive) (fun a => (child a).rows)
    (fun a => (child a).label) (fun a => (child a).active)
  refine ⟨B,?_⟩
  intro H place ports headers apart clear
  obtain ⟨P,table,code,rate,run⟩ := placeChild place ports headers apart clear
  refine ⟨P,table,code,rate,?_⟩
  intro a
  obtain ⟨root,path,depth,cut,_,cells,count,words,budget⟩ := spec a
  have node : (child a).input.node = bandRoot a.input.node.width a.input.cutoff (CopyChildLayout.spectators a.input.node) := by
    unfold CutoffNodeInput.node
    rw [root,path]; rfl
  have wide : packedDescriptor (child a).input.node.width (CopyChildLayout.spectators (child a).input.node) =
      packedDescriptor a.input.node.width (CopyChildLayout.spectators a.input.node) := by
    rw [node,count]; rfl
  have bill : cutoffTreeBudget D R (child a).input.cutoff ((child a).input.depth-(child a).input.path.length)
      (child a).input.node = _ := (by
    rw [cut,depth,path,List.length_nil,Nat.sub_zero,node]
    exact budget D R : _ = cutoffTreeBudget D R a.input.cutoff (a.input.depth-a.input.path.length) a.input.node)
  have execute := run a
  dsimp only at execute ⊢
  rw [wide] at execute
  simpa only [words,bill,cells] using execute

end IntegerMultBounds.MathlibTM2.M6.BitNode
