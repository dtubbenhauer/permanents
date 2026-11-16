import BlockPermanents.MarkedEdges

/-! # Appendix B's forced-edge evaluator on the five signed marked closures

The recursive table lists every partial assignment of distinct ket positions
to bra positions. Skipping a position leaves its packet in the mixed fine
closure. Forcing a pair multiplies by the single-packet Gram entry.
-/
namespace BlockPermanents.ForcedWitness
open Negative Polynomial
open scoped Polynomial
noncomputable section

/-- The chosen edges and untouched packets of a partial assignment. -/
structure Assignment (α β : Type) where
  edges : List (α × β)
  left : List α
  right : List β
  deriving Repr

/-- At each bra position either leave it untouched, or choose one still
unused ket position. Thus repetitions in the packet values keep their
labels throughout. -/
def assignments {α β : Type} : List α → List β → List (Assignment α β)
  | [],ys => [⟨[],[],ys⟩]
  | a::xs,ys =>
    ((assignments xs ys).map fun d => {d with left := a::d.left}) ++
    (picks ys).flatMap fun (b,ys') =>
      (assignments xs ys').map fun d => {d with edges := (a,b)::d.edges}

private theorem pick_partition {β : Type} (ys : List β) (t : β × List β) (ht : t ∈ picks ys) :
    (t.1 :: t.2).Perm ys := by
  induction ys generalizing t with
  | nil => simp [picks] at ht
  | cons a ys ih =>
    simp only [picks,List.mem_cons,List.mem_map] at ht
    obtain rfl | ⟨⟨b,bs⟩,hb,rfl⟩ := ht
    · rfl
    · exact (List.Perm.swap _ _ _).trans ((ih (b,bs) hb).cons a)

/-- On either boundary each packet label occurs exactly once, either in a
forced edge or among the untouched packets in the residual fine closure. -/
theorem partition {α β : Type} (xs : List α) (ys : List β) (t : Assignment α β)
    (ht : t ∈ assignments xs ys) :
    (t.edges.map Prod.fst ++ t.left).Perm xs ∧ (t.edges.map Prod.snd ++ t.right).Perm ys := by
  induction xs generalizing ys t with
  | nil => simp [assignments] at ht; subst t; simp
  | cons a xs ih =>
    simp only [assignments,List.mem_append,List.mem_map,List.mem_flatMap] at ht
    obtain ⟨v,hv,rfl⟩ | ⟨⟨b,bs⟩,hb,v,hv,rfl⟩ := ht
    · obtain ⟨hl,hr⟩ := ih ys v hv
      exact ⟨List.perm_middle.trans (hl.cons a),hr⟩
    · obtain ⟨hl,hr⟩ := ih bs v hv
      exact ⟨hl.cons a,(hr.cons b).trans (pick_partition ys (b,bs) hb)⟩

def forcedWeight {α β : Type} (x : α → Quad) (y : β → Quad) (d : Assignment α β) : ℚ :=
  (d.edges.map fun e => gram (x e.1) (y e.2)).prod *
    fine (d.left.map x) (d.right.map y)

/-- Coefficients of (z−1)^d, recursively with zero outside its support. -/
def signed : ℕ → ℕ → ℚ
  | 0,h => if h=0 then 1 else 0
  | d+1,0 => -signed d 0
  | d+1,h+1 => signed d h - signed d (h+1)

theorem signed_eq (d h : ℕ) : ((X-1 : ℚ[X])^d).coeff h = signed d h := by
  induction d generalizing h with
  | zero => simp [signed, Polynomial.coeff_one, eq_comm]
  | succ d ih =>
    cases h with
    | zero => simp [pow_succ,mul_sub,ih,signed]
    | succ h => simp [pow_succ,mul_sub,ih,signed]

def kernelPolynomial (d : ℕ) (v : ℚ) : ℚ[X] :=
  C 2*(X-1)^d - C v*(X*(X-1)^(d-1))

def kernelCoeff (d : ℕ) (v : ℚ) : ℕ → ℚ
  | 0 => 2*signed d 0
  | h+1 => 2*signed d (h+1) - v*signed (d-1) h

theorem kernel_coeff (d : ℕ) (v : ℚ) (h : ℕ) :
    (kernelPolynomial d v).coeff h = kernelCoeff d v h := by
  cases h <;> simp [kernelPolynomial, kernelCoeff, signed_eq]

def endCount {α β : Type} [DecidableEq α] [DecidableEq β] (i : α) (j : β)
    (d : Assignment α β) : ℚ :=
  (d.edges.map fun e => (if e.1=i then 1 else 0) + (if e.2=j then 1 else 0)).sum

/-- Form B_t by the product of forced Gram factors and the mixed closure
on the two untouched lists. Different marks may be used on bra and ket. -/
def polynomial {α β : Type} [DecidableEq α] [DecidableEq β] (x : α → Quad) (y : β → Quad)
    (i : α) (j : β) (xs : List α) (ys : List β) : ℚ[X] :=
  ((assignments xs ys).map fun d => C (forcedWeight x y d) *
    kernelPolynomial d.edges.length (endCount i j d)).sum

/-- Evaluate the signed coefficient readout on one forced assignment. -/
def multiplier (m d : ℕ) (v : ℚ) : ℚ :=
  ((List.range m).map fun h => (m : ℚ)/(2*(m-h : ℕ))*kernelCoeff d v h).sum

def evaluate {α β : Type} [DecidableEq α] [DecidableEq β] (m : ℕ) (x : α → Quad) (y : β → Quad)
    (i : α) (j : β) (xs : List α) (ys : List β) : ℚ :=
  ((assignments xs ys).map fun d => forcedWeight x y d * multiplier m d.edges.length (endCount i j d)).sum

/-- The executable readout is exactly coefficient extraction on the
forced-edge polynomial, including the degree-zero and omitted top terms. -/
theorem evaluate_eq {α β : Type} [DecidableEq α] [DecidableEq β] (m : ℕ)
    (x : α → Quad) (y : β → Quad) (i : α) (j : β) (xs : List α) (ys : List β) :
    evaluate m x y i j xs ys = ((List.range m).map fun h =>
      (m : ℚ)/(2*(m-h : ℕ)) * (polynomial x y i j xs ys).coeff h).sum := by
  unfold evaluate polynomial
  generalize assignments xs ys = ds
  induction ds with
  | nil => simp
  | cons d ds ih =>
    simp only [List.map_cons,List.sum_cons,Polynomial.coeff_add,mul_add,List.sum_map_add] at *
    rw [ih]
    congr 1
    unfold multiplier
    rw [← List.sum_map_mul_left]
    simp only [List.map_map, Function.comp_def, Polynomial.coeff_C_mul,kernel_coeff,mul_left_comm]

/-- Evaluate the same matching polynomial without materializing its full
list of assignments. Accumulated unmatched bra positions stay in order. -/
def run {α β : Type} [DecidableEq α] [DecidableEq β] (m : ℕ) (x : α → Quad) (y : β → Quad)
    (i : α) (j : β) : List α → List β → List α → ℕ → ℚ → ℚ
  | [],ys,pre,d,v => fine (pre.map x) (ys.map y) * multiplier m d v
  | a::xs,ys,pre,d,v =>
      run m x y i j xs ys (pre++[a]) d v +
      ((picks ys).map fun t => gram (x a) (y t.1) *
        run m x y i j xs t.2 pre (d+1) (v+((if a=i then 1 else 0)+(if t.1=j then 1 else 0)))).sum

private theorem sum_flat {α : Type} (s : List α) (f : α → List ℚ) :
    (s.flatMap f).sum = (s.map (fun a => (f a).sum)).sum := by
  induction s with
  | nil => rfl
  | cons a s ih => simp [List.sum_append, ih]

private theorem run_eq {α β : Type} [DecidableEq α] [DecidableEq β] (m : ℕ) (x : α → Quad) (y : β → Quad)
    (i : α) (j : β) (xs : List α) (ys : List β) (pre : List α) (d : ℕ) (v : ℚ) :
    run m x y i j xs ys pre d v =
      ((assignments xs ys).map fun t => ((t.edges.map fun e => gram (x e.1) (y e.2)).prod *
        fine ((pre++t.left).map x) (t.right.map y)) *
        multiplier m (d+t.edges.length) (v+endCount i j t)).sum := by
  induction xs generalizing ys pre d v with
  | nil => simp [run,assignments,endCount]
  | cons a xs ih =>
    simp only [run, assignments, List.map_append, List.sum_append, List.map_map, Function.comp_def,
      List.map_flatMap, sum_flat]
    congr 1
    · simpa only [List.append_assoc, List.singleton_append, List.map_append, endCount] using ih ys (pre++[a]) d v
    · apply congrArg List.sum
      apply List.map_congr_left
      rintro ⟨b,bs⟩ _
      rw [ih, ← List.sum_map_mul_left]
      simp only [List.map_map, Function.comp_def, List.map_cons, List.prod_cons, List.sum_cons,
        endCount,List.length_cons,List.map_append, Nat.add_assoc, Nat.add_comm 1, add_assoc, mul_assoc]

private theorem split_prefix {α β : Type} [DecidableEq α] [DecidableEq β] (m : ℕ) (x : α → Quad) (y : β → Quad)
    (i : α) (j : β) (tail xs : List α) (ys : List β) (pre : List α) (d : ℕ) (v : ℚ) :
    run m x y i j (xs++tail) ys pre d v =
      ((assignments xs ys).map fun t => (t.edges.map fun e => gram (x e.1) (y e.2)).prod *
        run m x y i j tail t.right (pre++t.left) (d+t.edges.length) (v+endCount i j t)).sum := by
  induction xs generalizing ys pre d v with
  | nil => simp [run,assignments,endCount]
  | cons a xs ih =>
    simp only [List.cons_append,run, assignments, List.map_append, List.sum_append, List.map_map, Function.comp_def,
      List.map_flatMap, sum_flat]
    congr 1
    · simpa only [List.append_assoc, List.singleton_append, List.map_append, endCount] using ih ys (pre++[a]) d v
    · apply congrArg List.sum
      apply List.map_congr_left
      rintro ⟨b,bs⟩ _
      rw [ih, ← List.sum_map_mul_left]
      simp only [List.map_map, Function.comp_def, List.map_cons, List.prod_cons, List.sum_cons,
        endCount,List.length_cons,List.map_append, Nat.add_assoc, Nat.add_comm 1, add_assoc, mul_assoc]

theorem run_correct {α β : Type} [DecidableEq α] [DecidableEq β] (m : ℕ) (x : α → Quad) (y : β → Quad)
    (i : α) (j : β) (xs : List α) (ys : List β) :
    run m x y i j xs ys [] 0 0 = evaluate m x y i j xs ys := by
  simp only [run_eq,evaluate, forcedWeight, List.nil_append,Nat.zero_add,zero_add]

def labels : List (Fin 5) := [0,1,2,3,4]

def witnessRead (t : Fin 5) : ℚ :=
  run 5 MarkedWitness.five MarkedWitness.five t t labels labels [] 0 0

private def blocks : List (Assignment (Fin 5) (Fin 5)) := assignments [0,1] labels

private def blockValue (t : Fin 5) (s : Assignment (Fin 5) (Fin 5)) : ℚ :=
  (s.edges.map fun e => gram (MarkedWitness.five e.1) (MarkedWitness.five e.2)).prod *
    run 5 MarkedWitness.five MarkedWitness.five t t [2,3,4] s.right s.left s.edges.length (endCount t t s)

private theorem sum_blocks (t : Fin 5) : witnessRead t = (blocks.map (blockValue t)).sum := by
  simpa only [Nat.zero_add, List.nil_append, zero_add] using
    split_prefix 5 MarkedWitness.five MarkedWitness.five t t [2,3,4] [0,1] labels [] 0 0

/- The first two bra labels have 31 partial assignments. Checking each
remaining three-row problem separately keeps kernel reduction bounded. -/
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
set_option Elab.async false

private theorem value_one : witnessRead 0 = 9041984725911/2000 := by
  have h : blocks.map (blockValue 0) = [
      153731605686087/32000, (-1626918062583/32000), 7204107596599/96000, 7204107596599/96000, 74415071,
      64316479/96000, (-3020773003857/16000), (-58340594161/6000), (-58340594161/6000), (-9598898),
      (-2349529/24000), (-3019888119397/48000), (-58340594161/6000), (-233433656969/64000), (-7203681/2),
      (-2592129/64000), (-3019888119397/48000), (-58340594161/6000), (-233433656969/64000), (-7203681/2),
      (-2592129/64000), (-62358994), (-9598898), (-7203681/2), (-7203681/2),
      (-12), (-18804757/48000), (-2349529/24000), (-2592129/64000), (-2592129/64000),
      (-12)] := by
    simp only [blocks, labels, assignments, picks, List.map_cons, List.map_nil, List.flatMap_cons,
      List.flatMap_nil, List.cons_append, List.nil_append]
    repeat' apply congrArg₂ List.cons
    all_goals decide +kernel
  rw [sum_blocks,h]
  norm_num

private theorem value_two : witnessRead 1 = 9041984725911/2000 := by
  have h : blocks.map (blockValue 1) = [
      153731605686087/32000, (-3019888119397/48000), (-3020773003857/16000), (-3019888119397/48000), (-62358994),
      (-18804757/48000), 7204107596599/96000, (-58340594161/6000), (-233433656969/64000), (-7203681/2),
      (-2592129/64000), (-1626918062583/32000), (-58340594161/6000), (-58340594161/6000), (-9598898),
      (-2349529/24000), 7204107596599/96000, (-233433656969/64000), (-58340594161/6000), (-7203681/2),
      (-2592129/64000), 74415071, (-7203681/2), (-9598898), (-7203681/2),
      (-12), 64316479/96000, (-2592129/64000), (-2349529/24000), (-2592129/64000),
      (-12)] := by
    simp only [blocks, labels, assignments, picks, List.map_cons, List.map_nil, List.flatMap_cons,
      List.flatMap_nil, List.cons_append, List.nil_append]
    repeat' apply congrArg₂ List.cons
    all_goals decide +kernel
  rw [sum_blocks,h]
  norm_num

private theorem value_three : witnessRead 2 = 9041984725911/2000 := by
  have h : blocks.map (blockValue 2) = [
      138429539825853/32000, 10922997040463/192000, 10922997040463/192000, (-4415575509411/64000), 112829737/2,
      89788223/192000, 10922997040463/192000, 233148535669/96000, (-233433656969/64000), 2398217,
      1625929/96000, 10922997040463/192000, 233148535669/96000, (-233433656969/64000), 2398217,
      1625929/96000, (-4415575509411/64000), (-233433656969/64000), (-233433656969/64000), (-7197681/2),
      (-2589329/64000), 112829737/2, 2398217, 2398217, (-7197681/2),
      18, 89788223/192000, 1625929/96000, 1625929/96000, (-2589329/64000),
      18] := by
    simp only [blocks, labels, assignments, picks, List.map_cons, List.map_nil, List.flatMap_cons,
      List.flatMap_nil, List.cons_append, List.nil_append]
    repeat' apply congrArg₂ List.cons
    all_goals decide +kernel
  rw [sum_blocks,h]
  norm_num

private theorem value_four : witnessRead 3 = 18083516817/4 := by
  have h : blocks.map (blockValue 3) = [
      691778428677/160, 45471563269/800, 45471563269/800, 45471563269/800, (-68395419),
      14277/200, 45471563269/800, 3905912507/1600, 3905912507/1600, (-3604858),
      (-139/200), 45471563269/800, 3905912507/1600, 3905912507/1600, (-3604858),
      (-139/200), 45471563269/800, 3905912507/1600, 3905912507/1600, (-3604858),
      (-139/200), (-68395419), (-3604858), (-3604858), (-3604858),
      (-12), 14277/200, (-139/200), (-139/200), (-139/200),
      (-12)] := by
    simp only [blocks, labels, assignments, picks, List.map_cons, List.map_nil, List.flatMap_cons,
      List.flatMap_nil, List.cons_append, List.nil_append]
    repeat' apply congrArg₂ List.cons
    all_goals decide +kernel
  rw [sum_blocks,h]
  norm_num

private theorem value_five : witnessRead 4 = (-565839/2000) := by
  have h : blocks.map (blockValue 4) = [
      (-75679947/32000), 4888628063/192000, 4888628063/192000, 4888628063/192000, (-151053/2),
      (-52302691/64000), 4888628063/192000, 1074802969/96000, 1074802969/96000, (-21601/2),
      (-3714929/64000), 4888628063/192000, 1074802969/96000, 1074802969/96000, (-21601/2),
      (-3714929/64000), 4888628063/192000, 1074802969/96000, 1074802969/96000, (-21601/2),
      (-3714929/64000), (-151053/2), (-21601/2), (-21601/2), (-21601/2),
      (-12), (-52302691/64000), (-3714929/64000), (-3714929/64000), (-3714929/64000),
      (-12)] := by
    simp only [blocks, labels, assignments, picks, List.map_cons, List.map_nil, List.flatMap_cons,
      List.flatMap_nil, List.cons_append, List.nil_append]
    repeat' apply congrArg₂ List.cons
    all_goals decide +kernel
  rw [sum_blocks,h]
  norm_num

/-- Direct polynomial readout for all five positions of the section 9 input. -/
theorem witness_readouts :
    labels.map witnessRead = [9041984725911/2000,9041984725911/2000,9041984725911/2000,
      18083516817/4,-565839/2000] := by
  simp only [labels,List.map_cons,List.map_nil,value_one,value_two,value_three,value_four,value_five]

/-- Equality of the forced-edge calculation with all five original
signed evaluations, independently calculated by the marked-transfer recurrence. -/
theorem witness_eq_transfer :
    labels.map witnessRead = (picks witness).map (fun ⟨p,xs⟩ => markedValue xs p) :=
  witness_readouts.trans all_marked_values.symm

/-- The fifth coefficient readout agrees exactly with the complex
permutation-clasp contraction, including both crossed terms. -/
theorem fifth_eq_clasps :
    witnessRead 4 = (MarkedWitness.markedByClasps MarkedWitness.otherFive fifthPacket).re := by
  rw [MarkedWitness.negative_fifth_full_clasps]
  exact_mod_cast value_five

end
end BlockPermanents.ForcedWitness
