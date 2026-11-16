import BlockPermanents.FiveAverage
import BlockPermanents.FiveMixedSquares

/-! Exact averaging of the two mixed gluings in the five-packet proof. -/
namespace BlockPermanents.FiveMixedAverageSquares
open Bend Closures FiveProjection FiveCycles
open scoped BigOperators
noncomputable section

/-- Sum the distinct ordered exits available among the q labels after the
shared packet and any spectator pair have been fixed. -/
def ordered {q : ℕ} (idx : Fin q → Fin 5) (Y T : FiveAverage.Forms) (σ : S) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.erase i,
    ((T (σ 2) (σ (idx i)) (σ (idx i))).re +
      2 * (star (Y (σ 2) (σ (idx j)) (σ (idx i))) * T (σ 2) (σ (idx j)) (σ (idx i))).re)

open private avg_finset_sum from BlockPermanents.FiveAverage in
private theorem orbit {q : ℕ} (idx : Fin q → Fin 5) (Y T : FiveAverage.Forms)
    (w : S → ℝ) (move : ∀ i j : Fin q, i ≠ j → ∃ τ : S,
      τ 0 = idx j ∧ τ 1 = idx i ∧ τ 2 = 2 ∧ ∀ σ : S, w (σ*τ) = w σ) :
    avg (fun σ => w σ * ordered idx Y T σ) = (q : ℝ) * (q-1 : ℕ) *
      avg (fun σ => w σ * FiveAverage.residual Y T σ) := by
  let term (i j : Fin q) (σ : S) := w σ *
    ((T (σ 2) (σ (idx i)) (σ (idx i))).re +
      2 * (star (Y (σ 2) (σ (idx j)) (σ (idx i))) * T (σ 2) (σ (idx j)) (σ (idx i))).re)
  have each (i j : Fin q) (hij : j ∈ Finset.univ.erase i) :
      avg (term i j) = avg (fun σ => w σ * FiveAverage.residual Y T σ) := by
    obtain ⟨τ,h₀,h₁,h₂,hw⟩ := move i j (Finset.ne_of_mem_erase hij).symm
    rw [← avg_relabel τ (fun σ => w σ * FiveAverage.residual Y T σ)]
    congr 1
    funext σ
    simp only [term, FiveAverage.residual, hw, Equiv.Perm.mul_apply, h₀,h₁,h₂]
  have row (i : Fin q) : (∑ j ∈ Finset.univ.erase i, avg (term i j)) =
      (q-1 : ℕ) * avg (fun σ => w σ * FiveAverage.residual Y T σ) := by
    rw [Finset.sum_congr rfl fun j hj => each i j hj]
    simp [Finset.card_erase_of_mem, nsmul_eq_mul]
  simp only [ordered, Finset.mul_sum]
  change avg (fun σ => ∑ i, ∑ j ∈ Finset.univ.erase i, term i j σ) = _
  rw [avg_sum]
  simp_rw [avg_finset_sum]
  simp only [row, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]

/-- G,F,I,J are the four free labels at fixed H. -/
def four : Fin 4 → Fin 5 := ![0,1,3,4]

/-- G,F are the two free labels at fixed H,I,J. -/
def two : Fin 2 → Fin 5 := ![0,1]

open private moveSlots four_move from BlockPermanents.FiveAverage in
theorem four_orbit (Y T : FiveAverage.Forms) :
    avg (FiveAverage.residual Y T) = avg (ordered four Y T) / 12 := by
  have h := orbit four Y T (fun _ => 1) (fun i j hij => by
    obtain ⟨h₀,h₁,h₂⟩ := four_move i j hij
    exact ⟨_,h₀,h₁,h₂,fun _ => rfl⟩)
  norm_num at h
  linarith

open private moveSlots two_move from BlockPermanents.FiveAverage in
theorem two_orbit (Y T : FiveAverage.Forms) (w : Fin 5 → Fin 5 → ℝ) :
    avg (fun σ => w (σ 3) (σ 4) * FiveAverage.residual Y T σ) =
      avg (fun σ => w (σ 3) (σ 4) * ordered two Y T σ) / 2 := by
  have h := orbit two Y T (fun σ => w (σ 3) (σ 4)) (fun i j hij => by
    obtain ⟨h₀,h₁,h₂,h₃,h₄⟩ := two_move i j hij
    exact ⟨_,h₀,h₁,h₂,fun σ => by simp only [Equiv.Perm.mul_apply,h₃,h₄]⟩)
  norm_num at h
  linarith

variable {d k : ℕ}

def tests (x : Fin 5 → Fin k → Fin d → ℂ) (l m : ℝ) : FiveAverage.Forms :=
  fun h => testForm l m (packet (x h)) (fun i => packet (x i))

def remainders (x : Fin 5 → Fin k → Fin d → ℂ) : FiveAverage.Forms :=
  fun h => remainderForm (packet (x h)) (fun i => packet (x i))

/-- For one choice of the frozen labels, glue the two mixed exits and retain
the q diagonal terms left after deleting equal labels. -/
def exits {q : ℕ} (x : Fin 5 → Fin k → Fin d → ℂ) (l m : ℝ)
    (idx : Fin q → Fin 5) (σ : S) : ℝ :=
  (∑ i, ((q : ℝ)-1 - 2 * (tests x l m (σ 2) (σ (idx i)) (σ (idx i))).re) *
    (remainders x (σ 2) (σ (idx i)) (σ (idx i))).re) +
    2 * energy (FiveMixedSquares.physicalHalf l m 1 (x (σ 2)) (fun i => packet (x (σ (idx i)))))

private theorem scaled_one (a : Fin k → Fin d → ℂ) : PairResidual.scaled 1 a = packet a := by
  funext i
  exact one_mul _

theorem ordered_eq_exits {q : ℕ} (hk : 3 ≤ k) (x : Fin 5 → Fin k → Fin d → ℂ)
    (hu : ∀ i, energy (packet (x i)) = 1) (l m : ℝ) (hl : 0 ≤ l) (hm : 0 ≤ m)
    (idx : Fin q → Fin 5) (σ : S) :
    ordered idx (tests x l m) (remainders x) σ = exits x l m idx σ := by
  have he := FiveMixedSquares.physical_trace hk l m hl hm 1 (x (σ 2))
    (by rw [scaled_one,hu]) (fun i => packet (x (σ (idx i)))) (fun i => Bridges.packet_symmetric _ _ _)
  simpa only [scaled_one,Fintype.card_fin] using he

theorem exits_nonneg {q : ℕ} (hk : 3 ≤ k) (x : Fin 5 → Fin k → Fin d → ℂ)
    (hu : ∀ i, energy (packet (x i)) = 1) (l m : ℝ) (hl : 0 ≤ l) (hm : 0 ≤ m)
    (hq : 2*(l+m) ≤ (q : ℝ)-1) (idx : Fin q → Fin 5) (σ : S) : 0 ≤ exits x l m idx σ := by
  rw [← ordered_eq_exits hk x hu l m hl hm idx σ]
  have he := FiveMixedSquares.physical_trace_lower hk l m hl hm (by simpa only [Fintype.card_fin] using hq)
    1 (x (σ 2)) (by rw [scaled_one,hu]) (fun i => packet (x (σ (idx i))))
    (fun i => Bridges.packet_symmetric _ _ _) (fun i => hu _)
  rw [scaled_one] at he
  exact (mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)).trans he

/-- The unconditional twelve ordered exits at H give the unweighted mixed average. -/
theorem plain_squares (hk : 3 ≤ k) (x : Fin 5 → Fin k → Fin d → ℂ)
    (hu : ∀ i, energy (packet (x i)) = 1) (l m : ℝ) (hl : 0 ≤ l) (hm : 0 ≤ m) :
    avg (FiveAverage.residual (tests x l m) (remainders x)) =
      avg (fun σ => exits x l m four σ) / 12 := by
  rw [four_orbit]
  simp_rw [show ordered four (tests x l m) (remainders x) = fun σ => exits x l m four σ
    from funext (ordered_eq_exits hk x hu l m hl hm four)]

/-- Fixing the spectator edge leaves two ordered exits. Its weight passes
through each gluing before the average is taken. -/
theorem weighted_squares (hk : 3 ≤ k) (x : Fin 5 → Fin k → Fin d → ℂ)
    (hu : ∀ i, energy (packet (x i)) = 1) (l m : ℝ) (hl : 0 ≤ l) (hm : 0 ≤ m)
    (w : Fin 5 → Fin 5 → ℝ) :
    avg (fun σ => w (σ 3) (σ 4) * FiveAverage.residual (tests x l m) (remainders x) σ) =
      avg (fun σ => w (σ 3) (σ 4) * exits x l m two σ) / 2 := by
  rw [two_orbit]
  simp_rw [ordered_eq_exits hk x hu l m hl hm]

end
end BlockPermanents.FiveMixedAverageSquares
