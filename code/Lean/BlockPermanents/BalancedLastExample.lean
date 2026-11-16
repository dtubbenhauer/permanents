import BlockPermanents.BalancedSupport
import BlockPermanents.BalancedPacketEnergy
import BlockPermanents.Coarse

/-! The example 6B.4 following Lemma 6B.3. Four copies of a unit packet give a
shortfall of seven in the available cubic single-edge diagonal. -/
namespace BlockPermanents.BalancedLastExample
open Bend BalancedRoutes BalancedSupport
noncomputable section

/-- Two upright copies of F followed by two turned copies. -/
def boundary {K : Type*} (F : K → ℂ) : Four K → ℂ :=
  product (product F F) (fun p => star (product F F p))

/-- An upright copy and a turned copy survive each crossing-edge cap. -/
def survivor {K : Type*} (F : K → ℂ) : K × K → ℂ :=
  product F (fun x => star (F x))

theorem routes {K : Type*} [Fintype K] (F : K → ℂ) (hF : energy F = 1) :
    L00 (boundary F) = survivor F ∧ L01 (boundary F) = survivor F ∧
    L10 (boundary F) = survivor F ∧ L11 (boundary F) = survivor F := by
  have unit : (∑ x, star (F x) * F x) = 1 := by
    change Closures.bracket F F = 1
    rw [Coarse.bracket_self, hF, Complex.ofReal_one]
  have eval (i j : K) :
      (∑ x, star (F x) * F x * (F i * star (F j))) = F i * star (F j) := by
    rw [← Finset.sum_mul, unit, one_mul]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> funext p <;>
    simp only [L00, L01, L10, L11, boundary, survivor, product, star_mul] <;>
    apply Eq.trans _ (eval p.1 p.2) <;>
    apply Finset.sum_congr rfl <;> intro x hx <;> ring

theorem survivor_energy {K : Type*} [Fintype K] (F : K → ℂ) (hF : energy F = 1) :
    energy (survivor F) = 1 := by
  simpa only [energy, survivor, product, Fintype.sum_prod_type, Complex.normSq_mul,
    Complex.star_def, Complex.normSq_conj, ← Finset.mul_sum, ← Finset.sum_mul]
    using (show energy F * energy F = 1 by rw [hF,one_mul])

/-- The coherent sum has energy sixteen. The available cubic diagonal is
nine, leaving precisely seven to be recovered from the surviving packets. -/
theorem cubic_shortfall {K : Type*} [Fintype K] (F : K → ℂ) (hF : energy F = 1) :
    let z := boundary F
    let D := lastWeight 3 / 2 * (energy (L00 z) + energy (L01 z) +
      energy (L10 z) + energy (L11 z))
    D = 9 ∧ energy (BalancedPacket.oneSum z) = 16 ∧ energy (BalancedPacket.oneSum z) - D = 7 := by
  dsimp only
  obtain ⟨h₀₀,h₀₁,h₁₀,h₁₁⟩ := routes F hF
  have addFour : BalancedPacket.oneSum (boundary F) = fun p => (4 : ℂ) * survivor F p := by
    funext p
    simp only [BalancedPacket.oneSum,h₀₀,h₀₁,h₁₀,h₁₁]
    ring
  have sumEnergy : energy (BalancedPacket.oneSum (boundary F)) = 16 := by
    rw [addFour]
    change ∑ i, Complex.normSq (4 * survivor F i) = _
    simp only [Complex.normSq_mul, ← Finset.mul_sum]
    change Complex.normSq 4 * energy (survivor F) = _
    rw [survivor_energy F hF]
    norm_num
  rw [h₀₀,h₀₁,h₁₀,h₁₁,survivor_energy F hF,sumEnergy,cubic_weight]
  norm_num

end
end BlockPermanents.BalancedLastExample
