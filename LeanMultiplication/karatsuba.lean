-- Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
import Mathlib

set_option linter.mathlibStandardSet false
open scoped BigOperators Real Nat Classical Pointwise
set_option maxHeartbeats 400000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option relaxedAutoImplicit false
set_option autoImplicit false

def karatsuba_n1 (n : ℤ) (b m : ℕ) : ℤ :=
  n / (b ^ m)
def karatsuba_n0 (n : ℤ) (b m : ℕ) : ℤ :=
  n % (b ^ m)
def digits (b : ℕ) (x : ℤ) : ℕ :=
  (b.digits (Int.natAbs x)).length

lemma bpow_m_le_max_natAbs (x y : ℤ) (b : ℕ) (hb : 1 < b)
    (h : ¬ max (digits b x) (digits b y) ≤ 1) :
    b ^ ((max (digits b x) (digits b y) + 1) / 2) ≤
      max (Int.natAbs x) (Int.natAbs y) := by
  -- By Nat.length_digits, (Nat.digits b (natAbs z)).length = Nat.log b (natAbs z) + 1 (when natAbs z ≠ 0 and b > 1).
  obtain ⟨z, hz⟩ : ∃ z ∈ [x, y], digits b z = max (digits b x) (digits b y) := by
    cases max_choice ( digits b x ) ( digits b y ) <;> aesop
  have h_len : (b.digits (z.natAbs)).length = Nat.log b (z.natAbs) + 1 := by
    by_cases hz_zero : z.natAbs = 0 <;> simp_all +decide [ Nat.length_digits ];
    -- Since `digits b 0 = 0`, we have `max (digits b x) (digits b y) = 0`.
    have h_max_zero : max (digits b x) (digits b y) = 0 := by
      exact hz.2.symm.trans ( by unfold digits; aesop ) ;
    grind +ring
  have h_log : Nat.log b (z.natAbs) = max (digits b x) (digits b y) - 1 := by
    exact eq_tsub_of_add_eq <| hz.2 ▸ h_len ▸ rfl;
  have h_pow : b ^ (max (digits b x) (digits b y) - 1) ≤ z.natAbs := by
    exact h_log ▸ Nat.pow_log_le_self b ( by aesop_cat ) |> le_trans <| by aesop_cat;
  have h_pow_le : b ^ ((max (digits b x) (digits b y) + 1) / 2) ≤ z.natAbs := by
    exact le_trans ( pow_le_pow_right₀ hb.le ( by omega ) ) h_pow
  have h_final : b ^ ((max (digits b x) (digits b y) + 1) / 2) ≤ max (x.natAbs) (y.natAbs) := by
    grind
  exact h_final

lemma natAbs_emod_lt (z : ℤ) (n : ℕ) (hn : 0 < n) :
    (z % (n : ℤ)).natAbs < n := by
  rw [ ← Int.ofNat_lt, Int.natAbs_of_nonneg ( Int.emod_nonneg _ ( by positivity ) ) ] ; simpa using Int.emod_lt_of_pos _ ( by positivity ) ;

lemma natAbs_ediv_lt_of_le_max (z : ℤ) (n : ℕ) (M : ℕ) (hn : 2 ≤ n) (hM : n ≤ M)
    (hz : z.natAbs ≤ M) :
    (z / (n : ℤ)).natAbs < M := by
  cases abs_cases z <;> cases abs_cases ( z / n ) <;> nlinarith [ Int.mul_ediv_add_emod z n, Int.emod_nonneg z ( by positivity : ( n : ℤ ) ≠ 0 ), Int.emod_lt_of_pos z ( by positivity : ( n : ℤ ) > 0 ) ] ;

lemma natAbs_ediv_add_emod_lt_of_le_max (z : ℤ) (n : ℕ) (M : ℕ) (hn : 2 ≤ n) (hM : n ≤ M)
    (hz : z.natAbs ≤ M) :
    (z / (n : ℤ) + z % (n : ℤ)).natAbs < M := by
  -- By definition of division and modulo, we have z = n * (z / n) + (z % n).
  have h_eq : z = (n : ℤ) * (z / (n : ℤ)) + (z % (n : ℤ)) := by
    rw [ Int.mul_ediv_add_emod ];
  cases abs_cases ( z / n + z % n ) <;> cases abs_cases z <;> nlinarith [ Int.emod_nonneg z ( by positivity : ( n : ℤ ) ≠ 0 ), Int.emod_lt_of_pos z ( by positivity : ( n : ℤ ) > 0 ) ]
-- Helper to get b ^ m ≥ 2 from b > 1
private lemma bpow_ge_two (b : ℕ) (hb : 1 < b) (m : ℕ) (hm : 0 < m) : 2 ≤ b ^ m := by
  calc 2 ≤ b := hb
    _ = b ^ 1 := (pow_one b).symm
    _ ≤ b ^ m := Nat.pow_le_pow_right (by omega) hm
private lemma half_pos_of_ge_two (n : ℕ) (hn : ¬ n ≤ 1) : 0 < (n + 1) / 2 := by omega
-- ============================================================
-- The Karatsuba function
-- ============================================================
def karatsuba (x y : ℤ) (b : ℕ) (hb : 1 < b) :=
  if (max (digits b x) (digits b y)) ≤ 1 then
    x * y
  else
    let n := max (digits b x) (digits b y)
    let m  := ((n + 1) / 2)
    let z0 := (karatsuba (karatsuba_n0 x b m)
                                   (karatsuba_n0 y b m)
                                   b hb)
    let z2 := (karatsuba (karatsuba_n1 x b m)
                                   (karatsuba_n1 y b m)
                                   b hb)
    let z3 := (karatsuba ((karatsuba_n1 x b m) + (karatsuba_n0 x b m))
                                   ((karatsuba_n1 y b m)  + (karatsuba_n0 y b m))
                                   b hb)
    z2 * (b ^ (2 * m)) + (z3 - z2 - z0) * (b ^ m) + z0
termination_by max (Int.natAbs x) (Int.natAbs y)
decreasing_by all_goals (
    simp only [karatsuba_n0, karatsuba_n1]
    rename_i hnd
    have hbm := bpow_m_le_max_natAbs x y b hb hnd
    have hm_pos := half_pos_of_ge_two _ hnd
    have hbm2 := bpow_ge_two b hb _ hm_pos
    apply Nat.max_lt.mpr; constructor
    · first
        | exact Nat.lt_of_lt_of_le (natAbs_emod_lt x _ (by positivity)) hbm
        | exact natAbs_ediv_lt_of_le_max x _ _ hbm2 hbm (le_max_left _ _)
        | exact natAbs_ediv_add_emod_lt_of_le_max x _ _ hbm2 hbm (le_max_left _ _)
    · first
        | exact Nat.lt_of_lt_of_le (natAbs_emod_lt y _ (by positivity)) hbm
        | exact natAbs_ediv_lt_of_le_max y _ _ hbm2 hbm (le_max_right _ _)
        | exact natAbs_ediv_add_emod_lt_of_le_max y _ _ hbm2 hbm (le_max_right _ _)
  )

theorem karatsuba_correctness (x y : ℤ) (b : ℕ) (hb : 1 < b)
: karatsuba x y b hb = x * y
:= by
  -- We'll use induction on the maximum of the number of digits of $x$ and $y$.
  induction' h_max : (max (Int.natAbs x) (Int.natAbs y)) using Nat.strong_induction_on with m ih generalizing x y b hb;
  by_cases h : max ( digits b x ) ( digits b y ) ≤ 1 <;> simp_all +decide [ Int.natAbs_mul ];
  · unfold karatsuba; aesop;
  · -- Let $m = \frac{\max(\text{digits}(b, x), \text{digits}(b, y)) + 1}{2}$.
    set m' := (max (digits b x) (digits b y) + 1) / 2 with hm';
    -- By the induction hypothesis, we have:
    have h_ih0 : karatsuba (x % (b ^ m')) (y % (b ^ m')) b hb = (x % (b ^ m')) * (y % (b ^ m')) := by
      apply ih (max (Int.natAbs (x % (b ^ m'))) (Int.natAbs (y % (b ^ m')))) (by
      have h_max_lt : b ^ m' ≤ max (Int.natAbs x) (Int.natAbs y) := by
        apply bpow_m_le_max_natAbs x y b hb (by
        grind)
      generalize_proofs at *; (
      have h_mod_lt : ∀ z : ℤ, (z % (b ^ m')).natAbs < b ^ m' := by
        exact fun z => by rw [ ← Int.ofNat_lt, Int.natAbs_of_nonneg ( Int.emod_nonneg _ ( by positivity ) ) ] ; exact Int.emod_lt_of_pos _ ( by positivity ) ; ;
      generalize_proofs at *; (
      exact max_lt ( lt_of_lt_of_le ( h_mod_lt x ) ( by linarith ) ) ( lt_of_lt_of_le ( h_mod_lt y ) ( by linarith ) ) ;))) (x % (b ^ m')) (y % (b ^ m')) b hb
      generalize_proofs at *; (
      rfl)
    have h_ih1 : karatsuba (x / (b ^ m')) (y / (b ^ m')) b hb = (x / (b ^ m')) * (y / (b ^ m')) := by
      apply ih (max (Int.natAbs (x / (b ^ m'))) (Int.natAbs (y / (b ^ m')))) (by
      have h_ih1 : (x / (b ^ m')).natAbs < m ∧ (y / (b ^ m')).natAbs < m := by
        apply And.intro (natAbs_ediv_lt_of_le_max x (b ^ m') m (by
        exact bpow_ge_two b hb m' ( half_pos_of_ge_two _ ( by contrapose! h; aesop ) ) |> le_trans <| le_rfl;) (by
        convert bpow_m_le_max_natAbs x y b hb _ using 1 ; aesop ( simp_config := { singlePass := true } ) ;
        grind +ring) (by
        exact h_max ▸ le_max_left _ _)) (natAbs_ediv_lt_of_le_max y (b ^ m') m (by
        exact bpow_ge_two b hb m' ( half_pos_of_ge_two _ ( by contrapose! h; aesop ) ) |> le_trans <| le_rfl;) (by
        convert bpow_m_le_max_natAbs x y b hb _ using 1 ; aesop ( simp_config := { singlePass := true } ) ;
        grind +ring) (by
        exact h_max ▸ le_max_right _ _))
      generalize_proofs at *; (
      exact max_lt h_ih1.1 h_ih1.2)) (x / (b ^ m')) (y / (b ^ m')) b hb
      generalize_proofs at *; (
      rfl)
    have h_ih2 : karatsuba ((x / (b ^ m')) + (x % (b ^ m'))) ((y / (b ^ m')) + (y % (b ^ m'))) b hb = ((x / (b ^ m')) + (x % (b ^ m'))) * ((y / (b ^ m')) + (y % (b ^ m'))) := by
      apply ih (max (Int.natAbs (x / (b ^ m') + x % (b ^ m'))) (Int.natAbs (y / (b ^ m') + y % (b ^ m')))) (by
      have h_ih2 : (x / (b ^ m') + x % (b ^ m')).natAbs < m := by
        convert natAbs_ediv_add_emod_lt_of_le_max x ( b ^ m' ) m _ _ _ using 1 <;> norm_num [ hm', h_max ];
        · exact one_lt_pow₀ hb ( Nat.ne_of_gt ( Nat.div_pos ( by linarith [ show 1 ≤ max ( digits b x ) ( digits b y ) from Nat.pos_of_ne_zero ( by aesop_cat ) ] ) zero_lt_two ) ) |> le_trans ( by norm_num ) ;
        · convert bpow_m_le_max_natAbs x y b hb _ using 1 <;> aesop ( simp_config := { singlePass := true } ) ;
        · exact h_max ▸ le_max_left _ _
      have h_ih3 : (y / (b ^ m') + y % (b ^ m')).natAbs < m := by
        apply natAbs_ediv_add_emod_lt_of_le_max y (b ^ m') m (by
        exact one_lt_pow₀ hb ( Nat.ne_of_gt ( Nat.div_pos ( by linarith [ show 1 ≤ max ( digits b x ) ( digits b y ) from Nat.pos_of_ne_zero ( by aesop_cat ) ] ) zero_lt_two ) ) |> le_trans ( by norm_num ) ;) (by
        have := bpow_m_le_max_natAbs x y b hb (by
        contrapose! h; aesop;) ; aesop;) (by
        exact h_max ▸ le_max_right _ _ |> le_trans ( by norm_num ) ;)
      exact max_lt h_ih2 h_ih3) (x / (b ^ m') + x % (b ^ m')) (y / (b ^ m') + y % (b ^ m')) b hb
      generalize_proofs at *; (
      rfl)
    generalize_proofs at *; (
    -- Substitute the induction hypotheses into the expression for karatsuba.
    have h_subst : karatsuba x y b hb = (x / (b ^ m')) * (y / (b ^ m')) * (b ^ (2 * m')) + ((x / (b ^ m') + x % (b ^ m')) * (y / (b ^ m') + y % (b ^ m')) - (x / (b ^ m')) * (y / (b ^ m')) - (x % (b ^ m')) * (y % (b ^ m'))) * (b ^ m') + (x % (b ^ m')) * (y % (b ^ m')) := by
      rw [karatsuba]
      generalize_proofs at *; (
      unfold karatsuba_n0 karatsuba_n1; aesop;)
    generalize_proofs at *; (
    rw [ h_subst ] ; ring;
    rw [ pow_mul ] ; rw [ Int.emod_def, Int.emod_def ] ; ring;))
