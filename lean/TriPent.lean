import Mathlib

/-!
# Sums of two triangular numbers and a pentagonal number

Formalization of the elementary part of the paper
"Every natural number is a sum of two triangular numbers and a pentagonal number".

The classical input (primitive representation by `x² + 3y² + 3z²` and `x² + y² + 3z²`,
Proposition 4.1 of the paper) is not proved here; it enters as the explicit hypotheses
`PrimRep133` and `PrimRep113`.
-/

namespace TriPent

/-! ## The partner of an odd pair (Section 2) -/

theorem normI {u v u' v' : ℤ} (h1 : 2 * u' = u + v) (h2 : 2 * v' = 3 * u - v) :
    3 * u' ^ 2 + v' ^ 2 = 3 * u ^ 2 + v ^ 2 := by
  have : 4 * (3 * u' ^ 2 + v' ^ 2) = 4 * (3 * u ^ 2 + v ^ 2) := by
    linear_combination 3 * (2 * u' + u + v) * h1 + (2 * v' + 3 * u - v) * h2
  linarith

theorem normII {u v u' v' : ℤ} (h1 : 2 * u' = u + v) (h2 : 2 * v' = v - 3 * u) :
    3 * u' ^ 2 + v' ^ 2 = 3 * u ^ 2 + v ^ 2 := by
  have : 4 * (3 * u' ^ 2 + v' ^ 2) = 4 * (3 * u ^ 2 + v ^ 2) := by
    linear_combination 3 * (2 * u' + u + v) * h1 + (2 * v' + v - 3 * u) * h2
  linarith

theorem normIII {u v u' v' : ℤ} (h1 : 2 * u' = u - v) (h2 : 2 * v' = 3 * u + v) :
    3 * u' ^ 2 + v' ^ 2 = 3 * u ^ 2 + v ^ 2 := by
  have : 4 * (3 * u' ^ 2 + v' ^ 2) = 4 * (3 * u ^ 2 + v ^ 2) := by
    linear_combination 3 * (2 * u' + u - v) * h1 + (2 * v' + 3 * u + v) * h2
  linarith

theorem normIII' {u v u' v' : ℤ} (h1 : 2 * u' = v - u) (h2 : 2 * v' = 3 * u + v) :
    3 * u' ^ 2 + v' ^ 2 = 3 * u ^ 2 + v ^ 2 := by
  have : 4 * (3 * u' ^ 2 + v' ^ 2) = 4 * (3 * u ^ 2 + v ^ 2) := by
    linear_combination 3 * (2 * u' + v - u) * h1 + (2 * v' + 3 * u + v) * h2
  linarith

/-- Lemma 2.2: an odd positive pair `(u, v)` with `3 ∤ v` has a partner `(u', v')` with the same
value of `3u² + v²`. Either `v'` and `v` have different residues mod 3 (cases II, III), or the
partner is given by the linear formulas of case I. -/
theorem partner (u v : ℤ) (hu0 : 0 < u) (hv0 : 0 < v) (hu : u % 2 = 1) (hv : v % 2 = 1)
    (hv3 : v % 3 ≠ 0) :
    ∃ u' v' : ℤ, 0 < u' ∧ 0 < v' ∧ u' % 2 = 1 ∧ v' % 2 = 1 ∧ v' % 3 ≠ 0 ∧
      3 * u' ^ 2 + v' ^ 2 = 3 * u ^ 2 + v ^ 2 ∧
      (v' % 3 ≠ v % 3 ∨ (v < 3 * u ∧ 2 * u' = u + v ∧ 2 * v' = 3 * u - v)) := by
  by_cases h4 : (u - v) % 4 = 0
  · rcases lt_or_gt_of_ne (show v ≠ 3 * u by omega) with hlt | hgt
    · -- case I
      obtain ⟨u', h1⟩ : ∃ u' : ℤ, 2 * u' = u + v := ⟨(u + v) / 2, by omega⟩
      obtain ⟨v', h2⟩ : ∃ v' : ℤ, 2 * v' = 3 * u - v := ⟨(3 * u - v) / 2, by omega⟩
      exact ⟨u', v', by omega, by omega, by omega, by omega, by omega, normI h1 h2,
        Or.inr ⟨hlt, h1, h2⟩⟩
    · -- case II
      obtain ⟨u', h1⟩ : ∃ u' : ℤ, 2 * u' = u + v := ⟨(u + v) / 2, by omega⟩
      obtain ⟨v', h2⟩ : ∃ v' : ℤ, 2 * v' = v - 3 * u := ⟨(v - 3 * u) / 2, by omega⟩
      exact ⟨u', v', by omega, by omega, by omega, by omega, by omega, normII h1 h2,
        Or.inl (by omega)⟩
  · -- case III
    obtain ⟨v', h2⟩ : ∃ v' : ℤ, 2 * v' = 3 * u + v := ⟨(3 * u + v) / 2, by omega⟩
    rcases lt_or_gt_of_ne (show u ≠ v by omega) with hlt | hgt
    · obtain ⟨u', h1⟩ : ∃ u' : ℤ, 2 * u' = v - u := ⟨(v - u) / 2, by omega⟩
      exact ⟨u', v', by omega, by omega, by omega, by omega, by omega, normIII' h1 h2,
        Or.inl (by omega)⟩
    · obtain ⟨u', h1⟩ : ∃ u' : ℤ, 2 * u' = u - v := ⟨(u - v) / 2, by omega⟩
      exact ⟨u', v', by omega, by omega, by omega, by omega, by omega, normIII h1 h2,
        Or.inl (by omega)⟩

/-! ## The 2-adic lemma (Lemma 3.1) -/

/-- A sequence of integer pairs that is periodic, bounded, and satisfies a linear recurrence
`Rel` with the two properties below, is identically zero. -/
theorem descent {Rel : ℤ → ℤ → ℤ → ℤ → Prop}
    (hlin : ∀ p q p' q', Rel (2 * p) (2 * q) (2 * p') (2 * q') → Rel p q p' q')
    (heven : ∀ p q p' q' pm qm, Rel p q p' q' → Rel pm qm p q → p % 2 = 0 ∧ q % 2 = 0) :
    ∀ (B : ℕ) (z : ℕ → ℤ × ℤ),
      (∀ k, Rel (z k).1 (z k).2 (z (k + 1)).1 (z (k + 1)).2) →
      ∀ r : ℕ, 1 ≤ r → (∀ k, z (k + r) = z k) →
      (∀ k, -(B : ℤ) ≤ (z k).1 ∧ (z k).1 ≤ B ∧ -(B : ℤ) ≤ (z k).2 ∧ (z k).2 ≤ B) →
      ∀ k, z k = (0, 0) := by
  intro B
  induction B using Nat.strong_induction_on with
  | _ B ih =>
    intro z hrec r hr hper hB k
    have hev : ∀ k, (z k).1 % 2 = 0 ∧ (z k).2 % 2 = 0 := by
      intro k
      have h1 := hrec k
      have h2 := hrec (k + r - 1)
      have e : k + r - 1 + 1 = k + r := by omega
      rw [e, hper k] at h2
      exact heven _ _ _ _ _ _ h1 h2
    by_cases hB0 : B = 0
    · subst hB0
      have hk := hB k
      have h1 : (z k).1 = 0 := by omega
      have h2 : (z k).2 = 0 := by omega
      exact Prod.ext h1 h2
    · have hz := ih (B / 2) (by omega) (fun k => ((z k).1 / 2, (z k).2 / 2)) ?_ r hr ?_ ?_ k
      · have hk := hev k
        have hz1 : (z k).1 / 2 = 0 := congrArg Prod.fst hz
        have hz2 : (z k).2 / 2 = 0 := congrArg Prod.snd hz
        have h1 : (z k).1 = 0 := by omega
        have h2 : (z k).2 = 0 := by omega
        exact Prod.ext h1 h2
      · intro k
        apply hlin
        have a1 := hev k
        have a2 := hev (k + 1)
        have e1 : 2 * ((z k).1 / 2) = (z k).1 := by omega
        have e2 : 2 * ((z k).2 / 2) = (z k).2 := by omega
        have e3 : 2 * ((z (k + 1)).1 / 2) = (z (k + 1)).1 := by omega
        have e4 : 2 * ((z (k + 1)).2 / 2) = (z (k + 1)).2 := by omega
        show Rel (2 * ((z k).1 / 2)) (2 * ((z k).2 / 2)) (2 * ((z (k + 1)).1 / 2))
          (2 * ((z (k + 1)).2 / 2))
        rw [e1, e2, e3, e4]
        exact hrec k
      · intro k
        show ((z (k + r)).1 / 2, (z (k + r)).2 / 2) = ((z k).1 / 2, (z k).2 / 2)
        rw [hper k]
      · intro k
        have hk := hB k
        have hk2 := hev k
        show -((B / 2 : ℕ) : ℤ) ≤ (z k).1 / 2 ∧ (z k).1 / 2 ≤ ((B / 2 : ℕ) : ℤ) ∧
          -((B / 2 : ℕ) : ℤ) ≤ (z k).2 / 2 ∧ (z k).2 / 2 ≤ ((B / 2 : ℕ) : ℤ)
        omega

/-- The recurrence given by the matrix `M₁`. -/
def Rel1 (p q p' q' : ℤ) : Prop := 4 * p' = 5 * p - 6 * q ∧ 4 * q' = 6 * p - 4 * q

/-- The recurrence given by the matrix `M₂`. -/
def Rel2 (p q p' q' : ℤ) : Prop := 4 * p' = -3 * p - 2 * q ∧ 4 * q' = 2 * p - 4 * q

theorem descent1 : ∀ (B : ℕ) (z : ℕ → ℤ × ℤ),
    (∀ k, Rel1 (z k).1 (z k).2 (z (k + 1)).1 (z (k + 1)).2) →
    ∀ r : ℕ, 1 ≤ r → (∀ k, z (k + r) = z k) →
    (∀ k, -(B : ℤ) ≤ (z k).1 ∧ (z k).1 ≤ B ∧ -(B : ℤ) ≤ (z k).2 ∧ (z k).2 ≤ B) →
    ∀ k, z k = (0, 0) :=
  descent (Rel := Rel1)
    (by rintro p q p' q' ⟨h1, h2⟩; exact ⟨by omega, by omega⟩)
    (by rintro p q p' q' pm qm ⟨h1, h2⟩ ⟨h3, h4⟩; exact ⟨by omega, by omega⟩)

theorem descent2 : ∀ (B : ℕ) (z : ℕ → ℤ × ℤ),
    (∀ k, Rel2 (z k).1 (z k).2 (z (k + 1)).1 (z (k + 1)).2) →
    ∀ r : ℕ, 1 ≤ r → (∀ k, z (k + r) = z k) →
    (∀ k, -(B : ℤ) ≤ (z k).1 ∧ (z k).1 ≤ B ∧ -(B : ℤ) ≤ (z k).2 ∧ (z k).2 ≤ B) →
    ∀ k, z k = (0, 0) :=
  descent (Rel := Rel2)
    (by rintro p q p' q' ⟨h1, h2⟩; exact ⟨by omega, by omega⟩)
    (by rintro p q p' q' pm qm ⟨h1, h2⟩ ⟨h3, h4⟩; exact ⟨by omega, by omega⟩)

/-- A periodic point of a self-map: if `f^[i] x = f^[j] x` with `i < j`, the orbit from `i` on
has period `j - i`. -/
theorem iterate_periodic {α : Type*} (f : α → α) (x : α) {i j : ℕ} (hij : i < j)
    (h : f^[i] x = f^[j] x) (k : ℕ) : f^[i + k + (j - i)] x = f^[i + k] x := by
  have e : i + k + (j - i) = k + j := by omega
  rw [e, Function.iterate_add_apply, ← h, ← Function.iterate_add_apply, Nat.add_comm]

/-! ## Theorem 3.2 -/

/-- `(v, a, b)` is a solution of `v² + 3a² + 3b² = N` in odd positive integers with `3 ∤ v`. -/
def IsS (N v a b : ℤ) : Prop :=
  0 < v ∧ 0 < a ∧ 0 < b ∧ v % 2 = 1 ∧ a % 2 = 1 ∧ b % 2 = 1 ∧ v % 3 ≠ 0 ∧
    v ^ 2 + 3 * a ^ 2 + 3 * b ^ 2 = N

theorem IsS.le {N v a b : ℤ} (h : IsS N v a b) : v ≤ N ∧ a ≤ N ∧ b ≤ N := by
  obtain ⟨hv0, ha0, hb0, -, -, -, -, heq⟩ := h
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

/-- The move `α`: either some solution has a different residue of `v` mod 3, or `α` is the
linear map `A`. -/
theorem IsS.moveA {N v a b : ℤ} (h : IsS N v a b) :
    (∃ v' a' b', IsS N v' a' b' ∧ v' % 3 ≠ v % 3) ∨
      IsS N ((3 * a - v) / 2) ((a + v) / 2) b := by
  obtain ⟨hv0, ha0, hb0, hv, ha, hb, hv3, heq⟩ := h
  obtain ⟨a', v', ha'0, hv'0, ha', hv', hv'3, hn, hcase⟩ := partner a v ha0 hv0 ha hv hv3
  have hS : IsS N v' a' b := ⟨hv'0, ha'0, hb0, hv', ha', hb, hv'3, by linarith⟩
  rcases hcase with hne | ⟨_, h1, h2⟩
  · exact Or.inl ⟨v', a', b, hS, hne⟩
  · right
    have e1 : (3 * a - v) / 2 = v' := by omega
    have e2 : (a + v) / 2 = a' := by omega
    rw [e1, e2]
    exact hS

/-- The move `β`. -/
theorem IsS.moveB {N v a b : ℤ} (h : IsS N v a b) :
    (∃ v' a' b', IsS N v' a' b' ∧ v' % 3 ≠ v % 3) ∨
      IsS N ((3 * b - v) / 2) a ((b + v) / 2) := by
  obtain ⟨hv0, ha0, hb0, hv, ha, hb, hv3, heq⟩ := h
  obtain ⟨b', v', hb'0, hv'0, hb', hv', hv'3, hn, hcase⟩ := partner b v hb0 hv0 hb hv hv3
  have hS : IsS N v' a b' := ⟨hv'0, ha0, hb'0, hv', ha, hb', hv'3, by linarith⟩
  rcases hcase with hne | ⟨_, h1, h2⟩
  · exact Or.inl ⟨v', a, b', hS, hne⟩
  · right
    have e1 : (3 * b - v) / 2 = v' := by omega
    have e2 : (b + v) / 2 = b' := by omega
    rw [e1, e2]
    exact hS

/-- The map `R = BA` on triples `(v, a, b)`. -/
def stepS (s : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  ((3 * s.2.2 - (3 * s.2.1 - s.1) / 2) / 2, (s.2.1 + s.1) / 2,
    (s.2.2 + (3 * s.2.1 - s.1) / 2) / 2)

theorem stepS_rec {N : ℤ} {s : ℤ × ℤ × ℤ} (h : IsS N s.1 s.2.1 s.2.2)
    (hA : IsS N ((3 * s.2.1 - s.1) / 2) ((s.2.1 + s.1) / 2) s.2.2) :
    Rel1 (s.2.1 - s.1) (s.2.2 - s.1) ((stepS s).2.1 - (stepS s).1)
      ((stepS s).2.2 - (stepS s).1) := by
  obtain ⟨-, -, -, hv, ha, hb, -, -⟩ := h
  obtain ⟨-, -, -, hv1, -, -, -, -⟩ := hA
  simp only [stepS, Rel1]
  constructor <;> omega

/-- **Theorem 3.2.** If `v² + 3a² + 3b² = N` has a solution in odd positive integers with
`3 ∤ v` that is not diagonal, then it has such a solution with the other residue of `v` mod 3. -/
theorem exists_other_residue {N v a b : ℤ} (h : IsS N v a b) (hnd : ¬(v = a ∧ a = b)) :
    ∃ v' a' b', IsS N v' a' b' ∧ v' % 3 ≠ v % 3 := by
  by_contra hcon
  push Not at hcon
  -- under `hcon`, the set of solutions is closed under the linear maps `A` and `R = BA`
  have hcl : ∀ s : ℤ × ℤ × ℤ, IsS N s.1 s.2.1 s.2.2 →
      IsS N ((3 * s.2.1 - s.1) / 2) ((s.2.1 + s.1) / 2) s.2.2 ∧
      IsS N (stepS s).1 (stepS s).2.1 (stepS s).2.2 := by
    intro s hs
    have hA : IsS N ((3 * s.2.1 - s.1) / 2) ((s.2.1 + s.1) / 2) s.2.2 := by
      rcases hs.moveA with ⟨v', a', b', h', hne⟩ | h'
      · exact absurd ((hcon v' a' b' h').trans (hcon _ _ _ hs).symm) hne
      · exact h'
    refine ⟨hA, ?_⟩
    rcases hA.moveB with ⟨v', a', b', h', hne⟩ | h'
    · exact absurd ((hcon v' a' b' h').trans (hcon _ _ _ hA).symm) hne
    · exact h'
  have ht : ∀ j, IsS N (stepS^[j] (v, a, b)).1 (stepS^[j] (v, a, b)).2.1
      (stepS^[j] (v, a, b)).2.2 := by
    intro j
    induction j with
    | zero => exact h
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact (hcl _ ih).2
  have hN : 0 < N := by
    have := h.le
    have := h.1
    omega
  -- the orbit is contained in a finite box, hence eventually periodic
  have hbd : ∀ j, stepS^[j] (v, a, b) ∈ Set.Icc ((0, 0, 0) : ℤ × ℤ × ℤ) (N, N, N) := by
    intro j
    have h1 := ht j
    have h2 := h1.le
    exact ⟨⟨h1.1.le, h1.2.1.le, h1.2.2.1.le⟩, ⟨h2.1, h2.2.1, h2.2.2⟩⟩
  obtain ⟨i, j, hij, hEq⟩ := (Set.finite_Icc _ _).exists_lt_map_eq_of_forall_mem hbd
  have hper := iterate_periodic stepS (v, a, b) hij hEq
  -- the differences `(a - v, b - v)` along the orbit
  have hrec : ∀ m, Rel1 ((stepS^[m] (v, a, b)).2.1 - (stepS^[m] (v, a, b)).1)
      ((stepS^[m] (v, a, b)).2.2 - (stepS^[m] (v, a, b)).1)
      ((stepS^[m + 1] (v, a, b)).2.1 - (stepS^[m + 1] (v, a, b)).1)
      ((stepS^[m + 1] (v, a, b)).2.2 - (stepS^[m + 1] (v, a, b)).1) := by
    intro m
    rw [Function.iterate_succ_apply']
    exact stepS_rec (ht m) (hcl _ (ht m)).1
  have hzero := descent1 N.toNat
    (fun k => ((stepS^[i + k] (v, a, b)).2.1 - (stepS^[i + k] (v, a, b)).1,
      (stepS^[i + k] (v, a, b)).2.2 - (stepS^[i + k] (v, a, b)).1))
    (fun k => hrec (i + k)) (j - i) (by omega)
    (fun k => by
      show ((stepS^[i + (k + (j - i))] (v, a, b)).2.1 - (stepS^[i + (k + (j - i))] (v, a, b)).1,
        (stepS^[i + (k + (j - i))] (v, a, b)).2.2 - (stepS^[i + (k + (j - i))] (v, a, b)).1) = _
      rw [← Nat.add_assoc, hper k])
    (fun k => by
      have h1 := ht (i + k)
      have h2 := h1.le
      have h3 := h1.1
      have h4 := h1.2.1
      have h5 := h1.2.2.1
      show -((N.toNat : ℕ) : ℤ) ≤ _ ∧ _ ≤ ((N.toNat : ℕ) : ℤ) ∧ -((N.toNat : ℕ) : ℤ) ≤ _ ∧
        _ ≤ ((N.toNat : ℕ) : ℤ)
      omega) 0
  -- go back from index `i` to index `0`
  have hback : ∀ m, (stepS^[m] (v, a, b)).2.1 - (stepS^[m] (v, a, b)).1 = 0 ∧
      (stepS^[m] (v, a, b)).2.2 - (stepS^[m] (v, a, b)).1 = 0 →
      a - v = 0 ∧ b - v = 0 := by
    intro m
    induction m with
    | zero => exact fun hm => hm
    | succ m ih =>
      intro hm
      apply ih
      obtain ⟨r1, r2⟩ := hrec m
      omega
  have h0 := hback i ⟨congrArg Prod.fst hzero, congrArg Prod.snd hzero⟩
  exact hnd ⟨by omega, by omega⟩

/-! ## Theorem 3.3 -/

/-- `(u, v, w)` is a solution of `3u² + v² + w² = N` in odd positive integers with `3 ∤ vw`. -/
def IsT (N u v w : ℤ) : Prop :=
  0 < u ∧ 0 < v ∧ 0 < w ∧ u % 2 = 1 ∧ v % 2 = 1 ∧ w % 2 = 1 ∧ v % 3 ≠ 0 ∧ w % 3 ≠ 0 ∧
    3 * u ^ 2 + v ^ 2 + w ^ 2 = N

theorem IsT.le {N u v w : ℤ} (h : IsT N u v w) : u ≤ N ∧ v ≤ N ∧ w ≤ N := by
  obtain ⟨hu0, hv0, hw0, -, -, -, -, -, heq⟩ := h
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

theorem IsT.swap {N u v w : ℤ} (h : IsT N u v w) : IsT N u w v := by
  obtain ⟨hu0, hv0, hw0, hu, hv, hw, hv3, hw3, heq⟩ := h
  exact ⟨hu0, hw0, hv0, hu, hw, hv, hw3, hv3, by linarith⟩

theorem IsT.moveA {N u v w : ℤ} (h : IsT N u v w) (hvw : v % 3 = w % 3) :
    (∃ u' v' w', IsT N u' v' w' ∧ v' % 3 ≠ w' % 3) ∨
      IsT N ((u + v) / 2) ((3 * u - v) / 2) w := by
  obtain ⟨hu0, hv0, hw0, hu, hv, hw, hv3, hw3, heq⟩ := h
  obtain ⟨u', v', hu'0, hv'0, hu', hv', hv'3, hn, hcase⟩ := partner u v hu0 hv0 hu hv hv3
  have hT : IsT N u' v' w := ⟨hu'0, hv'0, hw0, hu', hv', hw, hv'3, hw3, by linarith⟩
  rcases hcase with hne | ⟨_, h1, h2⟩
  · exact Or.inl ⟨u', v', w, hT, by omega⟩
  · right
    have e1 : (u + v) / 2 = u' := by omega
    have e2 : (3 * u - v) / 2 = v' := by omega
    rw [e1, e2]
    exact hT

theorem IsT.moveB {N u v w : ℤ} (h : IsT N u v w) (hvw : v % 3 = w % 3) :
    (∃ u' v' w', IsT N u' v' w' ∧ v' % 3 ≠ w' % 3) ∨
      IsT N ((u + w) / 2) v ((3 * u - w) / 2) := by
  rcases h.swap.moveA hvw.symm with ⟨u', v', w', h', hne⟩ | h'
  · exact Or.inl ⟨u', w', v', h'.swap, fun e => hne e.symm⟩
  · exact Or.inr h'.swap

/-- The map `R = BA` on triples `(u, v, w)`. -/
def stepT (s : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  (((s.1 + s.2.1) / 2 + s.2.2) / 2, (3 * s.1 - s.2.1) / 2,
    (3 * ((s.1 + s.2.1) / 2) - s.2.2) / 2)

theorem stepT_rec {N : ℤ} {s : ℤ × ℤ × ℤ} (h : IsT N s.1 s.2.1 s.2.2)
    (hA : IsT N ((s.1 + s.2.1) / 2) ((3 * s.1 - s.2.1) / 2) s.2.2) :
    Rel2 (s.1 - s.2.1) (s.1 - s.2.2) ((stepT s).1 - (stepT s).2.1)
      ((stepT s).1 - (stepT s).2.2) := by
  obtain ⟨-, -, -, hu, hv, hw, -, -, -⟩ := h
  obtain ⟨-, -, -, hu1, -, -, -, -, -⟩ := hA
  simp only [stepT, Rel2]
  constructor <;> omega

/-- **Theorem 3.3.** If `3u² + v² + w² = N` has a solution in odd positive integers with
`3 ∤ vw` that is not diagonal, then it has such a solution with `v ≢ w (mod 3)`. -/
theorem exists_mixed {N u v w : ℤ} (h : IsT N u v w) (hnd : ¬(u = v ∧ v = w)) :
    ∃ u' v' w', IsT N u' v' w' ∧ v' % 3 ≠ w' % 3 := by
  by_contra hcon
  push Not at hcon
  have hcl : ∀ s : ℤ × ℤ × ℤ, IsT N s.1 s.2.1 s.2.2 →
      IsT N ((s.1 + s.2.1) / 2) ((3 * s.1 - s.2.1) / 2) s.2.2 ∧
      IsT N (stepT s).1 (stepT s).2.1 (stepT s).2.2 := by
    intro s hs
    have hA : IsT N ((s.1 + s.2.1) / 2) ((3 * s.1 - s.2.1) / 2) s.2.2 := by
      rcases hs.moveA (hcon _ _ _ hs) with ⟨u', v', w', h', hne⟩ | h'
      · exact absurd (hcon u' v' w' h') hne
      · exact h'
    refine ⟨hA, ?_⟩
    rcases hA.moveB (hcon _ _ _ hA) with ⟨u', v', w', h', hne⟩ | h'
    · exact absurd (hcon u' v' w' h') hne
    · exact h'
  have ht : ∀ j, IsT N (stepT^[j] (u, v, w)).1 (stepT^[j] (u, v, w)).2.1
      (stepT^[j] (u, v, w)).2.2 := by
    intro j
    induction j with
    | zero => exact h
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact (hcl _ ih).2
  have hbd : ∀ j, stepT^[j] (u, v, w) ∈ Set.Icc ((0, 0, 0) : ℤ × ℤ × ℤ) (N, N, N) := by
    intro j
    have h1 := ht j
    have h2 := h1.le
    exact ⟨⟨h1.1.le, h1.2.1.le, h1.2.2.1.le⟩, ⟨h2.1, h2.2.1, h2.2.2⟩⟩
  obtain ⟨i, j, hij, hEq⟩ := (Set.finite_Icc _ _).exists_lt_map_eq_of_forall_mem hbd
  have hper := iterate_periodic stepT (u, v, w) hij hEq
  have hrec : ∀ m, Rel2 ((stepT^[m] (u, v, w)).1 - (stepT^[m] (u, v, w)).2.1)
      ((stepT^[m] (u, v, w)).1 - (stepT^[m] (u, v, w)).2.2)
      ((stepT^[m + 1] (u, v, w)).1 - (stepT^[m + 1] (u, v, w)).2.1)
      ((stepT^[m + 1] (u, v, w)).1 - (stepT^[m + 1] (u, v, w)).2.2) := by
    intro m
    rw [Function.iterate_succ_apply']
    exact stepT_rec (ht m) (hcl _ (ht m)).1
  have hzero := descent2 N.toNat
    (fun k => ((stepT^[i + k] (u, v, w)).1 - (stepT^[i + k] (u, v, w)).2.1,
      (stepT^[i + k] (u, v, w)).1 - (stepT^[i + k] (u, v, w)).2.2))
    (fun k => hrec (i + k)) (j - i) (by omega)
    (fun k => by
      show ((stepT^[i + (k + (j - i))] (u, v, w)).1 - (stepT^[i + (k + (j - i))] (u, v, w)).2.1,
        (stepT^[i + (k + (j - i))] (u, v, w)).1 - (stepT^[i + (k + (j - i))] (u, v, w)).2.2) = _
      rw [← Nat.add_assoc, hper k])
    (fun k => by
      have h1 := ht (i + k)
      have h2 := h1.le
      have h3 := h1.1
      have h4 := h1.2.1
      have h5 := h1.2.2.1
      show -((N.toNat : ℕ) : ℤ) ≤ _ ∧ _ ≤ ((N.toNat : ℕ) : ℤ) ∧ -((N.toNat : ℕ) : ℤ) ≤ _ ∧
        _ ≤ ((N.toNat : ℕ) : ℤ)
      omega) 0
  have hback : ∀ m, (stepT^[m] (u, v, w)).1 - (stepT^[m] (u, v, w)).2.1 = 0 ∧
      (stepT^[m] (u, v, w)).1 - (stepT^[m] (u, v, w)).2.2 = 0 →
      u - v = 0 ∧ u - w = 0 := by
    intro m
    induction m with
    | zero => exact fun hm => hm
    | succ m ih =>
      intro hm
      apply ih
      obtain ⟨r1, r2⟩ := hrec m
      omega
  have h0 := hback i ⟨congrArg Prod.fst hzero, congrArg Prod.snd hzero⟩
  exact hnd ⟨by omega, by omega⟩

/-! ## Squares modulo 8 and 3 -/

theorem sq_mod8 (x : ℤ) : (x % 2 = 1 ∧ x ^ 2 % 8 = 1) ∨ (x % 4 = 0 ∧ x ^ 2 % 8 = 0) ∨
    (x % 4 = 2 ∧ x ^ 2 % 8 = 4) := by
  have key : x ^ 2 % 8 = x % 8 * (x % 8) % 8 := by rw [pow_two]; exact Int.mul_emod x x 8
  have h8 : x % 8 = 0 ∨ x % 8 = 1 ∨ x % 8 = 2 ∨ x % 8 = 3 ∨ x % 8 = 4 ∨ x % 8 = 5 ∨ x % 8 = 6 ∨
      x % 8 = 7 := by omega
  rcases h8 with h | h | h | h | h | h | h | h <;> rw [h] at key <;> norm_num at key <;> omega

theorem sq_mod3 (x : ℤ) : (x % 3 = 0 ∧ x ^ 2 % 3 = 0) ∨ (x % 3 ≠ 0 ∧ x ^ 2 % 3 = 1) := by
  have key : x ^ 2 % 3 = x % 3 * (x % 3) % 3 := by rw [pow_two]; exact Int.mul_emod x x 3
  have h3 : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 := by omega
  rcases h3 with h | h | h <;> rw [h] at key <;> norm_num at key <;> omega

/-! ## Starting points (Lemma 4.2) -/

theorem IsS.swap {N v a b : ℤ} (h : IsS N v a b) : IsS N v b a := by
  obtain ⟨hv0, ha0, hb0, hv, ha, hb, hv3, heq⟩ := h
  exact ⟨hv0, hb0, ha0, hv, hb, ha, hv3, by linarith⟩

theorem mod3_S {N v a b : ℤ} (heq : v ^ 2 + 3 * a ^ 2 + 3 * b ^ 2 = N) (hN : N % 3 = 1) :
    v % 3 ≠ 0 := by
  rcases sq_mod3 v with ⟨h, h2⟩ | ⟨h, h2⟩
  · omega
  · exact h

theorem mod3_T {N u v w : ℤ} (heq : 3 * u ^ 2 + v ^ 2 + w ^ 2 = N) (hN : N % 3 = 2) :
    v % 3 ≠ 0 ∧ w % 3 ≠ 0 := by
  rcases sq_mod3 v with ⟨h, h2⟩ | ⟨h, h2⟩ <;> rcases sq_mod3 w with ⟨h', h2'⟩ | ⟨h', h2'⟩ <;>
    omega

/-- Case 2 of Lemma 4.2(a): from a solution with `V`, `B` even to a solution in odd numbers. -/
theorem seedS_even {N V A B : ℤ} (hN3 : N % 3 = 1) (hV : 0 ≤ V) (hB : 0 ≤ B) (hA0 : 0 < A)
    (heq : V ^ 2 + 3 * A ^ 2 + 3 * B ^ 2 = N) (hA1 : A % 2 = 1) (hV0 : V % 2 = 0)
    (hB0 : B % 2 = 0) (h4 : (V + B) % 4 = 2) :
    ∃ v₁ b₁ : ℤ, IsS N v₁ A b₁ ∧ (v₁ = A ∧ A = b₁ → B = 0 ∧ V = 2 * A) := by
  obtain ⟨v₁, h2⟩ : ∃ v₁ : ℤ, 2 * v₁ = 3 * B + V := ⟨(3 * B + V) / 2, by omega⟩
  rcases lt_or_gt_of_ne (show B ≠ V by omega) with hlt | hgt
  · obtain ⟨b₁, h1⟩ : ∃ b₁ : ℤ, 2 * b₁ = V - B := ⟨(V - B) / 2, by omega⟩
    have hn := normIII' h1 h2
    have heq' : v₁ ^ 2 + 3 * A ^ 2 + 3 * b₁ ^ 2 = N := by linarith
    refine ⟨v₁, b₁, ⟨by omega, hA0, by omega, by omega, hA1, by omega, mod3_S heq' hN3, heq'⟩, ?_⟩
    rintro ⟨e1, e2⟩
    constructor <;> omega
  · obtain ⟨b₁, h1⟩ : ∃ b₁ : ℤ, 2 * b₁ = B - V := ⟨(B - V) / 2, by omega⟩
    have hn := normIII h1 h2
    have heq' : v₁ ^ 2 + 3 * A ^ 2 + 3 * b₁ ^ 2 = N := by linarith
    refine ⟨v₁, b₁, ⟨by omega, hA0, by omega, by omega, hA1, by omega, mod3_S heq' hN3, heq'⟩, ?_⟩
    rintro ⟨e1, e2⟩
    constructor <;> omega

/-- **Lemma 4.2(a).** A primitive solution of `v² + 3a² + 3b² = N`, `N ≡ 7 (mod 24)`, `N > 7`,
gives a solution in odd positive integers that is not diagonal. -/
theorem seedS {N : ℤ} (hN : N % 24 = 7) (hN7 : 7 < N) {v a b : ℤ}
    (heq : v ^ 2 + 3 * a ^ 2 + 3 * b ^ 2 = N) (hprim : Int.gcd (Int.gcd v a) b = 1) :
    ∃ v' a' b', IsS N v' a' b' ∧ ¬(v' = a' ∧ a' = b') := by
  have hdiv : ∀ k : ℤ, 0 < k → k ∣ v → k ∣ a → k ∣ b → k = 1 := by
    intro k hk h1 h2 h3
    have h12 : k ∣ ((Int.gcd v a : ℕ) : ℤ) := Int.dvd_coe_gcd h1 h2
    have h123 : k ∣ ((Int.gcd (Int.gcd v a) b : ℕ) : ℤ) := Int.dvd_coe_gcd h12 h3
    rw [hprim] at h123
    exact Int.eq_one_of_dvd_one hk.le (by simpa using h123)
  obtain ⟨V, hVd⟩ : ∃ V : ℤ, V = |v| := ⟨_, rfl⟩
  obtain ⟨A, hAd⟩ : ∃ A : ℤ, A = |a| := ⟨_, rfl⟩
  obtain ⟨B, hBd⟩ : ∃ B : ℤ, B = |b| := ⟨_, rfl⟩
  have hV : 0 ≤ V := hVd ▸ abs_nonneg v
  have hA : 0 ≤ A := hAd ▸ abs_nonneg a
  have hB : 0 ≤ B := hBd ▸ abs_nonneg b
  have hdvV : ∀ k : ℤ, k ∣ V → k ∣ v := fun k h => (dvd_abs k v).mp (hVd ▸ h)
  have hdvA : ∀ k : ℤ, k ∣ A → k ∣ a := fun k h => (dvd_abs k a).mp (hAd ▸ h)
  have hdvB : ∀ k : ℤ, k ∣ B → k ∣ b := fun k h => (dvd_abs k b).mp (hBd ▸ h)
  have heq' : V ^ 2 + 3 * A ^ 2 + 3 * B ^ 2 = N := by
    rw [hVd, hAd, hBd, sq_abs, sq_abs, sq_abs]; exact heq
  have hN3 : N % 3 = 1 := by omega
  have pattern : (V % 2 = 1 ∧ A % 2 = 1 ∧ B % 2 = 1) ∨
      (A % 2 = 1 ∧ V % 2 = 0 ∧ B % 2 = 0 ∧ (V + B) % 4 = 2) ∨
      (B % 2 = 1 ∧ V % 2 = 0 ∧ A % 2 = 0 ∧ (V + A) % 4 = 2) := by
    rcases sq_mod8 V with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;>
    rcases sq_mod8 A with ⟨h2, h2'⟩ | ⟨h2, h2'⟩ | ⟨h2, h2'⟩ <;>
    rcases sq_mod8 B with ⟨h3, h3'⟩ | ⟨h3, h3'⟩ | ⟨h3, h3'⟩ <;> omega
  rcases pattern with ⟨h1, h2, h3⟩ | ⟨h2, h1, h3, h4⟩ | ⟨h3, h1, h2, h4⟩
  · refine ⟨V, A, B, ⟨by omega, by omega, by omega, h1, h2, h3, mod3_S heq' hN3, heq'⟩, ?_⟩
    rintro ⟨e1, e2⟩
    have hk : V = 1 := hdiv V (by omega) (hdvV V dvd_rfl) (hdvA V ⟨1, by omega⟩)
      (hdvB V ⟨1, by omega⟩)
    have hA1 : A = 1 := by omega
    have hB1 : B = 1 := by omega
    rw [hk, hA1, hB1] at heq'
    norm_num at heq'
    omega
  · obtain ⟨v₁, b₁, hS, hd⟩ := seedS_even hN3 hV hB (by omega : 0 < A) heq' h2 h1 h3 h4
    refine ⟨v₁, A, b₁, hS, ?_⟩
    intro hdiag
    obtain ⟨hB0, hV2⟩ := hd hdiag
    have hk : A = 1 := hdiv A (by omega) (hdvV A ⟨2, by omega⟩) (hdvA A dvd_rfl)
      (hdvB A ⟨0, by omega⟩)
    have hV2' : V = 2 := by omega
    rw [hV2', hk, hB0] at heq'
    norm_num at heq'
    omega
  · have heq'' : V ^ 2 + 3 * B ^ 2 + 3 * A ^ 2 = N := by linarith
    obtain ⟨v₁, a₁, hS, hd⟩ := seedS_even hN3 hV hA (by omega : 0 < B) heq'' h3 h1 h2 h4
    refine ⟨v₁, a₁, B, hS.swap, ?_⟩
    rintro ⟨e1, e2⟩
    obtain ⟨hA0, hV2⟩ := hd ⟨by omega, by omega⟩
    have hk : B = 1 := hdiv B (by omega) (hdvV B ⟨2, by omega⟩) (hdvA B ⟨0, by omega⟩)
      (hdvB B dvd_rfl)
    have hV2' : V = 2 := by omega
    rw [hV2', hk, hA0] at heq'
    norm_num at heq'
    omega

/-- Case 2 of Lemma 4.2(b). -/
theorem seedT_even {N U V W : ℤ} (hN3 : N % 3 = 2) (hU : 0 ≤ U) (hV : 0 ≤ V) (hW0 : 0 < W)
    (heq : 3 * U ^ 2 + V ^ 2 + W ^ 2 = N) (hW1 : W % 2 = 1) (hU0 : U % 2 = 0)
    (hV0 : V % 2 = 0) (h4 : (U + V) % 4 = 2) :
    ∃ u₁ v₁ : ℤ, IsT N u₁ v₁ W ∧ (u₁ = v₁ ∧ v₁ = W → U = 0 ∧ V = 2 * W) := by
  obtain ⟨v₁, h2⟩ : ∃ v₁ : ℤ, 2 * v₁ = 3 * U + V := ⟨(3 * U + V) / 2, by omega⟩
  rcases lt_or_gt_of_ne (show U ≠ V by omega) with hlt | hgt
  · obtain ⟨u₁, h1⟩ : ∃ u₁ : ℤ, 2 * u₁ = V - U := ⟨(V - U) / 2, by omega⟩
    have hn := normIII' h1 h2
    have heq' : 3 * u₁ ^ 2 + v₁ ^ 2 + W ^ 2 = N := by linarith
    have h3 := mod3_T heq' hN3
    refine ⟨u₁, v₁, ⟨by omega, by omega, hW0, by omega, by omega, hW1, h3.1, h3.2, heq'⟩, ?_⟩
    rintro ⟨e1, e2⟩
    constructor <;> omega
  · obtain ⟨u₁, h1⟩ : ∃ u₁ : ℤ, 2 * u₁ = U - V := ⟨(U - V) / 2, by omega⟩
    have hn := normIII h1 h2
    have heq' : 3 * u₁ ^ 2 + v₁ ^ 2 + W ^ 2 = N := by linarith
    have h3 := mod3_T heq' hN3
    refine ⟨u₁, v₁, ⟨by omega, by omega, hW0, by omega, by omega, hW1, h3.1, h3.2, heq'⟩, ?_⟩
    rintro ⟨e1, e2⟩
    constructor <;> omega

/-- **Lemma 4.2(b).** A primitive solution of `3u² + v² + w² = N`, `N ≡ 5 (mod 24)`, `N > 5`,
gives a solution in odd positive integers that is not diagonal. -/
theorem seedT {N : ℤ} (hN : N % 24 = 5) (hN5 : 5 < N) {u v w : ℤ}
    (heq : 3 * u ^ 2 + v ^ 2 + w ^ 2 = N) (hprim : Int.gcd (Int.gcd u v) w = 1) :
    ∃ u' v' w', IsT N u' v' w' ∧ ¬(u' = v' ∧ v' = w') := by
  have hdiv : ∀ k : ℤ, 0 < k → k ∣ u → k ∣ v → k ∣ w → k = 1 := by
    intro k hk h1 h2 h3
    have h12 : k ∣ ((Int.gcd u v : ℕ) : ℤ) := Int.dvd_coe_gcd h1 h2
    have h123 : k ∣ ((Int.gcd (Int.gcd u v) w : ℕ) : ℤ) := Int.dvd_coe_gcd h12 h3
    rw [hprim] at h123
    exact Int.eq_one_of_dvd_one hk.le (by simpa using h123)
  obtain ⟨U, hUd⟩ : ∃ U : ℤ, U = |u| := ⟨_, rfl⟩
  obtain ⟨V, hVd⟩ : ∃ V : ℤ, V = |v| := ⟨_, rfl⟩
  obtain ⟨W, hWd⟩ : ∃ W : ℤ, W = |w| := ⟨_, rfl⟩
  have hU : 0 ≤ U := hUd ▸ abs_nonneg u
  have hV : 0 ≤ V := hVd ▸ abs_nonneg v
  have hW : 0 ≤ W := hWd ▸ abs_nonneg w
  have hdvU : ∀ k : ℤ, k ∣ U → k ∣ u := fun k h => (dvd_abs k u).mp (hUd ▸ h)
  have hdvV : ∀ k : ℤ, k ∣ V → k ∣ v := fun k h => (dvd_abs k v).mp (hVd ▸ h)
  have hdvW : ∀ k : ℤ, k ∣ W → k ∣ w := fun k h => (dvd_abs k w).mp (hWd ▸ h)
  have heq' : 3 * U ^ 2 + V ^ 2 + W ^ 2 = N := by
    rw [hUd, hVd, hWd, sq_abs, sq_abs, sq_abs]; exact heq
  have hN3 : N % 3 = 2 := by omega
  have pattern : (U % 2 = 1 ∧ V % 2 = 1 ∧ W % 2 = 1) ∨
      (W % 2 = 1 ∧ U % 2 = 0 ∧ V % 2 = 0 ∧ (U + V) % 4 = 2) ∨
      (V % 2 = 1 ∧ U % 2 = 0 ∧ W % 2 = 0 ∧ (U + W) % 4 = 2) := by
    rcases sq_mod8 U with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;>
    rcases sq_mod8 V with ⟨h2, h2'⟩ | ⟨h2, h2'⟩ | ⟨h2, h2'⟩ <;>
    rcases sq_mod8 W with ⟨h3, h3'⟩ | ⟨h3, h3'⟩ | ⟨h3, h3'⟩ <;> omega
  rcases pattern with ⟨h1, h2, h3⟩ | ⟨h3, h1, h2, h4⟩ | ⟨h2, h1, h3, h4⟩
  · have hm := mod3_T heq' hN3
    refine ⟨U, V, W, ⟨by omega, by omega, by omega, h1, h2, h3, hm.1, hm.2, heq'⟩, ?_⟩
    rintro ⟨e1, e2⟩
    have hk : U = 1 := hdiv U (by omega) (hdvU U dvd_rfl) (hdvV U ⟨1, by omega⟩)
      (hdvW U ⟨1, by omega⟩)
    have hV1 : V = 1 := by omega
    have hW1 : W = 1 := by omega
    rw [hk, hV1, hW1] at heq'
    norm_num at heq'
    omega
  · obtain ⟨u₁, v₁, hT, hd⟩ := seedT_even hN3 hU hV (by omega : 0 < W) heq' h3 h1 h2 h4
    refine ⟨u₁, v₁, W, hT, ?_⟩
    intro hdiag
    obtain ⟨hU0, hV2⟩ := hd hdiag
    have hk : W = 1 := hdiv W (by omega) (hdvU W ⟨0, by omega⟩) (hdvV W ⟨2, by omega⟩)
      (hdvW W dvd_rfl)
    have hV2' : V = 2 := by omega
    rw [hU0, hV2', hk] at heq'
    norm_num at heq'
    omega
  · have heq'' : 3 * U ^ 2 + W ^ 2 + V ^ 2 = N := by linarith
    obtain ⟨u₁, w₁, hT, hd⟩ := seedT_even hN3 hU hW (by omega : 0 < V) heq'' h2 h1 h3 h4
    refine ⟨u₁, V, w₁, hT.swap, ?_⟩
    rintro ⟨e1, e2⟩
    obtain ⟨hU0, hW2⟩ := hd ⟨by omega, by omega⟩
    have hk : V = 1 := hdiv V (by omega) (hdvU V ⟨0, by omega⟩) (hdvV V dvd_rfl)
      (hdvW V ⟨2, by omega⟩)
    have hW2' : W = 2 := by omega
    rw [hU0, hk, hW2'] at heq'
    norm_num at heq'
    omega

/-! ## The classical input (Proposition 4.1), as hypotheses -/

/-- Proposition 4.1(a): every `N ≡ 7 (mod 24)` is primitively represented by
`v² + 3a² + 3b²`. This follows from the classical theory of genera; it is not proved here. -/
def PrimRep133 : Prop :=
  ∀ N : ℤ, 0 < N → N % 24 = 7 →
    ∃ v a b : ℤ, v ^ 2 + 3 * a ^ 2 + 3 * b ^ 2 = N ∧ Int.gcd (Int.gcd v a) b = 1

/-- Proposition 4.1(b): every `N ≡ 5 (mod 24)` is primitively represented by
`3u² + v² + w²`. This follows from the classical theory of genera; it is not proved here. -/
def PrimRep113 : Prop :=
  ∀ N : ℤ, 0 < N → N % 24 = 5 →
    ∃ u v w : ℤ, 3 * u ^ 2 + v ^ 2 + w ^ 2 = N ∧ Int.gcd (Int.gcd u v) w = 1

/-- For `N ≡ 7 (mod 24)`, `N > 7`, both residues of `v` mod 3 occur. -/
theorem exists_S_residue (hP : PrimRep133) {N : ℤ} (hN : N % 24 = 7) (hN7 : 7 < N) (c : ℤ)
    (hc : c = 1 ∨ c = 2) : ∃ v a b, IsS N v a b ∧ v % 3 = c := by
  obtain ⟨v, a, b, heq, hprim⟩ := hP N (by omega) hN
  obtain ⟨v', a', b', hS, hnd⟩ := seedS hN hN7 heq hprim
  by_cases hv : v' % 3 = c
  · exact ⟨v', a', b', hS, hv⟩
  · obtain ⟨v'', a'', b'', hS', hne⟩ := exists_other_residue hS hnd
    refine ⟨v'', a'', b'', hS', ?_⟩
    have h1 := hS.2.2.2.2.2.2.1
    have h2 := hS'.2.2.2.2.2.2.1
    omega

/-- For `N ≡ 5 (mod 24)`, `N > 5`, there is a solution with `v ≡ 2`, `w ≡ 1 (mod 3)`. -/
theorem exists_T_mixed (hP : PrimRep113) {N : ℤ} (hN : N % 24 = 5) (hN5 : 5 < N) :
    ∃ u v w, IsT N u v w ∧ v % 3 = 2 ∧ w % 3 = 1 := by
  obtain ⟨u, v, w, heq, hprim⟩ := hP N (by omega) hN
  obtain ⟨u', v', w', hT, hnd⟩ := seedT hN hN5 heq hprim
  obtain ⟨u'', v'', w'', hT', hne⟩ := exists_mixed hT hnd
  have h1 := hT'.2.2.2.2.2.2.1
  have h2 := hT'.2.2.2.2.2.2.2.1
  by_cases hv : v'' % 3 = 2
  · exact ⟨u'', v'', w'', hT', hv, by omega⟩
  · exact ⟨u'', w'', v'', hT'.swap, by omega, by omega⟩

/-! ## From solutions to representations (Lemma 5.1) -/

theorem even_pent (z : ℕ) : Even (z * (3 * z - 1)) := by
  rcases Nat.even_or_odd z with h | h
  · exact Nat.even_mul.mpr (Or.inl h)
  · refine Nat.even_mul.mpr (Or.inr ?_)
    obtain ⟨k, rfl⟩ := h
    exact ⟨3 * k + 1, by omega⟩

theorem even_pent' (z : ℕ) : Even (z * (3 * z + 1)) := by
  rcases Nat.even_or_odd z with h | h
  · exact Nat.even_mul.mpr (Or.inl h)
  · refine Nat.even_mul.mpr (Or.inr ?_)
    obtain ⟨k, rfl⟩ := h
    exact ⟨3 * k + 2, by omega⟩

theorem repr_class2 (n : ℕ) {v a b : ℤ} (h : IsS (24 * n + 7) v a b) (hv : v % 3 = 2) :
    ∃ x y z : ℕ, 1 ≤ z ∧ n = x * (x + 1) / 2 + y * (y + 1) / 2 + z * (3 * z - 1) / 2 := by
  obtain ⟨hv0, ha0, hb0, hv2, ha2, hb2, -, heq⟩ := h
  obtain ⟨x, hx⟩ : ∃ x : ℕ, a = 2 * x + 1 := ⟨((a - 1) / 2).toNat, by omega⟩
  obtain ⟨y, hy⟩ : ∃ y : ℕ, b = 2 * y + 1 := ⟨((b - 1) / 2).toNat, by omega⟩
  obtain ⟨z, hz⟩ : ∃ z : ℕ, v = 6 * z - 1 := ⟨((v + 1) / 6).toNat, by omega⟩
  have hz1 : 1 ≤ z := by omega
  subst hx hy hz
  have h24 : (24 : ℤ) * n = 12 * (x * (x + 1)) + 12 * (y * (y + 1)) + 12 * (z * (3 * z - 1)) := by
    linear_combination (-1 : ℤ) * heq
  have hN : 2 * n = x * (x + 1) + y * (y + 1) + z * (3 * z - 1) := by
    zify [show 1 ≤ 3 * z by omega]
    linarith
  obtain ⟨X, hX⟩ := Nat.even_mul_succ_self x
  obtain ⟨Y, hY⟩ := Nat.even_mul_succ_self y
  obtain ⟨Z, hZ⟩ := even_pent z
  refine ⟨x, y, z, hz1, ?_⟩
  rw [hX, hY, hZ] at hN ⊢
  omega

theorem repr_class1 (n : ℕ) {v a b : ℤ} (h : IsS (24 * n + 7) v a b) (hv : v % 3 = 1) :
    ∃ x y z : ℕ, n = x * (x + 1) / 2 + y * (y + 1) / 2 + z * (3 * z + 1) / 2 := by
  obtain ⟨hv0, ha0, hb0, hv2, ha2, hb2, -, heq⟩ := h
  obtain ⟨x, hx⟩ : ∃ x : ℕ, a = 2 * x + 1 := ⟨((a - 1) / 2).toNat, by omega⟩
  obtain ⟨y, hy⟩ : ∃ y : ℕ, b = 2 * y + 1 := ⟨((b - 1) / 2).toNat, by omega⟩
  obtain ⟨z, hz⟩ : ∃ z : ℕ, v = 6 * z + 1 := ⟨((v - 1) / 6).toNat, by omega⟩
  subst hx hy hz
  have h24 : (24 : ℤ) * n = 12 * (x * (x + 1)) + 12 * (y * (y + 1)) + 12 * (z * (3 * z + 1)) := by
    linear_combination (-1 : ℤ) * heq
  have hN : 2 * n = x * (x + 1) + y * (y + 1) + z * (3 * z + 1) := by
    zify
    linarith
  obtain ⟨X, hX⟩ := Nat.even_mul_succ_self x
  obtain ⟨Y, hY⟩ := Nat.even_mul_succ_self y
  obtain ⟨Z, hZ⟩ := even_pent' z
  refine ⟨x, y, z, ?_⟩
  rw [hX, hY, hZ] at hN ⊢
  omega

theorem repr_mixed (n : ℕ) {u v w : ℤ} (h : IsT (24 * n + 5) u v w) (hv : v % 3 = 2)
    (hw : w % 3 = 1) :
    ∃ x y z : ℕ, 1 ≤ y ∧ n = x * (x + 1) / 2 + y * (3 * y - 1) / 2 + z * (3 * z + 1) / 2 := by
  obtain ⟨hu0, hv0, hw0, hu2, hv2, hw2, -, -, heq⟩ := h
  obtain ⟨x, hx⟩ : ∃ x : ℕ, u = 2 * x + 1 := ⟨((u - 1) / 2).toNat, by omega⟩
  obtain ⟨y, hy⟩ : ∃ y : ℕ, v = 6 * y - 1 := ⟨((v + 1) / 6).toNat, by omega⟩
  obtain ⟨z, hz⟩ : ∃ z : ℕ, w = 6 * z + 1 := ⟨((w - 1) / 6).toNat, by omega⟩
  have hy1 : 1 ≤ y := by omega
  subst hx hy hz
  have h24 : (24 : ℤ) * n = 12 * (x * (x + 1)) + 12 * (y * (3 * y - 1)) + 12 * (z * (3 * z + 1)) := by
    linear_combination (-1 : ℤ) * heq
  have hN : 2 * n = x * (x + 1) + y * (3 * y - 1) + z * (3 * z + 1) := by
    zify [show 1 ≤ 3 * y by omega]
    linarith
  obtain ⟨X, hX⟩ := Nat.even_mul_succ_self x
  obtain ⟨Y, hY⟩ := even_pent y
  obtain ⟨Z, hZ⟩ := even_pent' z
  refine ⟨x, y, z, hy1, ?_⟩
  rw [hX, hY, hZ] at hN ⊢
  omega

/-! ## Main theorems -/

/-- **Theorem 1.1.** Every natural number is a sum of two triangular numbers and a pentagonal
number, `n = x(x+1)/2 + y(y+1)/2 + z(3z-1)/2` with `x y z : ℕ`; if `n ≥ 1` one can take `z ≥ 1`. -/
theorem two_triangular_pentagonal (hP : PrimRep133) (n : ℕ) :
    ∃ x y z : ℕ, n = x * (x + 1) / 2 + y * (y + 1) / 2 + z * (3 * z - 1) / 2 ∧
      (1 ≤ n → 1 ≤ z) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨0, 0, 0, by norm_num, by omega⟩
  · obtain ⟨v, a, b, hS, hv⟩ :=
      exists_S_residue hP (N := 24 * n + 7) (by omega) (by omega) 2 (Or.inr rfl)
    obtain ⟨x, y, z, hz, h⟩ := repr_class2 n hS hv
    exact ⟨x, y, z, h, fun _ => hz⟩

/-- Every natural number is `x(x+1)/2 + y(y+1)/2 + z(3z+1)/2` with `x y z : ℕ`
(the tuple `(3,1,1,1,1,1)`). -/
theorem two_triangular_second_pentagonal (hP : PrimRep133) (n : ℕ) :
    ∃ x y z : ℕ, n = x * (x + 1) / 2 + y * (y + 1) / 2 + z * (3 * z + 1) / 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨0, 0, 0, by norm_num⟩
  · obtain ⟨v, a, b, hS, hv⟩ :=
      exists_S_residue hP (N := 24 * n + 7) (by omega) (by omega) 1 (Or.inl rfl)
    exact repr_class1 n hS hv

/-- **Theorem 1.4.** Every natural number is `x(x+1)/2 + y(3y-1)/2 + z(3z+1)/2` with
`x y z : ℕ`; if `n ≥ 1` one can take `y ≥ 1`. -/
theorem triangular_two_pentagonal_mixed (hP : PrimRep113) (n : ℕ) :
    ∃ x y z : ℕ, n = x * (x + 1) / 2 + y * (3 * y - 1) / 2 + z * (3 * z + 1) / 2 ∧
      (1 ≤ n → 1 ≤ y) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨0, 0, 0, by norm_num, by omega⟩
  · obtain ⟨u, v, w, hT, hv, hw⟩ := exists_T_mixed hP (N := 24 * n + 5) (by omega) (by omega)
    obtain ⟨x, y, z, hy, h⟩ := repr_mixed n hT hv hw
    exact ⟨x, y, z, h, fun _ => hy⟩

/-! ## Lower bounds on `a` (Lemma 3.6 and Proposition 5.2) -/

/-- Lemma 2.2 in cases II and III, with size information. -/
theorem partner_size (u v : ℤ) (hu0 : 0 < u) (hu : u % 2 = 1) (hv : v % 2 = 1)
    (hv3 : v % 3 ≠ 0) (hbig : 3 * u < v) :
    ∃ u' v' : ℤ, 0 < u' ∧ 0 < v' ∧ u' % 2 = 1 ∧ v' % 2 = 1 ∧ v' % 3 ≠ 0 ∧
      3 * u' ^ 2 + v' ^ 2 = 3 * u ^ 2 + v ^ 2 ∧ v' % 3 ≠ v % 3 ∧
      v - u ≤ 2 * u' ∧ v - 3 * u ≤ 2 * v' := by
  by_cases h4 : (u - v) % 4 = 0
  · obtain ⟨u', h1⟩ : ∃ u' : ℤ, 2 * u' = u + v := ⟨(u + v) / 2, by omega⟩
    obtain ⟨v', h2⟩ : ∃ v' : ℤ, 2 * v' = v - 3 * u := ⟨(v - 3 * u) / 2, by omega⟩
    exact ⟨u', v', by omega, by omega, by omega, by omega, by omega, normII h1 h2, by omega,
      by omega, by omega⟩
  · obtain ⟨u', h1⟩ : ∃ u' : ℤ, 2 * u' = v - u := ⟨(v - u) / 2, by omega⟩
    obtain ⟨v', h2⟩ : ∃ v' : ℤ, 2 * v' = 3 * u + v := ⟨(3 * u + v) / 2, by omega⟩
    exact ⟨u', v', by omega, by omega, by omega, by omega, by omega, normIII' h1 h2, by omega,
      by omega, by omega⟩

/-- **Lemma 3.6.** If `v > 3a + 6b`, two moves keep the residue of `v` and make `a` large. -/
theorem IsS.large {N v a b : ℤ} (h : IsS N v a b) (hbig : 3 * a + 6 * b < v) :
    ∃ v' a' b', IsS N v' a' b' ∧ v' % 3 = v % 3 ∧ v - a ≤ 2 * a' := by
  obtain ⟨hv0, ha0, hb0, hv, ha, hb, hv3, heq⟩ := h
  obtain ⟨a', v', ha'0, hv'0, ha', hv', hv'3, hn, hne, hsa, hsv⟩ :=
    partner_size a v ha0 ha hv hv3 (by omega)
  obtain ⟨b', v'', hb'0, hv''0, hb', hv'', hv''3, hn', hne', -, -⟩ :=
    partner_size b v' hb0 hb hv' hv'3 (by omega)
  exact ⟨v'', a', b', ⟨hv''0, ha'0, hb'0, hv'', ha', hb', hv''3, by linarith⟩, by omega, hsa⟩

/-- **Proposition 5.2**, in terms of solutions: for `d = 1` or `N > 87(d-2)²` there is a
solution with a prescribed residue of `v` and with `a ≥ d`. -/
theorem exists_S_bound (hP : PrimRep133) {N : ℤ} (hN : N % 24 = 7) (hN7 : 7 < N) (c : ℤ)
    (hc : c = 1 ∨ c = 2) (d : ℤ) (hd : d % 2 = 1) (hd1 : 1 ≤ d)
    (hbig : d = 1 ∨ 87 * (d - 2) ^ 2 < N) :
    ∃ v a b, IsS N v a b ∧ v % 3 = c ∧ d ≤ a := by
  obtain ⟨v, a, b, hS, hv⟩ := exists_S_residue hP hN hN7 c hc
  by_cases ha : d ≤ a
  · exact ⟨v, a, b, hS, hv, ha⟩
  by_cases hb : d ≤ b
  · exact ⟨v, b, a, hS.swap, hv, hb⟩
  have hv0 := hS.1
  have ha0 := hS.2.1
  have hb0 := hS.2.2.1
  have ha2 := hS.2.2.2.2.1
  have hb2 := hS.2.2.2.2.2.1
  have heq := hS.2.2.2.2.2.2.2
  have hbig' : 87 * (d - 2) ^ 2 < N := by
    rcases hbig with h | h
    · omega
    · exact h
  have haK : a ≤ d - 2 := by omega
  have hbK : b ≤ d - 2 := by omega
  have hv9 : 9 * (d - 2) < v := by
    by_contra hle
    have hle' : v ≤ 9 * (d - 2) := by omega
    have h1 : v ^ 2 ≤ (9 * (d - 2)) ^ 2 := by nlinarith
    have h2 : a ^ 2 ≤ (d - 2) ^ 2 := by nlinarith
    have h3 : b ^ 2 ≤ (d - 2) ^ 2 := by nlinarith
    nlinarith
  obtain ⟨v', a', b', hS', hv', hsz⟩ := hS.large (by omega)
  exact ⟨v', a', b', hS', by omega, by omega⟩

/-- The solutions needed for the three families, with `N = 24n + C + 3d²`, `C ∈ {4, 28}`. -/
theorem exists_state (hP : PrimRep133) (c : ℤ) (hc : c = 1 ∨ c = 2) (C : ℤ)
    (hC : C = 4 ∨ C = 28) (n d : ℕ) (hd : d % 2 = 1)
    (hN7 : 7 < 24 * (n : ℤ) + C + 3 * (d : ℤ) ^ 2)
    (hbig : d = 1 ∨ 87 * ((d : ℤ) - 2) ^ 2 < 24 * (n : ℤ) + C + 3 * (d : ℤ) ^ 2) :
    ∃ v a b, IsS (24 * (n : ℤ) + C + 3 * (d : ℤ) ^ 2) v a b ∧ v % 3 = c ∧ (d : ℤ) ≤ a := by
  have hsq := sq_mod8 (d : ℤ)
  have hN : (24 * (n : ℤ) + C + 3 * (d : ℤ) ^ 2) % 24 = 7 := by
    rcases hC with rfl | rfl <;> omega
  refine exists_S_bound hP hN hN7 c hc d (by omega) (by omega) ?_
  rcases hbig with h | h
  · left; exact_mod_cast h
  · right; exact h

/-! ## From solutions to representations, with the parameter `d` -/

theorem even_mul_add_odd (y d : ℕ) (hd : d % 2 = 1) : Even (y * (y + d)) := by
  rcases Nat.even_or_odd y with h | h
  · exact Nat.even_mul.mpr (Or.inl h)
  · refine Nat.even_mul.mpr (Or.inr ?_)
    obtain ⟨k, rfl⟩ := h
    exact ⟨k + (d + 1) / 2, by omega⟩

theorem even_35 (x : ℕ) : Even (x * (3 * x + 5)) := by
  rcases Nat.even_or_odd x with h | h
  · exact Nat.even_mul.mpr (Or.inl h)
  · refine Nat.even_mul.mpr (Or.inr ?_)
    obtain ⟨k, rfl⟩ := h
    exact ⟨3 * k + 4, by omega⟩

theorem repr_m1 (n d : ℕ) (hd : d % 2 = 1) {v a b : ℤ}
    (h : IsS (24 * (n : ℤ) + 4 + 3 * (d : ℤ) ^ 2) v a b) (hv : v % 3 = 2) (ha : (d : ℤ) ≤ a) :
    ∃ x y z : ℕ, n = x * (3 * x - 1) / 2 + y * (y + d) / 2 + z * (z + 1) / 2 := by
  obtain ⟨hv0, ha0, hb0, hv2, ha2, hb2, -, heq⟩ := h
  obtain ⟨x, hx⟩ : ∃ x : ℕ, v = 6 * x - 1 := ⟨((v + 1) / 6).toNat, by omega⟩
  obtain ⟨y, hy⟩ : ∃ y : ℕ, a = 2 * y + d := ⟨((a - d) / 2).toNat, by omega⟩
  obtain ⟨z, hz⟩ : ∃ z : ℕ, b = 2 * z + 1 := ⟨((b - 1) / 2).toNat, by omega⟩
  have hx1 : 1 ≤ x := by omega
  subst hx hy hz
  have h24 : (24 : ℤ) * n = 12 * (x * (3 * x - 1)) + 12 * (y * (y + d)) + 12 * (z * (z + 1)) := by
    linear_combination (-1 : ℤ) * heq
  have hN : 2 * n = x * (3 * x - 1) + y * (y + d) + z * (z + 1) := by
    zify [show 1 ≤ 3 * x by omega]
    linarith
  obtain ⟨X, hX⟩ := even_pent x
  obtain ⟨Y, hY⟩ := even_mul_add_odd y d hd
  obtain ⟨Z, hZ⟩ := Nat.even_mul_succ_self z
  refine ⟨x, y, z, ?_⟩
  rw [hX, hY, hZ] at hN ⊢
  omega

theorem repr_p1 (n d : ℕ) (hd : d % 2 = 1) {v a b : ℤ}
    (h : IsS (24 * (n : ℤ) + 4 + 3 * (d : ℤ) ^ 2) v a b) (hv : v % 3 = 1) (ha : (d : ℤ) ≤ a) :
    ∃ x y z : ℕ, n = x * (3 * x + 1) / 2 + y * (y + d) / 2 + z * (z + 1) / 2 := by
  obtain ⟨hv0, ha0, hb0, hv2, ha2, hb2, -, heq⟩ := h
  obtain ⟨x, hx⟩ : ∃ x : ℕ, v = 6 * x + 1 := ⟨((v - 1) / 6).toNat, by omega⟩
  obtain ⟨y, hy⟩ : ∃ y : ℕ, a = 2 * y + d := ⟨((a - d) / 2).toNat, by omega⟩
  obtain ⟨z, hz⟩ : ∃ z : ℕ, b = 2 * z + 1 := ⟨((b - 1) / 2).toNat, by omega⟩
  subst hx hy hz
  have h24 : (24 : ℤ) * n = 12 * (x * (3 * x + 1)) + 12 * (y * (y + d)) + 12 * (z * (z + 1)) := by
    linear_combination (-1 : ℤ) * heq
  have hN : 2 * n = x * (3 * x + 1) + y * (y + d) + z * (z + 1) := by
    zify
    linarith
  obtain ⟨X, hX⟩ := even_pent' x
  obtain ⟨Y, hY⟩ := even_mul_add_odd y d hd
  obtain ⟨Z, hZ⟩ := Nat.even_mul_succ_self z
  refine ⟨x, y, z, ?_⟩
  rw [hX, hY, hZ] at hN ⊢
  omega

theorem repr_p5 (n d : ℕ) (hd : d % 2 = 1) {v a b : ℤ}
    (h : IsS (24 * (n : ℤ) + 28 + 3 * (d : ℤ) ^ 2) v a b) (hv : v % 3 = 2) (ha : (d : ℤ) ≤ a) :
    ∃ x y z : ℕ, n = x * (3 * x + 5) / 2 + y * (y + d) / 2 + z * (z + 1) / 2 := by
  obtain ⟨hv0, ha0, hb0, hv2, ha2, hb2, -, heq⟩ := h
  obtain ⟨x, hx⟩ : ∃ x : ℕ, v = 6 * x + 5 := ⟨((v - 5) / 6).toNat, by omega⟩
  obtain ⟨y, hy⟩ : ∃ y : ℕ, a = 2 * y + d := ⟨((a - d) / 2).toNat, by omega⟩
  obtain ⟨z, hz⟩ : ∃ z : ℕ, b = 2 * z + 1 := ⟨((b - 1) / 2).toNat, by omega⟩
  subst hx hy hz
  have h24 : (24 : ℤ) * n = 12 * (x * (3 * x + 5)) + 12 * (y * (y + d)) + 12 * (z * (z + 1)) := by
    linear_combination (-1 : ℤ) * heq
  have hN : 2 * n = x * (3 * x + 5) + y * (y + d) + z * (z + 1) := by
    zify
    linarith
  obtain ⟨X, hX⟩ := even_35 x
  obtain ⟨Y, hY⟩ := even_mul_add_odd y d hd
  obtain ⟨Z, hZ⟩ := Nat.even_mul_succ_self z
  refine ⟨x, y, z, ?_⟩
  rw [hX, hY, hZ] at hN ⊢
  omega

/-! ## The finite range in the proof of Theorem 1.2: explicit representations -/

/-- `chkFrom f d k L`: the `i`-th entry `(x, y, z)` of `L` satisfies
`f x + y(y+d)/2 + z(z+1)/2 = k + i`. -/
def chkFrom (f : ℕ → ℕ) (d : ℕ) : ℕ → List (ℕ × ℕ × ℕ) → Bool
  | _, [] => true
  | k, t :: L => (f t.1 + t.2.1 * (t.2.1 + d) / 2 + t.2.2 * (t.2.2 + 1) / 2 == k) &&
      chkFrom f d (k + 1) L

theorem of_chkFrom (f : ℕ → ℕ) (d : ℕ) : ∀ (L : List (ℕ × ℕ × ℕ)) (k : ℕ),
    chkFrom f d k L = true → ∀ n, k ≤ n → n < k + L.length →
    ∃ x y z : ℕ, n = f x + y * (y + d) / 2 + z * (z + 1) / 2
  | [], k, _, n, h1, h2 => by simp at h2; omega
  | t :: L, k, h, n, h1, h2 => by
    simp only [chkFrom, Bool.and_eq_true, beq_iff_eq] at h
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · exact ⟨_, _, _, h.1.symm⟩
    · exact of_chkFrom f d L (k + 1) h.2 n hlt (by simp at h2; omega)

def L_m1_3 : List (ℕ × ℕ × ℕ) :=
  [(0, 0, 0), (0, 0, 1), (0, 1, 0)]

theorem cert_m1_3 (n : ℕ) (hn : n < 3) :
    ∃ x y z : ℕ, n = x * (3 * x - 1) / 2 + y * (y + 3) / 2 + z * (z + 1) / 2 :=
  of_chkFrom (fun x => x * (3 * x - 1) / 2) 3 L_m1_3 0 (by decide +kernel) n (Nat.zero_le n)
    (lt_of_lt_of_eq hn (by decide +kernel : 3 = 0 + L_m1_3.length))

def L_m1_5 : List (ℕ × ℕ × ℕ) :=
  [(0, 0, 0), (0, 0, 1), (1, 0, 1), (0, 0, 2), (0, 1, 1), (1, 1, 1), (0, 0, 3), (0, 2, 0),
   (0, 2, 1), (0, 1, 3), (0, 0, 4), (1, 0, 4), (0, 3, 0), (0, 1, 4), (1, 1, 4), (0, 0, 5),
   (1, 0, 5), (0, 2, 4), (0, 1, 5), (0, 4, 1), (1, 4, 1), (0, 0, 6), (0, 2, 5), (1, 2, 5),
   (0, 1, 6), (0, 5, 0), (0, 5, 1), (0, 3, 5), (0, 0, 7), (1, 0, 7)]

theorem cert_m1_5 (n : ℕ) (hn : n < 30) :
    ∃ x y z : ℕ, n = x * (3 * x - 1) / 2 + y * (y + 5) / 2 + z * (z + 1) / 2 :=
  of_chkFrom (fun x => x * (3 * x - 1) / 2) 5 L_m1_5 0 (by decide +kernel) n (Nat.zero_le n)
    (lt_of_lt_of_eq hn (by decide +kernel : 30 = 0 + L_m1_5.length))

def L_m1_7 : List (ℕ × ℕ × ℕ) :=
  [(0, 0, 0), (0, 0, 1), (1, 0, 1), (0, 0, 2), (0, 1, 0), (0, 1, 1), (0, 0, 3), (0, 1, 2),
   (1, 1, 2), (0, 2, 0), (0, 0, 4), (1, 0, 4), (0, 2, 2), (1, 2, 2), (0, 1, 4), (0, 0, 5),
   (0, 3, 1), (1, 3, 1), (0, 3, 2), (0, 1, 5), (1, 1, 5), (0, 0, 6), (0, 4, 0), (0, 4, 1),
   (0, 2, 5), (0, 1, 6), (1, 1, 6), (2, 4, 0), (0, 0, 7), (1, 0, 7), (0, 2, 6), (0, 5, 1),
   (0, 1, 7), (0, 5, 2), (1, 5, 2), (2, 2, 6), (0, 0, 8), (0, 2, 7), (1, 2, 7), (0, 6, 0),
   (0, 1, 8), (1, 1, 8), (0, 6, 2), (0, 3, 7), (1, 3, 7), (0, 0, 9), (1, 0, 9), (2, 6, 2),
   (2, 3, 7), (0, 1, 9), (0, 4, 7), (0, 3, 8), (0, 7, 2), (1, 7, 2), (0, 2, 9), (0, 0, 10),
   (1, 0, 10), (2, 7, 2), (0, 4, 8), (0, 1, 10), (0, 3, 9), (0, 8, 1), (1, 8, 1), (0, 8, 2),
   (0, 2, 10), (1, 2, 10), (0, 0, 11), (0, 4, 9), (1, 4, 9), (2, 2, 10), (0, 1, 11), (1, 1, 11),
   (0, 9, 0), (0, 9, 1), (1, 9, 1), (0, 2, 11), (1, 2, 11), (0, 4, 10), (0, 0, 12), (1, 0, 12),
   (2, 2, 11), (0, 3, 11), (0, 1, 12), (1, 1, 12), (0, 6, 9)]

theorem cert_m1_7 (n : ℕ) (hn : n < 85) :
    ∃ x y z : ℕ, n = x * (3 * x - 1) / 2 + y * (y + 7) / 2 + z * (z + 1) / 2 :=
  of_chkFrom (fun x => x * (3 * x - 1) / 2) 7 L_m1_7 0 (by decide +kernel) n (Nat.zero_le n)
    (lt_of_lt_of_eq hn (by decide +kernel : 85 = 0 + L_m1_7.length))

def L_m1_9 : List (ℕ × ℕ × ℕ) :=
  [(0, 0, 0), (0, 0, 1), (1, 0, 1), (0, 0, 2), (1, 0, 2), (0, 1, 0), (0, 0, 3), (1, 0, 3),
   (0, 1, 2), (1, 1, 2), (0, 0, 4), (0, 1, 3), (0, 2, 1), (1, 2, 1), (0, 2, 2), (0, 0, 5),
   (1, 0, 5), (0, 2, 3), (0, 3, 0), (0, 3, 1), (0, 1, 5), (0, 0, 6), (1, 0, 6), (2, 3, 0),
   (0, 3, 3), (1, 3, 3), (0, 1, 6), (0, 4, 1), (0, 0, 7), (0, 4, 2), (1, 4, 2), (2, 1, 6),
   (0, 2, 6), (0, 1, 7), (1, 1, 7), (0, 5, 0), (0, 0, 8), (1, 0, 8), (0, 5, 2), (0, 2, 7),
   (1, 2, 7), (0, 1, 8), (1, 1, 8), (2, 5, 2), (2, 2, 7), (0, 0, 9), (0, 3, 7), (0, 2, 8),
   (0, 6, 2), (1, 6, 2), (0, 1, 9), (0, 6, 3), (1, 6, 3), (2, 6, 2), (0, 3, 8), (0, 0, 10),
   (0, 2, 9), (0, 7, 1), (1, 7, 1), (0, 7, 2), (0, 1, 10), (1, 1, 10), (0, 4, 8), (0, 3, 9),
   (1, 3, 9), (2, 1, 10), (0, 0, 11), (1, 0, 11), (0, 8, 0), (0, 8, 1), (1, 8, 1), (0, 1, 11),
   (1, 1, 11), (0, 3, 10), (0, 8, 3), (1, 8, 3), (2, 1, 11), (0, 2, 11), (0, 0, 12), (1, 0, 12),
   (0, 5, 9), (0, 4, 10), (0, 9, 1), (0, 1, 12), (0, 3, 11), (1, 3, 11), (2, 4, 10), (0, 9, 3),
   (1, 9, 3), (0, 2, 12), (0, 5, 10), (0, 0, 13), (0, 4, 11), (1, 4, 11), (2, 2, 12), (0, 10, 0),
   (0, 1, 13), (1, 1, 13), (0, 10, 2), (1, 10, 2), (0, 6, 10), (0, 5, 11), (0, 2, 13),
   (1, 2, 13), (0, 4, 12), (0, 0, 14), (1, 0, 14), (2, 2, 13), (3, 1, 13), (0, 3, 13),
   (0, 1, 14), (0, 6, 11), (1, 6, 11), (0, 5, 12), (1, 5, 12), (2, 1, 14), (0, 2, 14),
   (0, 4, 13), (1, 4, 13), (5, 3, 11), (0, 0, 15), (1, 0, 15), (0, 7, 11), (0, 3, 14),
   (1, 3, 14), (0, 1, 15), (0, 5, 13), (0, 12, 1), (1, 12, 1), (0, 12, 2), (1, 12, 2),
   (0, 2, 15), (0, 12, 3), (1, 12, 3), (0, 7, 12), (1, 7, 12), (0, 0, 16), (1, 0, 16),
   (0, 3, 15), (1, 3, 15), (0, 5, 14), (0, 1, 16), (1, 1, 16), (0, 13, 0), (0, 13, 1),
   (1, 13, 1), (0, 4, 15), (0, 2, 16), (1, 2, 16), (0, 13, 3), (0, 6, 14), (1, 6, 14),
   (2, 2, 16), (0, 0, 17), (0, 3, 16), (0, 5, 15), (1, 5, 15), (5, 7, 11), (0, 1, 17),
   (0, 8, 13), (1, 8, 13), (0, 7, 14), (0, 4, 16), (1, 4, 16), (0, 2, 17), (0, 6, 15),
   (1, 6, 15), (0, 14, 3)]

theorem cert_m1_9 (n : ℕ) (hn : n < 168) :
    ∃ x y z : ℕ, n = x * (3 * x - 1) / 2 + y * (y + 9) / 2 + z * (z + 1) / 2 :=
  of_chkFrom (fun x => x * (3 * x - 1) / 2) 9 L_m1_9 0 (by decide +kernel) n (Nat.zero_le n)
    (lt_of_lt_of_eq hn (by decide +kernel : 168 = 0 + L_m1_9.length))

def L_m1_11 : List (ℕ × ℕ × ℕ) :=
  [(0, 0, 0), (0, 0, 1), (1, 0, 1), (0, 0, 2), (1, 0, 2), (2, 0, 0), (0, 0, 3), (0, 1, 1),
   (1, 1, 1), (0, 1, 2), (0, 0, 4), (1, 0, 4), (0, 1, 3), (0, 2, 0), (0, 2, 1), (0, 0, 5),
   (0, 1, 4), (1, 1, 4), (2, 2, 0), (0, 2, 3), (1, 2, 3), (0, 0, 6), (0, 3, 1), (0, 2, 4),
   (0, 3, 2), (1, 3, 2), (2, 0, 6), (0, 1, 6), (0, 0, 7), (1, 0, 7), (0, 4, 0), (0, 3, 4),
   (1, 3, 4), (0, 4, 2), (0, 1, 7), (1, 1, 7), (0, 0, 8), (1, 0, 8), (2, 4, 2), (2, 1, 7),
   (0, 4, 4), (0, 2, 7), (0, 1, 8), (0, 5, 2), (1, 5, 2), (0, 0, 9), (0, 5, 3), (1, 5, 3),
   (2, 5, 2), (0, 2, 8), (0, 5, 4), (0, 1, 9), (0, 6, 1), (1, 6, 1), (0, 6, 2), (0, 0, 10),
   (1, 0, 10), (0, 3, 8), (0, 2, 9), (1, 2, 9), (2, 0, 10), (0, 1, 10), (1, 1, 10), (0, 7, 0),
   (0, 7, 1), (1, 7, 1), (0, 0, 11), (1, 0, 11), (0, 2, 10), (0, 7, 3), (1, 7, 3), (2, 0, 11),
   (0, 1, 11), (0, 7, 4), (1, 7, 4), (0, 4, 9), (0, 3, 10), (0, 8, 1), (0, 0, 12), (0, 2, 11),
   (1, 2, 11), (2, 3, 10), (0, 8, 3), (1, 8, 3), (0, 1, 12), (0, 4, 10), (0, 8, 4), (0, 3, 11),
   (1, 3, 11), (2, 1, 12), (0, 9, 0), (0, 0, 13), (1, 0, 13), (0, 9, 2), (1, 9, 2), (0, 5, 10),
   (0, 4, 11), (0, 1, 13), (1, 1, 13), (0, 3, 12), (0, 9, 4), (1, 9, 4), (2, 1, 13), (3, 0, 13),
   (0, 2, 13), (0, 0, 14), (0, 5, 11), (1, 5, 11), (0, 4, 12), (1, 4, 12), (2, 0, 14),
   (0, 1, 14), (0, 3, 13), (1, 3, 13), (5, 2, 11), (0, 10, 4), (1, 10, 4), (0, 6, 11),
   (0, 2, 14), (1, 2, 14), (0, 0, 15), (0, 4, 13), (0, 11, 1), (1, 11, 1), (0, 11, 2),
   (1, 11, 2), (0, 1, 15), (0, 11, 3), (1, 11, 3), (0, 6, 12), (1, 6, 12), (0, 5, 13),
   (1, 5, 13), (0, 2, 15), (1, 2, 15), (0, 4, 14), (0, 0, 16), (1, 0, 16), (0, 12, 0),
   (0, 12, 1), (1, 12, 1), (0, 3, 15), (0, 1, 16), (1, 1, 16), (0, 12, 3), (0, 5, 14),
   (1, 5, 14), (2, 1, 16), (0, 12, 4), (0, 2, 16), (0, 4, 15), (1, 4, 15), (5, 6, 11),
   (0, 0, 17), (0, 7, 13), (1, 7, 13), (0, 6, 14), (0, 3, 16), (1, 3, 16), (0, 1, 17),
   (0, 5, 15), (1, 5, 15), (0, 13, 3), (1, 13, 3), (2, 1, 17), (2, 5, 15), (0, 2, 17),
   (0, 8, 13), (0, 7, 14), (1, 7, 14), (4, 12, 4), (0, 0, 18), (1, 0, 18), (2, 7, 14),
   (0, 3, 17), (0, 14, 0), (0, 5, 16), (0, 1, 18), (0, 14, 2), (1, 14, 2), (2, 14, 0),
   (0, 8, 14), (1, 8, 14), (0, 4, 17), (0, 2, 18), (0, 14, 4), (1, 14, 4), (0, 6, 16),
   (1, 6, 16), (2, 2, 18), (0, 0, 19), (1, 0, 19), (0, 3, 18), (0, 5, 17), (1, 5, 17),
   (0, 9, 14), (0, 1, 19), (1, 1, 19), (0, 15, 2), (0, 7, 16), (1, 7, 16), (0, 4, 18),
   (1, 4, 18), (0, 2, 19), (0, 6, 17), (0, 15, 4), (1, 15, 4), (3, 9, 14), (2, 2, 19),
   (2, 6, 17), (0, 0, 20), (0, 3, 19), (0, 8, 16), (1, 8, 16), (4, 3, 18), (2, 0, 20),
   (0, 1, 20), (0, 16, 1), (1, 16, 1), (0, 16, 2), (0, 4, 19), (1, 4, 19), (0, 6, 18),
   (0, 2, 20), (1, 2, 20), (0, 10, 15), (0, 9, 16), (1, 9, 16), (2, 2, 20), (0, 8, 17),
   (0, 5, 19), (0, 0, 21), (1, 0, 21), (4, 3, 19), (0, 7, 18), (1, 7, 18), (2, 0, 21),
   (0, 1, 21), (0, 17, 0), (0, 17, 1), (0, 4, 20), (0, 6, 19), (1, 6, 19), (0, 9, 17),
   (0, 2, 21), (1, 2, 21), (2, 6, 19), (0, 8, 18), (0, 17, 4), (1, 17, 4), (0, 5, 20),
   (1, 5, 20), (0, 3, 21), (0, 0, 22), (1, 0, 22), (2, 5, 20), (3, 2, 21), (0, 11, 16),
   (0, 10, 17), (0, 1, 22), (1, 1, 22), (0, 4, 21), (0, 18, 1), (1, 18, 1), (0, 18, 2),
   (1, 18, 2), (0, 2, 22), (0, 18, 3), (1, 18, 3), (2, 18, 2), (3, 10, 17), (0, 5, 21),
   (1, 5, 21), (0, 7, 20), (0, 3, 22), (1, 3, 22), (0, 0, 23), (1, 0, 23), (2, 7, 20)]

theorem cert_m1_11 (n : ℕ) (hn : n < 279) :
    ∃ x y z : ℕ, n = x * (3 * x - 1) / 2 + y * (y + 11) / 2 + z * (z + 1) / 2 :=
  of_chkFrom (fun x => x * (3 * x - 1) / 2) 11 L_m1_11 0 (by decide +kernel) n (Nat.zero_le n)
    (lt_of_lt_of_eq hn (by decide +kernel : 279 = 0 + L_m1_11.length))

def L_m1_13 : List (ℕ × ℕ × ℕ) :=
  [(0, 0, 0), (0, 0, 1), (1, 0, 1), (0, 0, 2), (1, 0, 2), (2, 0, 0), (0, 0, 3), (0, 1, 0),
   (0, 1, 1), (1, 1, 1), (0, 0, 4), (1, 0, 4), (2, 1, 0), (0, 1, 3), (1, 1, 3), (0, 0, 5),
   (0, 2, 1), (0, 1, 4), (0, 2, 2), (1, 2, 2), (2, 0, 5), (0, 0, 6), (0, 1, 5), (1, 1, 5),
   (0, 3, 0), (0, 2, 4), (1, 2, 4), (0, 3, 2), (0, 0, 7), (1, 0, 7), (0, 2, 5), (1, 2, 5),
   (2, 3, 2), (2, 0, 7), (0, 3, 4), (0, 1, 7), (0, 0, 8), (0, 4, 2), (1, 4, 2), (0, 3, 5),
   (0, 4, 3), (1, 4, 3), (2, 4, 2), (0, 1, 8), (0, 4, 4), (0, 0, 9), (0, 5, 1), (1, 5, 1),
   (0, 5, 2), (0, 4, 5), (1, 4, 5), (0, 2, 8), (0, 1, 9), (1, 1, 9), (2, 4, 5), (0, 0, 10),
   (1, 0, 10), (0, 6, 0), (0, 6, 1), (1, 6, 1), (0, 2, 9), (1, 2, 9), (0, 1, 10), (0, 6, 3),
   (1, 6, 3), (2, 2, 9), (0, 0, 11), (0, 6, 4), (1, 6, 4), (0, 3, 9), (0, 2, 10), (0, 7, 1),
   (0, 6, 5), (0, 1, 11), (1, 1, 11), (2, 2, 10), (0, 7, 3), (1, 7, 3), (0, 0, 12), (0, 3, 10),
   (0, 7, 4), (0, 2, 11), (1, 2, 11), (2, 0, 12), (0, 8, 0), (0, 1, 12), (1, 1, 12), (0, 8, 2),
   (1, 8, 2), (0, 4, 10), (0, 3, 11), (0, 0, 13), (1, 0, 13), (0, 2, 12), (0, 8, 4), (1, 8, 4),
   (2, 0, 13), (3, 1, 12), (0, 1, 13), (0, 8, 5), (0, 4, 11), (1, 4, 11), (0, 3, 12), (1, 3, 12),
   (2, 8, 5), (0, 0, 14), (0, 2, 13), (1, 2, 13), (5, 1, 11), (0, 9, 4), (1, 9, 4), (0, 5, 11),
   (0, 1, 14), (1, 1, 14), (0, 9, 5), (0, 3, 13), (0, 10, 1), (1, 10, 1), (0, 10, 2), (1, 10, 2),
   (0, 0, 15), (0, 10, 3), (1, 10, 3), (0, 5, 12), (1, 5, 12), (0, 4, 13), (1, 4, 13),
   (0, 1, 15), (1, 1, 15), (0, 3, 14), (0, 10, 5), (1, 10, 5), (0, 11, 0), (0, 11, 1),
   (1, 11, 1), (0, 2, 15), (0, 0, 16), (1, 0, 16), (0, 11, 3), (0, 4, 14), (1, 4, 14),
   (2, 0, 16), (0, 11, 4), (0, 1, 16), (0, 3, 15), (1, 3, 15), (5, 5, 11), (0, 11, 5),
   (0, 6, 13), (1, 6, 13), (0, 5, 14), (0, 2, 16), (1, 2, 16), (0, 0, 17), (0, 4, 15),
   (1, 4, 15), (0, 12, 3), (1, 12, 3), (2, 0, 17), (2, 4, 15), (0, 1, 17), (0, 7, 13),
   (0, 6, 14), (1, 6, 14), (4, 11, 4), (0, 5, 15), (1, 5, 15), (2, 6, 14), (0, 2, 17),
   (0, 13, 0), (0, 4, 16), (0, 0, 18), (0, 13, 2), (1, 13, 2), (2, 13, 0), (0, 7, 14),
   (1, 7, 14), (0, 3, 17), (0, 1, 18), (0, 13, 4), (1, 13, 4), (0, 5, 16), (1, 5, 16),
   (2, 1, 18), (0, 13, 5), (1, 13, 5), (0, 2, 18), (0, 4, 17), (1, 4, 17), (0, 8, 14),
   (0, 0, 19), (1, 0, 19), (0, 14, 2), (0, 6, 16), (1, 6, 16), (0, 3, 18), (1, 3, 18),
   (0, 1, 19), (0, 5, 17), (0, 14, 4), (1, 14, 4), (3, 8, 14), (2, 1, 19), (2, 5, 17),
   (0, 8, 15), (0, 2, 19), (0, 7, 16), (1, 7, 16), (4, 2, 18), (2, 8, 15), (0, 0, 20),
   (0, 15, 1), (1, 15, 1), (0, 15, 2), (0, 3, 19), (1, 3, 19), (0, 5, 18), (0, 1, 20),
   (1, 1, 20), (0, 9, 15), (0, 8, 16), (1, 8, 16), (2, 1, 20), (0, 7, 17), (0, 4, 19),
   (0, 2, 20), (1, 2, 20), (4, 2, 19), (0, 6, 18), (1, 6, 18), (2, 2, 20), (0, 0, 21),
   (0, 16, 0), (0, 16, 1), (0, 3, 20), (0, 5, 19), (1, 5, 19), (0, 8, 17), (0, 1, 21),
   (1, 1, 21), (2, 5, 19), (0, 7, 18), (0, 16, 4), (1, 16, 4), (0, 4, 20), (1, 4, 20),
   (0, 2, 21), (0, 6, 19), (1, 6, 19), (2, 4, 20), (3, 1, 21), (0, 10, 16), (0, 9, 17),
   (0, 0, 22), (1, 0, 22), (0, 3, 21), (0, 17, 1), (1, 17, 1), (0, 17, 2), (1, 17, 2),
   (0, 1, 22), (0, 17, 3), (1, 17, 3), (2, 17, 2), (3, 9, 17), (0, 4, 21), (1, 4, 21),
   (0, 6, 20), (0, 2, 22), (1, 2, 22), (0, 9, 18), (1, 9, 18), (2, 6, 20), (2, 2, 22),
   (0, 8, 19), (1, 8, 19), (0, 0, 23), (0, 3, 22), (1, 3, 22), (0, 18, 0), (0, 7, 20),
   (1, 7, 20), (0, 18, 2), (0, 1, 23), (1, 1, 23), (0, 11, 17), (0, 10, 18), (0, 4, 22),
   (0, 6, 21), (0, 9, 19), (1, 9, 19), (0, 2, 23), (1, 2, 23), (2, 6, 21), (0, 8, 20),
   (1, 8, 20), (2, 2, 23), (3, 11, 17), (0, 5, 22), (1, 5, 22), (0, 0, 24), (0, 7, 21),
   (1, 7, 21), (0, 11, 18), (0, 19, 0), (0, 10, 19), (1, 10, 19), (0, 1, 24), (1, 1, 24),
   (0, 9, 20), (0, 4, 23), (1, 4, 23), (2, 1, 24), (3, 7, 21), (0, 19, 4), (0, 2, 24),
   (1, 2, 24), (3, 10, 19), (5, 1, 23), (0, 19, 5), (1, 19, 5), (0, 5, 23), (0, 11, 19),
   (0, 7, 22), (0, 3, 24), (0, 0, 25), (1, 0, 25), (2, 11, 19), (2, 7, 22), (2, 3, 24),
   (0, 9, 21), (0, 20, 1), (0, 1, 25), (0, 6, 23), (0, 4, 24), (1, 4, 24), (0, 20, 3),
   (0, 8, 22), (1, 8, 22), (2, 4, 24), (0, 2, 25), (1, 2, 25), (0, 11, 20), (1, 11, 20),
   (3, 1, 25), (0, 5, 24), (0, 7, 23), (1, 7, 23), (3, 20, 3), (0, 3, 25), (1, 3, 25),
   (0, 0, 26), (0, 9, 22), (1, 9, 22), (2, 3, 25), (4, 6, 23), (2, 0, 26), (0, 6, 24),
   (0, 1, 26), (0, 4, 25), (0, 8, 23), (1, 8, 23), (2, 6, 24), (0, 11, 21), (1, 11, 21),
   (2, 8, 23), (0, 2, 26), (0, 21, 4), (0, 10, 22), (1, 10, 22), (0, 5, 25), (1, 5, 25),
   (0, 21, 5), (1, 21, 5), (4, 9, 22), (0, 3, 26), (1, 3, 26), (2, 21, 5), (0, 0, 27),
   (0, 13, 20), (1, 13, 20), (0, 12, 21), (0, 6, 25), (1, 6, 25), (0, 8, 24), (0, 1, 27),
   (0, 22, 1), (1, 22, 1), (0, 22, 2), (1, 22, 2), (2, 1, 27), (0, 10, 23), (1, 10, 23),
   (0, 2, 27), (1, 2, 27), (0, 7, 25), (0, 5, 26), (1, 5, 26), (2, 2, 27), (0, 9, 24),
   (0, 13, 21), (1, 13, 21), (0, 3, 27), (0, 12, 22), (1, 12, 22), (2, 13, 21), (0, 0, 28),
   (1, 0, 28), (0, 6, 26), (0, 8, 25), (1, 8, 25), (2, 0, 28), (0, 4, 27), (0, 1, 28),
   (0, 23, 0), (0, 10, 24), (1, 10, 24), (0, 23, 2)]

theorem cert_m1_13 (n : ℕ) (hn : n < 418) :
    ∃ x y z : ℕ, n = x * (3 * x - 1) / 2 + y * (y + 13) / 2 + z * (z + 1) / 2 :=
  of_chkFrom (fun x => x * (3 * x - 1) / 2) 13 L_m1_13 0 (by decide +kernel) n (Nat.zero_le n)
    (lt_of_lt_of_eq hn (by decide +kernel : 418 = 0 + L_m1_13.length))

def L_m1_15 : List (ℕ × ℕ × ℕ) :=
  [(0, 0, 0), (0, 0, 1), (1, 0, 1), (0, 0, 2), (1, 0, 2), (2, 0, 0), (0, 0, 3), (1, 0, 3),
   (0, 1, 0), (0, 1, 1), (0, 0, 4), (0, 1, 2), (1, 1, 2), (2, 1, 0), (0, 1, 3), (0, 0, 5),
   (1, 0, 5), (0, 2, 0), (0, 1, 4), (1, 1, 4), (0, 2, 2), (0, 0, 6), (1, 0, 6), (0, 1, 5),
   (1, 1, 5), (2, 2, 2), (2, 0, 6), (0, 2, 4), (0, 0, 7), (0, 1, 6), (0, 3, 2), (1, 3, 2),
   (0, 2, 5), (0, 3, 3), (1, 3, 3), (2, 3, 2), (0, 0, 8), (0, 3, 4), (0, 2, 6), (0, 4, 1),
   (1, 4, 1), (0, 4, 2), (0, 3, 5), (1, 3, 5), (0, 1, 8), (0, 0, 9), (1, 0, 9), (2, 3, 5),
   (0, 3, 6), (1, 3, 6), (0, 5, 0), (0, 5, 1), (1, 5, 1), (0, 1, 9), (1, 1, 9), (0, 0, 10),
   (0, 5, 3), (1, 5, 3), (2, 1, 9), (0, 4, 6), (0, 5, 4), (1, 5, 4), (0, 2, 9), (0, 1, 10),
   (0, 6, 1), (0, 5, 5), (0, 0, 11), (1, 0, 11), (2, 1, 10), (0, 6, 3), (1, 6, 3), (0, 5, 6),
   (0, 2, 10), (0, 6, 4), (0, 1, 11), (1, 1, 11), (2, 5, 6), (0, 7, 0), (0, 0, 12), (1, 0, 12),
   (0, 7, 2), (1, 7, 2), (0, 3, 10), (0, 2, 11), (0, 6, 6), (1, 6, 6), (0, 1, 12), (0, 7, 4),
   (1, 7, 4), (2, 6, 6), (3, 0, 12), (0, 0, 13), (0, 7, 5), (0, 3, 11), (1, 3, 11), (0, 2, 12),
   (1, 2, 12), (2, 7, 5), (0, 7, 6), (0, 1, 13), (1, 1, 13), (5, 0, 11), (0, 8, 4), (1, 8, 4),
   (0, 4, 11), (0, 0, 14), (1, 0, 14), (0, 8, 5), (0, 2, 13), (0, 9, 1), (1, 9, 1), (0, 9, 2),
   (1, 9, 2), (0, 1, 14), (0, 9, 3), (1, 9, 3), (0, 4, 12), (1, 4, 12), (0, 3, 13), (1, 3, 13),
   (0, 0, 15), (1, 0, 15), (0, 2, 14), (0, 9, 5), (1, 9, 5), (0, 10, 0), (0, 10, 1), (1, 10, 1),
   (0, 1, 15), (0, 4, 13), (1, 4, 13), (0, 10, 3), (0, 3, 14), (1, 3, 14), (2, 4, 13),
   (0, 10, 4), (0, 0, 16), (0, 2, 15), (1, 2, 15), (5, 4, 11), (0, 10, 5), (0, 5, 13),
   (1, 5, 13), (0, 4, 14), (0, 1, 16), (1, 1, 16), (0, 10, 6), (0, 3, 15), (1, 3, 15),
   (0, 11, 3), (1, 11, 3), (2, 10, 6), (2, 3, 15), (0, 0, 17), (0, 6, 13), (0, 5, 14),
   (1, 5, 14), (4, 10, 4), (0, 4, 15), (1, 4, 15), (2, 5, 14), (0, 1, 17), (0, 12, 0),
   (0, 3, 16), (0, 11, 6), (0, 12, 2), (1, 12, 2), (2, 12, 0), (0, 6, 14), (1, 6, 14),
   (0, 2, 17), (0, 0, 18), (0, 12, 4), (1, 12, 4), (0, 4, 16), (1, 4, 16), (2, 0, 18),
   (0, 12, 5), (1, 12, 5), (0, 1, 18), (0, 3, 17), (1, 3, 17), (0, 7, 14), (0, 6, 15),
   (1, 6, 15), (0, 13, 2), (0, 5, 16), (1, 5, 16), (0, 2, 18), (1, 2, 18), (0, 0, 19),
   (0, 4, 17), (0, 13, 4), (1, 13, 4), (3, 7, 14), (2, 0, 19), (2, 4, 17), (0, 7, 15),
   (0, 1, 19), (0, 6, 16), (1, 6, 16), (4, 1, 18), (2, 7, 15), (0, 5, 17), (0, 14, 1),
   (1, 14, 1), (0, 14, 2), (0, 2, 19), (1, 2, 19), (0, 4, 18), (0, 0, 20), (1, 0, 20),
   (0, 8, 15), (0, 7, 16), (1, 7, 16), (2, 0, 20), (0, 6, 17), (0, 3, 19), (0, 1, 20),
   (1, 1, 20), (4, 1, 19), (0, 5, 18), (1, 5, 18), (2, 1, 20), (0, 14, 6), (0, 15, 0),
   (0, 15, 1), (0, 2, 20), (0, 4, 19), (1, 4, 19), (0, 7, 17), (0, 0, 21), (1, 0, 21),
   (2, 4, 19), (0, 6, 18), (0, 15, 4), (1, 15, 4), (0, 3, 20), (1, 3, 20), (0, 1, 21),
   (0, 5, 19), (1, 5, 19), (2, 3, 20), (3, 0, 21), (0, 9, 16), (0, 8, 17), (0, 15, 6),
   (1, 15, 6), (0, 2, 21), (0, 16, 1), (1, 16, 1), (0, 16, 2), (1, 16, 2), (0, 0, 22),
   (0, 16, 3), (1, 16, 3), (2, 16, 2), (3, 8, 17), (0, 3, 21), (1, 3, 21), (0, 5, 20),
   (0, 1, 22), (1, 1, 22), (0, 8, 18), (1, 8, 18), (2, 5, 20), (2, 1, 22), (0, 7, 19),
   (1, 7, 19), (0, 4, 21), (0, 2, 22), (1, 2, 22), (0, 17, 0), (0, 6, 20), (1, 6, 20),
   (0, 17, 2), (0, 0, 23), (1, 0, 23), (0, 10, 17), (0, 9, 18), (0, 3, 22), (0, 5, 21),
   (0, 8, 19), (1, 8, 19), (0, 1, 23), (1, 1, 23), (2, 5, 21), (0, 7, 20), (1, 7, 20),
   (2, 1, 23), (3, 10, 17), (0, 4, 22), (1, 4, 22), (0, 2, 23), (0, 6, 21), (1, 6, 21),
   (0, 10, 18), (0, 18, 0), (0, 9, 19), (1, 9, 19), (0, 0, 24), (1, 0, 24), (0, 8, 20),
   (0, 3, 23), (1, 3, 23), (2, 0, 24), (3, 6, 21), (0, 18, 4), (0, 1, 24), (1, 1, 24),
   (3, 9, 19), (5, 0, 23), (0, 18, 5), (1, 18, 5), (0, 4, 23), (0, 10, 19), (0, 6, 22),
   (0, 2, 24), (0, 9, 20), (1, 9, 20), (2, 10, 19), (2, 6, 22), (2, 2, 24), (0, 8, 21),
   (0, 19, 1), (0, 0, 25), (0, 5, 23), (0, 3, 24), (1, 3, 24), (0, 19, 3), (0, 7, 22),
   (1, 7, 22), (2, 3, 24), (0, 1, 25), (1, 1, 25), (0, 10, 20), (1, 10, 20), (3, 0, 25),
   (0, 4, 24), (0, 6, 23), (1, 6, 23), (3, 19, 3), (0, 2, 25), (1, 2, 25), (0, 19, 6),
   (0, 8, 22), (1, 8, 22), (2, 2, 25), (4, 5, 23), (2, 19, 6), (0, 5, 24), (0, 0, 26),
   (0, 3, 25), (0, 7, 23), (1, 7, 23), (2, 5, 24), (0, 10, 21), (1, 10, 21), (2, 7, 23),
   (0, 1, 26), (0, 20, 4), (0, 9, 22), (1, 9, 22), (0, 4, 25), (1, 4, 25), (0, 20, 5),
   (1, 20, 5), (4, 8, 22), (0, 2, 26), (1, 2, 26), (2, 20, 5), (0, 20, 6), (0, 12, 20),
   (1, 12, 20), (0, 11, 21), (0, 5, 25), (1, 5, 25), (0, 7, 24), (0, 0, 27), (0, 21, 1),
   (1, 21, 1), (0, 21, 2), (1, 21, 2), (2, 0, 27), (0, 9, 23), (1, 9, 23), (0, 1, 27),
   (1, 1, 27), (0, 6, 25), (0, 4, 26), (1, 4, 26), (2, 1, 27), (0, 8, 24), (0, 12, 21),
   (1, 12, 21), (0, 2, 27), (0, 11, 22), (1, 11, 22), (2, 12, 21), (0, 21, 6), (1, 21, 6),
   (0, 5, 26), (0, 7, 25), (1, 7, 25), (2, 21, 6), (0, 3, 27), (0, 0, 28), (0, 22, 0),
   (0, 9, 24), (1, 9, 24), (0, 22, 2), (1, 22, 2), (2, 22, 0), (0, 13, 21), (0, 1, 28),
   (0, 12, 22), (0, 4, 27), (0, 8, 25), (1, 8, 25), (0, 11, 23), (1, 11, 23), (2, 4, 27),
   (0, 22, 5), (0, 2, 28), (1, 2, 28), (0, 10, 24), (1, 10, 24), (2, 22, 5), (0, 5, 27),
   (1, 5, 27), (2, 10, 24), (3, 11, 23), (4, 22, 2), (0, 3, 28), (0, 14, 21), (0, 0, 29),
   (1, 0, 29), (0, 23, 0), (0, 12, 23), (1, 12, 23), (0, 23, 2), (0, 6, 27), (1, 6, 27),
   (0, 1, 29), (0, 4, 28), (1, 4, 28), (2, 6, 27), (0, 23, 4), (1, 23, 4), (2, 4, 28),
   (0, 10, 25), (1, 10, 25), (0, 2, 29), (1, 2, 29), (5, 11, 23), (0, 7, 27), (0, 5, 28),
   (1, 5, 28), (0, 13, 23), (0, 9, 26), (1, 9, 26), (2, 5, 28), (0, 3, 29), (1, 3, 29),
   (2, 9, 26), (0, 0, 30), (1, 0, 30), (2, 3, 29), (0, 11, 25), (0, 6, 28), (0, 8, 27),
   (0, 24, 2), (1, 24, 2), (0, 1, 30), (0, 24, 3), (1, 24, 3), (0, 10, 26), (1, 10, 26),
   (0, 15, 22), (0, 14, 23), (1, 14, 23), (2, 10, 26), (0, 2, 30), (0, 7, 28), (1, 7, 28),
   (0, 5, 29), (0, 9, 27), (0, 12, 25), (1, 12, 25), (0, 24, 6), (1, 24, 6), (2, 9, 27),
   (0, 3, 30), (1, 3, 30), (0, 11, 26), (1, 11, 26), (0, 0, 31), (1, 0, 31), (0, 6, 29),
   (1, 6, 29), (0, 25, 0), (0, 15, 23), (1, 15, 23), (0, 4, 30), (0, 1, 31), (1, 1, 31),
   (0, 25, 3), (0, 13, 25), (1, 13, 25), (2, 1, 31), (0, 25, 4), (1, 25, 4), (0, 7, 29),
   (0, 2, 31), (0, 9, 28), (0, 5, 30), (1, 5, 30), (2, 7, 29), (2, 2, 31), (2, 9, 28),
   (2, 5, 30), (0, 11, 27), (1, 11, 27), (0, 3, 31), (0, 16, 23), (0, 15, 24), (1, 15, 24),
   (0, 8, 29), (0, 0, 32), (1, 0, 32), (2, 15, 24), (0, 10, 28), (1, 10, 28), (0, 13, 26),
   (0, 4, 31), (1, 4, 31), (0, 1, 32), (1, 1, 32), (2, 13, 26), (0, 26, 3), (0, 12, 27),
   (1, 12, 27), (0, 7, 30), (0, 9, 29), (1, 9, 29), (0, 2, 32), (0, 5, 31), (1, 5, 31),
   (0, 16, 24), (0, 11, 28), (0, 15, 25), (1, 15, 25), (3, 12, 27), (2, 16, 24), (0, 14, 26),
   (0, 3, 32), (1, 3, 32), (0, 8, 30), (1, 8, 30), (0, 6, 31), (0, 10, 29), (0, 0, 33),
   (1, 0, 33), (5, 0, 32), (2, 6, 31), (2, 10, 29), (0, 4, 32), (0, 27, 0), (0, 12, 28),
   (0, 1, 33), (0, 27, 2), (1, 27, 2), (0, 17, 24), (0, 7, 31), (1, 7, 31), (2, 27, 2),
   (0, 15, 26), (0, 27, 4), (0, 2, 33), (1, 2, 33), (3, 12, 28), (0, 14, 27), (0, 27, 5),
   (1, 27, 5), (3, 17, 24)]

theorem cert_m1_15 (n : ℕ) (hn : n < 585) :
    ∃ x y z : ℕ, n = x * (3 * x - 1) / 2 + y * (y + 15) / 2 + z * (z + 1) / 2 :=
  of_chkFrom (fun x => x * (3 * x - 1) / 2) 15 L_m1_15 0 (by decide +kernel) n (Nat.zero_le n)
    (lt_of_lt_of_eq hn (by decide +kernel : 585 = 0 + L_m1_15.length))

def L_m1_17 : List (ℕ × ℕ × ℕ) :=
  [(0, 0, 0), (0, 0, 1), (1, 0, 1), (0, 0, 2), (1, 0, 2), (2, 0, 0), (0, 0, 3), (1, 0, 3),
   (2, 0, 2), (0, 1, 0), (0, 0, 4), (1, 0, 4), (0, 1, 2), (1, 1, 2), (2, 1, 0), (0, 0, 5),
   (1, 0, 5), (2, 1, 2), (3, 0, 3), (0, 1, 4), (0, 2, 1), (0, 0, 6), (0, 2, 2), (1, 2, 2),
   (0, 1, 5), (0, 2, 3), (1, 2, 3), (2, 2, 2), (0, 0, 7), (0, 2, 4), (0, 1, 6), (0, 3, 1),
   (1, 3, 1), (0, 3, 2), (0, 2, 5), (1, 2, 5), (0, 0, 8), (0, 1, 7), (1, 1, 7), (2, 2, 5),
   (0, 2, 6), (1, 2, 6), (0, 4, 0), (0, 4, 1), (1, 4, 1), (0, 0, 9), (1, 0, 9), (0, 2, 7),
   (0, 4, 3), (1, 4, 3), (2, 0, 9), (0, 3, 6), (0, 4, 4), (1, 4, 4), (0, 1, 9), (0, 0, 10),
   (0, 5, 1), (0, 4, 5), (0, 3, 7), (1, 3, 7), (2, 0, 10), (0, 5, 3), (1, 5, 3), (0, 4, 6),
   (0, 1, 10), (0, 5, 4), (0, 0, 11), (1, 0, 11), (2, 4, 6), (0, 6, 0), (0, 4, 7), (1, 4, 7),
   (0, 6, 2), (1, 6, 2), (0, 2, 10), (0, 1, 11), (0, 5, 6), (1, 5, 6), (0, 0, 12), (0, 6, 4),
   (1, 6, 4), (2, 5, 6), (3, 4, 7), (0, 5, 7), (0, 6, 5), (0, 2, 11), (1, 2, 11), (0, 1, 12),
   (1, 1, 12), (2, 6, 5), (0, 6, 6), (0, 0, 13), (1, 0, 13), (5, 3, 7), (0, 7, 4), (1, 7, 4),
   (0, 3, 11), (0, 2, 12), (1, 2, 12), (0, 7, 5), (0, 1, 13), (0, 8, 1), (1, 8, 1), (0, 8, 2),
   (1, 8, 2), (0, 0, 14), (0, 8, 3), (1, 8, 3), (0, 3, 12), (1, 3, 12), (0, 2, 13), (1, 2, 13),
   (0, 7, 7), (1, 7, 7), (0, 1, 14), (0, 8, 5), (1, 8, 5), (0, 9, 0), (0, 9, 1), (1, 9, 1),
   (0, 0, 15), (0, 3, 13), (1, 3, 13), (0, 9, 3), (0, 2, 14), (1, 2, 14), (2, 3, 13), (0, 9, 4),
   (0, 8, 7), (0, 1, 15), (1, 1, 15), (5, 3, 11), (0, 9, 5), (0, 4, 13), (1, 4, 13), (0, 3, 14),
   (0, 0, 16), (1, 0, 16), (0, 9, 6), (0, 2, 15), (1, 2, 15), (0, 10, 3), (1, 10, 3), (2, 9, 6),
   (2, 2, 15), (0, 1, 16), (0, 5, 13), (0, 4, 14), (1, 4, 14), (4, 9, 4), (0, 3, 15), (1, 3, 15),
   (2, 4, 14), (0, 0, 17), (0, 11, 0), (0, 2, 16), (0, 10, 6), (0, 11, 2), (1, 11, 2),
   (2, 11, 0), (0, 5, 14), (1, 5, 14), (0, 1, 17), (0, 10, 7), (0, 11, 4), (1, 11, 4),
   (0, 3, 16), (1, 3, 16), (2, 10, 7), (0, 11, 5), (1, 11, 5), (0, 0, 18), (0, 2, 17),
   (1, 2, 17), (0, 6, 14), (0, 5, 15), (1, 5, 15), (0, 12, 2), (0, 4, 16), (1, 4, 16),
   (0, 1, 18), (1, 1, 18), (0, 11, 7), (0, 3, 17), (0, 12, 4), (1, 12, 4), (3, 6, 14),
   (2, 11, 7), (2, 3, 17), (0, 6, 15), (0, 0, 19), (0, 5, 16), (1, 5, 16), (4, 0, 18),
   (2, 6, 15), (0, 4, 17), (0, 13, 1), (1, 13, 1), (0, 13, 2), (0, 1, 19), (1, 1, 19),
   (0, 3, 18), (0, 12, 7), (1, 12, 7), (0, 7, 15), (0, 6, 16), (1, 6, 16), (2, 12, 7),
   (0, 5, 17), (0, 2, 19), (0, 0, 20), (1, 0, 20), (4, 0, 19), (0, 4, 18), (1, 4, 18),
   (2, 0, 20), (0, 13, 6), (0, 14, 0), (0, 14, 1), (0, 1, 20), (0, 3, 19), (1, 3, 19),
   (0, 6, 17), (0, 13, 7), (1, 13, 7), (2, 3, 19), (0, 5, 18), (0, 14, 4), (1, 14, 4),
   (0, 2, 20), (1, 2, 20), (0, 0, 21), (0, 4, 19), (1, 4, 19), (2, 2, 20), (3, 13, 7),
   (0, 8, 16), (0, 7, 17), (0, 14, 6), (1, 14, 6), (0, 1, 21), (0, 15, 1), (1, 15, 1),
   (0, 15, 2), (1, 15, 2), (0, 5, 19), (0, 15, 3), (1, 15, 3), (2, 15, 2), (3, 7, 17),
   (0, 2, 21), (1, 2, 21), (0, 4, 20), (0, 0, 22), (1, 0, 22), (0, 7, 18), (1, 7, 18),
   (2, 4, 20), (2, 0, 22), (0, 6, 19), (1, 6, 19), (0, 3, 21), (0, 1, 22), (1, 1, 22),
   (0, 16, 0), (0, 5, 20), (1, 5, 20), (0, 16, 2), (0, 15, 7), (1, 15, 7), (0, 9, 17),
   (0, 8, 18), (0, 2, 22), (0, 4, 21), (0, 7, 19), (1, 7, 19), (0, 0, 23), (1, 0, 23),
   (2, 4, 21), (0, 6, 20), (1, 6, 20), (2, 0, 23), (3, 9, 17), (0, 3, 22), (1, 3, 22),
   (0, 1, 23), (0, 5, 21), (1, 5, 21), (0, 9, 18), (0, 17, 0), (0, 8, 19), (1, 8, 19),
   (0, 16, 7), (1, 16, 7), (0, 7, 20), (0, 2, 23), (1, 2, 23), (2, 16, 7), (3, 5, 21),
   (0, 17, 4), (0, 0, 24), (1, 0, 24), (3, 8, 19), (5, 15, 7), (0, 17, 5), (1, 17, 5),
   (0, 3, 23), (0, 9, 19), (0, 5, 22), (0, 1, 24), (0, 8, 20), (1, 8, 20), (2, 9, 19),
   (2, 5, 22), (2, 1, 24), (0, 7, 21), (0, 18, 1), (0, 17, 7), (0, 4, 23), (0, 2, 24),
   (1, 2, 24), (0, 18, 3), (0, 6, 22), (1, 6, 22), (2, 2, 24), (0, 0, 25), (1, 0, 25),
   (0, 9, 20), (1, 9, 20), (3, 17, 7), (0, 3, 24), (0, 5, 23), (1, 5, 23), (3, 18, 3),
   (0, 1, 25), (1, 1, 25), (0, 18, 6), (0, 7, 22), (1, 7, 22), (2, 1, 25), (4, 4, 23),
   (2, 18, 6), (0, 4, 24), (0, 18, 7), (0, 2, 25), (0, 6, 23), (1, 6, 23), (2, 4, 24),
   (0, 9, 21), (1, 9, 21), (2, 6, 23), (0, 0, 26), (0, 19, 4), (0, 8, 22), (1, 8, 22),
   (0, 3, 25), (1, 3, 25), (0, 19, 5), (1, 19, 5), (4, 7, 22), (0, 1, 26), (1, 1, 26),
   (2, 19, 5), (0, 19, 6), (0, 11, 20), (1, 11, 20), (0, 10, 21), (0, 4, 25), (1, 4, 25),
   (0, 6, 24), (0, 2, 26), (0, 20, 1), (1, 20, 1), (0, 20, 2), (1, 20, 2), (2, 2, 26),
   (0, 8, 23), (1, 8, 23), (0, 0, 27), (1, 0, 27), (0, 5, 25), (0, 3, 26), (1, 3, 26),
   (2, 0, 27), (0, 7, 24), (0, 11, 21), (1, 11, 21), (0, 1, 27), (0, 10, 22), (1, 10, 22),
   (2, 11, 21), (0, 20, 6), (1, 20, 6), (0, 4, 26), (0, 6, 25), (1, 6, 25), (2, 20, 6),
   (0, 2, 27), (0, 20, 7), (0, 21, 0), (0, 8, 24), (1, 8, 24), (0, 21, 2), (1, 21, 2),
   (2, 21, 0), (0, 12, 21), (0, 0, 28), (0, 11, 22), (0, 3, 27), (0, 7, 25), (1, 7, 25),
   (0, 10, 23), (1, 10, 23), (2, 3, 27), (0, 21, 5), (0, 1, 28), (1, 1, 28), (0, 9, 24),
   (1, 9, 24), (2, 21, 5), (0, 4, 27), (1, 4, 27), (2, 9, 24), (3, 10, 23), (4, 21, 2),
   (0, 2, 28), (0, 13, 21), (0, 12, 22), (1, 12, 22), (0, 22, 0), (0, 11, 23), (1, 11, 23),
   (0, 22, 2), (0, 5, 27), (1, 5, 27), (0, 0, 29), (0, 3, 28), (1, 3, 28), (2, 5, 27),
   (0, 22, 4), (1, 22, 4), (2, 3, 28), (0, 9, 25), (1, 9, 25), (0, 1, 29), (1, 1, 29),
   (5, 10, 23), (0, 6, 27), (0, 4, 28), (1, 4, 28), (0, 12, 23), (0, 8, 26), (1, 8, 26),
   (2, 4, 28), (0, 2, 29), (1, 2, 29), (2, 8, 26), (0, 22, 7), (1, 22, 7), (2, 2, 29),
   (0, 10, 25), (0, 5, 28), (0, 7, 27), (0, 23, 2), (1, 23, 2), (0, 0, 30), (0, 23, 3),
   (1, 23, 3), (0, 9, 26), (1, 9, 26), (0, 14, 22), (0, 13, 23), (1, 13, 23), (2, 9, 26),
   (0, 1, 30), (0, 6, 28), (1, 6, 28), (0, 4, 29), (0, 8, 27), (0, 11, 25), (1, 11, 25),
   (0, 23, 6), (1, 23, 6), (2, 8, 27), (0, 2, 30), (1, 2, 30), (0, 10, 26), (1, 10, 26),
   (0, 23, 7), (1, 23, 7), (0, 5, 29), (1, 5, 29), (0, 24, 0), (0, 14, 23), (1, 14, 23),
   (0, 3, 30), (0, 0, 31), (1, 0, 31), (0, 24, 3), (0, 12, 25), (1, 12, 25), (2, 0, 31),
   (0, 24, 4), (1, 24, 4), (0, 6, 29), (0, 1, 31), (0, 8, 28), (0, 4, 30), (1, 4, 30),
   (2, 6, 29), (2, 1, 31), (2, 8, 28), (2, 4, 30), (0, 10, 27), (1, 10, 27), (0, 2, 31),
   (0, 15, 23), (0, 14, 24), (1, 14, 24), (0, 7, 29), (0, 5, 30), (1, 5, 30), (2, 14, 24),
   (0, 9, 28), (1, 9, 28), (0, 12, 26), (0, 3, 31), (1, 3, 31), (0, 0, 32), (1, 0, 32),
   (2, 12, 26), (0, 25, 3), (0, 11, 27), (1, 11, 27), (0, 6, 30), (0, 8, 29), (1, 8, 29),
   (0, 1, 32), (0, 4, 31), (1, 4, 31), (0, 15, 24), (0, 10, 28), (0, 14, 25), (1, 14, 25),
   (3, 11, 27), (2, 15, 24), (0, 13, 26), (0, 2, 32), (1, 2, 32), (0, 7, 30), (1, 7, 30),
   (0, 5, 31), (0, 9, 29), (0, 25, 7), (1, 25, 7), (5, 5, 30), (2, 5, 31), (2, 9, 29),
   (0, 3, 32), (0, 26, 0), (0, 11, 28), (0, 0, 33), (0, 26, 2), (1, 26, 2), (0, 16, 24),
   (0, 6, 31), (1, 6, 31), (2, 26, 2), (0, 14, 26), (0, 26, 4), (0, 1, 33), (1, 1, 33),
   (3, 11, 28), (0, 13, 27), (0, 26, 5), (1, 26, 5), (3, 16, 24), (3, 6, 31), (2, 13, 27),
   (2, 26, 5), (0, 2, 33), (1, 2, 33), (0, 9, 30), (0, 5, 32), (1, 5, 32), (2, 2, 33),
   (3, 26, 5), (0, 26, 7), (1, 26, 7), (0, 11, 29), (1, 11, 29), (0, 3, 33), (1, 3, 33),
   (5, 3, 32), (0, 27, 0), (0, 0, 34), (0, 8, 31), (0, 6, 32), (1, 6, 32), (2, 27, 0),
   (0, 10, 30), (0, 13, 28), (1, 13, 28), (0, 4, 33), (0, 1, 34), (1, 1, 34), (2, 13, 28),
   (3, 0, 34), (2, 4, 33), (0, 12, 29), (1, 12, 29), (4, 11, 29), (0, 7, 32), (0, 9, 31),
   (0, 2, 34), (0, 16, 26), (0, 5, 33), (1, 5, 33), (0, 15, 27), (0, 11, 30), (1, 11, 30),
   (2, 5, 33), (0, 27, 7), (0, 14, 28), (1, 14, 28), (0, 3, 34), (1, 3, 34), (2, 27, 7),
   (0, 8, 32), (1, 8, 32), (0, 0, 35), (0, 10, 31), (1, 10, 31), (0, 28, 2), (1, 28, 2),
   (2, 0, 35), (0, 28, 3), (0, 4, 34), (1, 4, 34), (0, 1, 35), (0, 17, 26), (1, 17, 26),
   (0, 16, 27), (1, 16, 27), (2, 1, 35), (0, 7, 33), (0, 15, 28), (1, 15, 28), (3, 28, 3),
   (0, 2, 35), (0, 5, 34), (0, 28, 6), (0, 14, 29), (1, 14, 29), (2, 2, 35), (2, 5, 34),
   (2, 28, 6), (2, 14, 29), (0, 28, 7), (1, 28, 7), (0, 3, 35), (0, 8, 33), (1, 8, 33),
   (0, 10, 32), (0, 6, 34), (1, 6, 34), (0, 0, 36), (0, 17, 27), (0, 29, 1), (1, 29, 1),
   (0, 12, 31), (1, 12, 31), (0, 4, 35), (0, 29, 3), (1, 29, 3), (0, 1, 36), (1, 1, 36),
   (0, 29, 4), (0, 9, 33), (0, 7, 34), (1, 7, 34), (5, 15, 28), (0, 11, 32), (1, 11, 32),
   (2, 7, 34), (0, 2, 36), (1, 2, 36), (2, 11, 32), (0, 29, 6), (1, 29, 6), (2, 2, 36),
   (0, 13, 31), (1, 13, 31), (0, 18, 27), (1, 18, 27), (0, 8, 34), (0, 3, 36), (1, 3, 36),
   (2, 18, 27), (0, 6, 35), (1, 6, 35), (2, 3, 36), (0, 12, 32), (0, 0, 37), (1, 0, 37),
   (0, 15, 30), (0, 30, 1), (1, 30, 1), (0, 4, 36), (1, 4, 36), (2, 15, 30), (0, 30, 3),
   (0, 1, 37), (0, 14, 31), (0, 7, 35), (0, 11, 33), (1, 11, 33), (2, 1, 37), (2, 14, 31),
   (2, 7, 35), (0, 19, 27), (0, 5, 36), (0, 2, 37), (0, 13, 32), (0, 17, 29), (1, 17, 29),
   (0, 30, 6), (1, 30, 6), (2, 13, 32), (0, 16, 30), (0, 8, 35), (1, 8, 35), (3, 19, 27),
   (0, 3, 37), (1, 3, 37), (0, 6, 36), (0, 15, 31), (1, 15, 31), (2, 3, 37), (6, 29, 6),
   (2, 6, 36), (0, 0, 38), (1, 0, 38), (4, 5, 36), (0, 31, 0), (0, 4, 37), (1, 4, 37),
   (0, 9, 35), (0, 19, 28), (0, 11, 34), (0, 1, 38), (1, 1, 38), (2, 9, 35), (2, 19, 28),
   (0, 17, 30), (1, 17, 30), (0, 13, 33), (1, 13, 33), (0, 5, 37), (0, 31, 5), (0, 2, 38),
   (1, 2, 38), (3, 1, 38), (2, 5, 37), (2, 31, 5), (0, 10, 35), (0, 8, 36), (1, 8, 36),
   (0, 15, 32), (0, 12, 34), (1, 12, 34), (0, 3, 38), (0, 6, 37), (1, 6, 37), (2, 12, 34),
   (6, 17, 29), (0, 20, 28), (0, 19, 29), (0, 14, 33), (1, 14, 33)]

theorem cert_m1_17 (n : ℕ) (hn : n < 780) :
    ∃ x y z : ℕ, n = x * (3 * x - 1) / 2 + y * (y + 17) / 2 + z * (z + 1) / 2 :=
  of_chkFrom (fun x => x * (3 * x - 1) / 2) 17 L_m1_17 0 (by decide +kernel) n (Nat.zero_le n)
    (lt_of_lt_of_eq hn (by decide +kernel : 780 = 0 + L_m1_17.length))

def L_p1_3 : List (ℕ × ℕ × ℕ) :=
  [(0, 0, 0), (0, 0, 1), (0, 1, 0)]

theorem cert_p1_3 (n : ℕ) (hn : n < 3) :
    ∃ x y z : ℕ, n = x * (3 * x + 1) / 2 + y * (y + 3) / 2 + z * (z + 1) / 2 :=
  of_chkFrom (fun x => x * (3 * x + 1) / 2) 3 L_p1_3 0 (by decide +kernel) n (Nat.zero_le n)
    (lt_of_lt_of_eq hn (by decide +kernel : 3 = 0 + L_p1_3.length))

def L_p1_5 : List (ℕ × ℕ × ℕ) :=
  [(0, 0, 0), (0, 0, 1), (1, 0, 0), (0, 0, 2), (0, 1, 1), (1, 0, 2), (0, 0, 3), (0, 2, 0),
   (0, 2, 1), (0, 1, 3), (0, 0, 4), (1, 1, 3), (0, 3, 0), (0, 1, 4), (1, 3, 0), (0, 0, 5),
   (2, 1, 3), (0, 2, 4), (0, 1, 5), (0, 4, 1), (1, 1, 5), (0, 0, 6), (0, 2, 5), (1, 0, 6),
   (0, 1, 6), (0, 5, 0), (0, 5, 1), (0, 3, 5), (0, 0, 7), (1, 3, 5)]

theorem cert_p1_5 (n : ℕ) (hn : n < 30) :
    ∃ x y z : ℕ, n = x * (3 * x + 1) / 2 + y * (y + 5) / 2 + z * (z + 1) / 2 :=
  of_chkFrom (fun x => x * (3 * x + 1) / 2) 5 L_p1_5 0 (by decide +kernel) n (Nat.zero_le n)
    (lt_of_lt_of_eq hn (by decide +kernel : 30 = 0 + L_p1_5.length))

def L_p1_7 : List (ℕ × ℕ × ℕ) :=
  [(0, 0, 0), (0, 0, 1), (1, 0, 0), (0, 0, 2), (0, 1, 0), (0, 1, 1), (0, 0, 3), (0, 1, 2),
   (1, 0, 3), (0, 2, 0), (0, 0, 4), (1, 2, 0), (0, 2, 2), (2, 0, 3), (0, 1, 4), (0, 0, 5),
   (0, 3, 1), (1, 0, 5), (0, 3, 2), (0, 1, 5), (1, 3, 2), (0, 0, 6), (0, 4, 0), (0, 4, 1),
   (0, 2, 5), (0, 1, 6), (1, 2, 5), (1, 1, 6), (0, 0, 7), (2, 4, 0), (0, 2, 6), (0, 5, 1),
   (0, 1, 7), (0, 5, 2), (1, 1, 7), (1, 5, 2), (0, 0, 8), (0, 2, 7), (1, 0, 8), (0, 6, 0),
   (0, 1, 8), (1, 6, 0), (0, 6, 2), (0, 3, 7), (1, 6, 2), (0, 0, 9), (2, 6, 0), (1, 0, 9),
   (3, 5, 2), (0, 1, 9), (0, 4, 7), (0, 3, 8), (0, 7, 2), (1, 3, 8), (0, 2, 9), (0, 0, 10),
   (1, 2, 9), (1, 0, 10), (0, 4, 8), (0, 1, 10), (0, 3, 9), (0, 8, 1), (1, 3, 9), (0, 8, 2),
   (0, 2, 10), (1, 8, 2), (0, 0, 11), (0, 4, 9), (1, 0, 11), (1, 4, 9), (0, 1, 11), (2, 2, 10),
   (0, 9, 0), (0, 9, 1), (1, 9, 0), (0, 2, 11), (3, 8, 1), (0, 4, 10), (0, 0, 12), (1, 4, 10),
   (1, 0, 12), (0, 3, 11), (0, 1, 12), (1, 3, 11), (0, 6, 9)]

theorem cert_p1_7 (n : ℕ) (hn : n < 85) :
    ∃ x y z : ℕ, n = x * (3 * x + 1) / 2 + y * (y + 7) / 2 + z * (z + 1) / 2 :=
  of_chkFrom (fun x => x * (3 * x + 1) / 2) 7 L_p1_7 0 (by decide +kernel) n (Nat.zero_le n)
    (lt_of_lt_of_eq hn (by decide +kernel : 85 = 0 + L_p1_7.length))

def L_p5_3 : List (ℕ × ℕ × ℕ) :=
  [(0, 0, 0), (0, 0, 1)]

theorem cert_p5_3 (n : ℕ) (hn : n < 2) :
    ∃ x y z : ℕ, n = x * (3 * x + 5) / 2 + y * (y + 3) / 2 + z * (z + 1) / 2 :=
  of_chkFrom (fun x => x * (3 * x + 5) / 2) 3 L_p5_3 0 (by decide +kernel) n (Nat.zero_le n)
    (lt_of_lt_of_eq hn (by decide +kernel : 2 = 0 + L_p5_3.length))

/-! ## Theorem 1.2 (universality part) -/

theorem small_m1 (d n : ℕ) (hd : d % 2 = 1) (hd3 : 3 ≤ d) (hd17 : d ≤ 17)
    (hsmall : 24 * n + 4 + 3 * d ^ 2 ≤ 87 * (d - 2) ^ 2) :
    ∃ x y z : ℕ, n = x * (3 * x - 1) / 2 + y * (y + d) / 2 + z * (z + 1) / 2 := by
  interval_cases d
  · norm_num at hsmall; exact cert_m1_3 n (by omega)
  · exact absurd hd (by norm_num)
  · norm_num at hsmall; exact cert_m1_5 n (by omega)
  · exact absurd hd (by norm_num)
  · norm_num at hsmall; exact cert_m1_7 n (by omega)
  · exact absurd hd (by norm_num)
  · norm_num at hsmall; exact cert_m1_9 n (by omega)
  · exact absurd hd (by norm_num)
  · norm_num at hsmall; exact cert_m1_11 n (by omega)
  · exact absurd hd (by norm_num)
  · norm_num at hsmall; exact cert_m1_13 n (by omega)
  · exact absurd hd (by norm_num)
  · norm_num at hsmall; exact cert_m1_15 n (by omega)
  · exact absurd hd (by norm_num)
  · norm_num at hsmall; exact cert_m1_17 n (by omega)

theorem small_p1 (d n : ℕ) (hd : d % 2 = 1) (hd3 : 3 ≤ d) (hd7 : d ≤ 7)
    (hsmall : 24 * n + 4 + 3 * d ^ 2 ≤ 87 * (d - 2) ^ 2) :
    ∃ x y z : ℕ, n = x * (3 * x + 1) / 2 + y * (y + d) / 2 + z * (z + 1) / 2 := by
  interval_cases d
  · norm_num at hsmall; exact cert_p1_3 n (by omega)
  · exact absurd hd (by norm_num)
  · norm_num at hsmall; exact cert_p1_5 n (by omega)
  · exact absurd hd (by norm_num)
  · norm_num at hsmall; exact cert_p1_7 n (by omega)

/-- The inequality `N > 87(d-2)²` over `ℤ`, from the same inequality over `ℕ`. -/
theorem big_cast (C n d : ℕ) (hd3 : 3 ≤ d) (h : 87 * (d - 2) ^ 2 < 24 * n + C + 3 * d ^ 2) :
    87 * ((d : ℤ) - 2) ^ 2 < 24 * (n : ℤ) + (C : ℤ) + 3 * (d : ℤ) ^ 2 := by
  have h2 : ((d - 2 : ℕ) : ℤ) = (d : ℤ) - 2 := by omega
  rw [← h2]
  exact_mod_cast h

/-- **Theorem 1.2(i).** For odd `d ≤ 17`, every natural number is
`x(3x-1)/2 + y(y+d)/2 + z(z+1)/2` with `x y z : ℕ`: the tuples `(3,-1,1,d,1,1)`. -/
theorem family_m1 (hP : PrimRep133) (d : ℕ) (hd : d % 2 = 1) (hd17 : d ≤ 17) (n : ℕ) :
    ∃ x y z : ℕ, n = x * (3 * x - 1) / 2 + y * (y + d) / 2 + z * (z + 1) / 2 := by
  rcases Nat.lt_or_ge d 3 with hd3 | hd3
  · have hd1 : d = 1 := by omega
    subst hd1
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨0, 0, 0, by norm_num⟩
    · obtain ⟨v, a, b, hS, hv, ha⟩ := exists_state hP 2 (Or.inr rfl) 4 (Or.inl rfl) n 1 hd
        (by push_cast; omega) (Or.inl rfl)
      exact repr_m1 n 1 hd hS hv ha
  · by_cases hbig : 87 * (d - 2) ^ 2 < 24 * n + 4 + 3 * d ^ 2
    · have hbigZ := big_cast 4 n d hd3 hbig
      have h9 : (9 : ℤ) ≤ (d : ℤ) ^ 2 := by
        have : (3 : ℤ) ≤ d := by exact_mod_cast hd3
        nlinarith
      obtain ⟨v, a, b, hS, hv, ha⟩ := exists_state hP 2 (Or.inr rfl) 4 (Or.inl rfl) n d hd
        (by push_cast at hbigZ ⊢; omega) (Or.inr (by push_cast at hbigZ ⊢; exact hbigZ))
      exact repr_m1 n d hd hS hv ha
    · exact small_m1 d n hd hd3 hd17 (by omega)

/-- **Theorem 1.2(ii).** For odd `d ≤ 7`, every natural number is
`x(3x+1)/2 + y(y+d)/2 + z(z+1)/2` with `x y z : ℕ`: the tuples `(3,1,1,d,1,1)`. -/
theorem family_p1 (hP : PrimRep133) (d : ℕ) (hd : d % 2 = 1) (hd7 : d ≤ 7) (n : ℕ) :
    ∃ x y z : ℕ, n = x * (3 * x + 1) / 2 + y * (y + d) / 2 + z * (z + 1) / 2 := by
  rcases Nat.lt_or_ge d 3 with hd3 | hd3
  · have hd1 : d = 1 := by omega
    subst hd1
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨0, 0, 0, by norm_num⟩
    · obtain ⟨v, a, b, hS, hv, ha⟩ := exists_state hP 1 (Or.inl rfl) 4 (Or.inl rfl) n 1 hd
        (by push_cast; omega) (Or.inl rfl)
      exact repr_p1 n 1 hd hS hv ha
  · by_cases hbig : 87 * (d - 2) ^ 2 < 24 * n + 4 + 3 * d ^ 2
    · have hbigZ := big_cast 4 n d hd3 hbig
      have h9 : (9 : ℤ) ≤ (d : ℤ) ^ 2 := by
        have : (3 : ℤ) ≤ d := by exact_mod_cast hd3
        nlinarith
      obtain ⟨v, a, b, hS, hv, ha⟩ := exists_state hP 1 (Or.inl rfl) 4 (Or.inl rfl) n d hd
        (by push_cast at hbigZ ⊢; omega) (Or.inr (by push_cast at hbigZ ⊢; exact hbigZ))
      exact repr_p1 n d hd hS hv ha
    · exact small_p1 d n hd hd3 hd7 (by omega)

/-- **Theorem 1.2(iii).** For `d ∈ {1, 3}`, every natural number is
`x(3x+5)/2 + y(y+d)/2 + z(z+1)/2` with `x y z : ℕ`: the tuples `(3,5,1,d,1,1)`. -/
theorem family_p5 (hP : PrimRep133) (d : ℕ) (hd : d % 2 = 1) (hd3' : d ≤ 3) (n : ℕ) :
    ∃ x y z : ℕ, n = x * (3 * x + 5) / 2 + y * (y + d) / 2 + z * (z + 1) / 2 := by
  rcases Nat.lt_or_ge d 3 with hd3 | hd3
  · have hd1 : d = 1 := by omega
    subst hd1
    obtain ⟨v, a, b, hS, hv, ha⟩ := exists_state hP 2 (Or.inr rfl) 28 (Or.inr rfl) n 1 hd
      (by push_cast; omega) (Or.inl rfl)
    exact repr_p5 n 1 hd hS hv ha
  · have hd3'' : d = 3 := by omega
    subst hd3''
    by_cases hbig : 87 * (3 - 2) ^ 2 < 24 * n + 28 + 3 * 3 ^ 2
    · obtain ⟨v, a, b, hS, hv, ha⟩ := exists_state hP 2 (Or.inr rfl) 28 (Or.inr rfl) n 3 hd
        (by push_cast; omega) (Or.inr (by push_cast; norm_num at hbig ⊢; omega))
      exact repr_p5 n 3 hd hS hv ha
    · norm_num at hbig
      exact cert_p5_3 n (by omega)

/-! ## Corollary 1.3 and the remaining tuples -/

/-- Lemma 5.3: a sum of two triangular numbers is of the form `r(r+1) + s²`. -/
theorem two_tri_eq (y z : ℕ) : ∃ r s : ℕ, y * (y + 1) / 2 + z * (z + 1) / 2 = r * (r + 1) + s ^ 2 := by
  have aux : ∀ y z : ℕ, z ≤ y →
      ∃ r s : ℕ, y * (y + 1) / 2 + z * (z + 1) / 2 = r * (r + 1) + s ^ 2 := by
    intro y z hzy
    obtain ⟨Y, hY⟩ := Nat.even_mul_succ_self y
    obtain ⟨Z, hZ⟩ := Nat.even_mul_succ_self z
    rcases Nat.even_or_odd (y - z) with ⟨k, hk⟩ | ⟨k, hk⟩
    · have hy : y = z + k + k := by omega
      subst hy
      have key : (z + k + k) * (z + k + k + 1) + z * (z + 1) = 2 * ((z + k) * (z + k + 1) + k ^ 2) := by
        ring
      refine ⟨z + k, k, ?_⟩
      rw [hY, hZ] at *
      omega
    · have hy : y = z + 2 * k + 1 := by omega
      subst hy
      have key : (z + 2 * k + 1) * (z + 2 * k + 1 + 1) + z * (z + 1) =
          2 * (k * (k + 1) + (z + k + 1) ^ 2) := by
        ring
      refine ⟨k, z + k + 1, ?_⟩
      rw [hY, hZ] at *
      omega
  rcases le_total z y with h | h
  · exact aux y z h
  · obtain ⟨r, s, hrs⟩ := aux z y h
    exact ⟨r, s, by omega⟩

/-- **Corollary 1.3**: the tuples `(3,-1,2,2,2,0)`, `(3,1,2,2,2,0)`, `(3,5,2,2,2,0)`. -/
theorem tuple_3_m1_2_2_2_0 (hP : PrimRep133) (n : ℕ) :
    ∃ x y z : ℕ, n = x * (3 * x - 1) / 2 + y * (y + 1) + z ^ 2 := by
  obtain ⟨x, y, z, h⟩ := family_m1 hP 1 (by norm_num) (by norm_num) n
  obtain ⟨r, s, hrs⟩ := two_tri_eq y z
  exact ⟨x, r, s, by omega⟩

theorem tuple_3_1_2_2_2_0 (hP : PrimRep133) (n : ℕ) :
    ∃ x y z : ℕ, n = x * (3 * x + 1) / 2 + y * (y + 1) + z ^ 2 := by
  obtain ⟨x, y, z, h⟩ := family_p1 hP 1 (by norm_num) (by norm_num) n
  obtain ⟨r, s, hrs⟩ := two_tri_eq y z
  exact ⟨x, r, s, by omega⟩

theorem tuple_3_5_2_2_2_0 (hP : PrimRep133) (n : ℕ) :
    ∃ x y z : ℕ, n = x * (3 * x + 5) / 2 + y * (y + 1) + z ^ 2 := by
  obtain ⟨x, y, z, h⟩ := family_p5 hP 1 (by norm_num) (by norm_num) n
  obtain ⟨r, s, hrs⟩ := two_tri_eq y z
  exact ⟨x, r, s, by omega⟩

/-- The tuple `(3,5,3,1,1,1)`: every natural number is `x(3x+5)/2 + y(3y+1)/2 + z(z+1)/2`. -/
theorem tuple_3_5_3_1_1_1 (hP : PrimRep113) (n : ℕ) :
    ∃ x y z : ℕ, n = x * (3 * x + 5) / 2 + y * (3 * y + 1) / 2 + z * (z + 1) / 2 := by
  obtain ⟨x, y, z, h, hy⟩ := triangular_two_pentagonal_mixed hP (n + 1)
  have hy1 : 1 ≤ y := hy (by omega)
  obtain ⟨w, rfl⟩ : ∃ w, y = w + 1 := ⟨y - 1, by omega⟩
  have e1 : 3 * (w + 1) - 1 = 3 * w + 2 := by omega
  have e2 : (w + 1) * (3 * w + 2) = w * (3 * w + 5) + 2 := by ring
  rw [e1, e2] at h
  exact ⟨w, z, x, by omega⟩

/-! ## Signed solutions: Lemma 3.7, Theorems 3.8 and 3.9 -/

/-- **Lemma 3.7.** The partner of a pair `(u, x)`, where `x ≥ -1` stands for a `v` with `v ≡ 2 (mod 3)`
(`x = v`) or for `v = 1` (`x = -1`). Either there is a pair `(u', v')` with the same norm and
`v' ≡ 1 (mod 3)`, `v' > 1`, or the linear formulas of case I give a pair of the same kind. -/
theorem partnerHat (u x : ℤ) (hu0 : 0 < u) (hx : -1 ≤ x) (hu : u % 2 = 1) (hxo : x % 2 = 1)
    (hx3 : x % 3 = 2) (hne : ¬(u = 1 ∧ x = -1)) :
    (∃ u' v' : ℤ, 0 < u' ∧ 1 < v' ∧ u' % 2 = 1 ∧ v' % 2 = 1 ∧ v' % 3 = 1 ∧
        3 * u' ^ 2 + v' ^ 2 = 3 * u ^ 2 + x ^ 2) ∨
      (0 < (u + x) / 2 ∧ -1 ≤ (3 * u - x) / 2 ∧ ((u + x) / 2) % 2 = 1 ∧
        ((3 * u - x) / 2) % 2 = 1 ∧ ((3 * u - x) / 2) % 3 = 2 ∧
        3 * ((u + x) / 2) ^ 2 + ((3 * u - x) / 2) ^ 2 = 3 * u ^ 2 + x ^ 2) := by
  by_cases h4 : (u - x) % 4 = 0
  · obtain ⟨u', h1⟩ : ∃ u' : ℤ, 2 * u' = u + x := ⟨(u + x) / 2, by omega⟩
    by_cases hbig : -1 ≤ (3 * u - x) / 2
    · right
      obtain ⟨x', h2⟩ : ∃ x' : ℤ, 2 * x' = 3 * u - x := ⟨(3 * u - x) / 2, by omega⟩
      have e1 : (u + x) / 2 = u' := by omega
      have e2 : (3 * u - x) / 2 = x' := by omega
      rw [e1, e2]
      exact ⟨by omega, by omega, by omega, by omega, by omega, normI h1 h2⟩
    · left
      obtain ⟨v', h2⟩ : ∃ v' : ℤ, 2 * v' = x - 3 * u := ⟨(x - 3 * u) / 2, by omega⟩
      exact ⟨u', v', by omega, by omega, by omega, by omega, by omega, normII h1 h2⟩
  · left
    obtain ⟨v', h2⟩ : ∃ v' : ℤ, 2 * v' = 3 * u + x := ⟨(3 * u + x) / 2, by omega⟩
    rcases lt_or_ge u x with hlt | hge
    · obtain ⟨u', h1⟩ : ∃ u' : ℤ, 2 * u' = x - u := ⟨(x - u) / 2, by omega⟩
      exact ⟨u', v', by omega, by omega, by omega, by omega, by omega, normIII' h1 h2⟩
    · obtain ⟨u', h1⟩ : ∃ u' : ℤ, 2 * u' = u - x := ⟨(u - x) / 2, by omega⟩
      exact ⟨u', v', by omega, by omega, by omega, by omega, by omega, normIII h1 h2⟩

theorem stepS_rec' {s : ℤ × ℤ × ℤ} (hv : s.1 % 2 = 1) (ha : s.2.1 % 2 = 1) (hb : s.2.2 % 2 = 1)
    (hv1 : ((3 * s.2.1 - s.1) / 2) % 2 = 1) :
    Rel1 (s.2.1 - s.1) (s.2.2 - s.1) ((stepS s).2.1 - (stepS s).1)
      ((stepS s).2.2 - (stepS s).1) := by
  simp only [stepS, Rel1]
  constructor <;> omega

/-- A set of integer triples `(v, a, b)` with odd entries that is contained in a box and closed
under the linear maps `A` and `B` of Theorem 3.2 consists of diagonal triples. -/
theorem orbitS (P : ℤ → ℤ → ℤ → Prop) (M : ℕ)
    (hbox : ∀ v a b, P v a b →
      -(M : ℤ) ≤ v ∧ v ≤ M ∧ -(M : ℤ) ≤ a ∧ a ≤ M ∧ -(M : ℤ) ≤ b ∧ b ≤ M)
    (hodd : ∀ v a b, P v a b → v % 2 = 1 ∧ a % 2 = 1 ∧ b % 2 = 1)
    (hA : ∀ v a b, P v a b → P ((3 * a - v) / 2) ((a + v) / 2) b)
    (hB : ∀ v a b, P v a b → P ((3 * b - v) / 2) a ((b + v) / 2))
    {v a b : ℤ} (h : P v a b) : v = a ∧ a = b := by
  have hcl : ∀ s : ℤ × ℤ × ℤ, P s.1 s.2.1 s.2.2 →
      P ((3 * s.2.1 - s.1) / 2) ((s.2.1 + s.1) / 2) s.2.2 ∧
      P (stepS s).1 (stepS s).2.1 (stepS s).2.2 := by
    intro s hs
    have h1 := hA _ _ _ hs
    exact ⟨h1, hB _ _ _ h1⟩
  have ht : ∀ j, P (stepS^[j] (v, a, b)).1 (stepS^[j] (v, a, b)).2.1
      (stepS^[j] (v, a, b)).2.2 := by
    intro j
    induction j with
    | zero => exact h
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact (hcl _ ih).2
  have hbd : ∀ j, stepS^[j] (v, a, b) ∈
      Set.Icc ((-(M : ℤ), -(M : ℤ), -(M : ℤ)) : ℤ × ℤ × ℤ) (M, M, M) := by
    intro j
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hbox _ _ _ (ht j)
    exact ⟨⟨h1, h3, h5⟩, ⟨h2, h4, h6⟩⟩
  obtain ⟨i, j, hij, hEq⟩ := (Set.finite_Icc _ _).exists_lt_map_eq_of_forall_mem hbd
  have hper := iterate_periodic stepS (v, a, b) hij hEq
  have hrec : ∀ m, Rel1 ((stepS^[m] (v, a, b)).2.1 - (stepS^[m] (v, a, b)).1)
      ((stepS^[m] (v, a, b)).2.2 - (stepS^[m] (v, a, b)).1)
      ((stepS^[m + 1] (v, a, b)).2.1 - (stepS^[m + 1] (v, a, b)).1)
      ((stepS^[m + 1] (v, a, b)).2.2 - (stepS^[m + 1] (v, a, b)).1) := by
    intro m
    rw [Function.iterate_succ_apply']
    obtain ⟨o1, o2, o3⟩ := hodd _ _ _ (ht m)
    obtain ⟨o4, -, -⟩ := hodd _ _ _ (hcl _ (ht m)).1
    exact stepS_rec' o1 o2 o3 o4
  have hzero := descent1 (2 * M)
    (fun k => ((stepS^[i + k] (v, a, b)).2.1 - (stepS^[i + k] (v, a, b)).1,
      (stepS^[i + k] (v, a, b)).2.2 - (stepS^[i + k] (v, a, b)).1))
    (fun k => hrec (i + k)) (j - i) (by omega)
    (fun k => by
      show ((stepS^[i + (k + (j - i))] (v, a, b)).2.1 - (stepS^[i + (k + (j - i))] (v, a, b)).1,
        (stepS^[i + (k + (j - i))] (v, a, b)).2.2 - (stepS^[i + (k + (j - i))] (v, a, b)).1) = _
      rw [← Nat.add_assoc, hper k])
    (fun k => by
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hbox _ _ _ (ht (i + k))
      show -((2 * M : ℕ) : ℤ) ≤ _ ∧ _ ≤ ((2 * M : ℕ) : ℤ) ∧ -((2 * M : ℕ) : ℤ) ≤ _ ∧
        _ ≤ ((2 * M : ℕ) : ℤ)
      omega) 0
  have hback : ∀ m, (stepS^[m] (v, a, b)).2.1 - (stepS^[m] (v, a, b)).1 = 0 ∧
      (stepS^[m] (v, a, b)).2.2 - (stepS^[m] (v, a, b)).1 = 0 →
      a - v = 0 ∧ b - v = 0 := by
    intro m
    induction m with
    | zero => exact fun hm => hm
    | succ m ih =>
      intro hm
      apply ih
      obtain ⟨r1, r2⟩ := hrec m
      omega
  have h0 := hback i ⟨congrArg Prod.fst hzero, congrArg Prod.snd hzero⟩
  exact ⟨by omega, by omega⟩

theorem stepT_rec' {s : ℤ × ℤ × ℤ} (hu : s.1 % 2 = 1) (hv : s.2.1 % 2 = 1) (hw : s.2.2 % 2 = 1)
    (hu1 : ((s.1 + s.2.1) / 2) % 2 = 1) :
    Rel2 (s.1 - s.2.1) (s.1 - s.2.2) ((stepT s).1 - (stepT s).2.1)
      ((stepT s).1 - (stepT s).2.2) := by
  simp only [stepT, Rel2]
  constructor <;> omega

/-- The analogue of `orbitS` for triples `(u, v, w)` and the maps of Theorem 3.3. -/
theorem orbitT (P : ℤ → ℤ → ℤ → Prop) (M : ℕ)
    (hbox : ∀ u v w, P u v w →
      -(M : ℤ) ≤ u ∧ u ≤ M ∧ -(M : ℤ) ≤ v ∧ v ≤ M ∧ -(M : ℤ) ≤ w ∧ w ≤ M)
    (hodd : ∀ u v w, P u v w → u % 2 = 1 ∧ v % 2 = 1 ∧ w % 2 = 1)
    (hA : ∀ u v w, P u v w → P ((u + v) / 2) ((3 * u - v) / 2) w)
    (hB : ∀ u v w, P u v w → P ((u + w) / 2) v ((3 * u - w) / 2))
    {u v w : ℤ} (h : P u v w) : u = v ∧ v = w := by
  have hcl : ∀ s : ℤ × ℤ × ℤ, P s.1 s.2.1 s.2.2 →
      P ((s.1 + s.2.1) / 2) ((3 * s.1 - s.2.1) / 2) s.2.2 ∧
      P (stepT s).1 (stepT s).2.1 (stepT s).2.2 := by
    intro s hs
    have h1 := hA _ _ _ hs
    exact ⟨h1, hB _ _ _ h1⟩
  have ht : ∀ j, P (stepT^[j] (u, v, w)).1 (stepT^[j] (u, v, w)).2.1
      (stepT^[j] (u, v, w)).2.2 := by
    intro j
    induction j with
    | zero => exact h
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact (hcl _ ih).2
  have hbd : ∀ j, stepT^[j] (u, v, w) ∈
      Set.Icc ((-(M : ℤ), -(M : ℤ), -(M : ℤ)) : ℤ × ℤ × ℤ) (M, M, M) := by
    intro j
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hbox _ _ _ (ht j)
    exact ⟨⟨h1, h3, h5⟩, ⟨h2, h4, h6⟩⟩
  obtain ⟨i, j, hij, hEq⟩ := (Set.finite_Icc _ _).exists_lt_map_eq_of_forall_mem hbd
  have hper := iterate_periodic stepT (u, v, w) hij hEq
  have hrec : ∀ m, Rel2 ((stepT^[m] (u, v, w)).1 - (stepT^[m] (u, v, w)).2.1)
      ((stepT^[m] (u, v, w)).1 - (stepT^[m] (u, v, w)).2.2)
      ((stepT^[m + 1] (u, v, w)).1 - (stepT^[m + 1] (u, v, w)).2.1)
      ((stepT^[m + 1] (u, v, w)).1 - (stepT^[m + 1] (u, v, w)).2.2) := by
    intro m
    rw [Function.iterate_succ_apply']
    obtain ⟨o1, o2, o3⟩ := hodd _ _ _ (ht m)
    obtain ⟨o4, -, -⟩ := hodd _ _ _ (hcl _ (ht m)).1
    exact stepT_rec' o1 o2 o3 o4
  have hzero := descent2 (2 * M)
    (fun k => ((stepT^[i + k] (u, v, w)).1 - (stepT^[i + k] (u, v, w)).2.1,
      (stepT^[i + k] (u, v, w)).1 - (stepT^[i + k] (u, v, w)).2.2))
    (fun k => hrec (i + k)) (j - i) (by omega)
    (fun k => by
      show ((stepT^[i + (k + (j - i))] (u, v, w)).1 - (stepT^[i + (k + (j - i))] (u, v, w)).2.1,
        (stepT^[i + (k + (j - i))] (u, v, w)).1 - (stepT^[i + (k + (j - i))] (u, v, w)).2.2) = _
      rw [← Nat.add_assoc, hper k])
    (fun k => by
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hbox _ _ _ (ht (i + k))
      show -((2 * M : ℕ) : ℤ) ≤ _ ∧ _ ≤ ((2 * M : ℕ) : ℤ) ∧ -((2 * M : ℕ) : ℤ) ≤ _ ∧
        _ ≤ ((2 * M : ℕ) : ℤ)
      omega) 0
  have hback : ∀ m, (stepT^[m] (u, v, w)).1 - (stepT^[m] (u, v, w)).2.1 = 0 ∧
      (stepT^[m] (u, v, w)).1 - (stepT^[m] (u, v, w)).2.2 = 0 →
      u - v = 0 ∧ u - w = 0 := by
    intro m
    induction m with
    | zero => exact fun hm => hm
    | succ m ih =>
      intro hm
      apply ih
      obtain ⟨r1, r2⟩ := hrec m
      omega
  have h0 := hback i ⟨congrArg Prod.fst hzero, congrArg Prod.snd hzero⟩
  exact ⟨by omega, by omega⟩

/-- Signed solutions of `v² + 3a² + 3b² = N`: the entry `x ≥ -1` is `v` if `v ≡ 2 (mod 3)` and
`-1` if `v = 1`. -/
def IsSh (N x a b : ℤ) : Prop :=
  -1 ≤ x ∧ 0 < a ∧ 0 < b ∧ x % 2 = 1 ∧ a % 2 = 1 ∧ b % 2 = 1 ∧ x % 3 = 2 ∧
    x ^ 2 + 3 * a ^ 2 + 3 * b ^ 2 = N

theorem IsSh.swap {N x a b : ℤ} (h : IsSh N x a b) : IsSh N x b a := by
  obtain ⟨hx, ha0, hb0, hxo, ha, hb, hx3, heq⟩ := h
  exact ⟨hx, hb0, ha0, hxo, hb, ha, hx3, by linarith⟩

theorem IsSh.box {N x a b : ℤ} (h : IsSh N x a b) :
    -((N.toNat : ℕ) : ℤ) ≤ x ∧ x ≤ (N.toNat : ℕ) ∧ -((N.toNat : ℕ) : ℤ) ≤ a ∧ a ≤ (N.toNat : ℕ) ∧
      -((N.toNat : ℕ) : ℤ) ≤ b ∧ b ≤ (N.toNat : ℕ) := by
  obtain ⟨hx, ha0, hb0, hxo, -, -, -, heq⟩ := h
  have h1 : a ≤ N := by nlinarith [sq_nonneg x, sq_nonneg (a - 1), sq_nonneg b]
  have h2 : b ≤ N := by nlinarith [sq_nonneg x, sq_nonneg (b - 1), sq_nonneg a]
  have h3 : x ≤ N := by nlinarith [sq_nonneg (x - 1), sq_nonneg a, sq_nonneg b]
  omega

/-- From `(1, 1, b)`: `N ∈ {7, 31}`, or there is a solution with `v ≡ 1 (mod 3)`, `v > 1`. -/
theorem IsS.one_one {N b : ℤ} (h : IsS N 1 1 b) :
    N = 7 ∨ N = 31 ∨ ∃ v' a' b', IsS N v' a' b' ∧ v' % 3 = 1 ∧ 1 < v' := by
  obtain ⟨-, -, hb0, -, -, hb, -, heq⟩ := h
  have hN : N = 4 + 3 * b ^ 2 := by rw [← heq]; ring
  rcases (show b % 4 = 1 ∨ b % 4 = 3 by omega) with h1 | h3
  · obtain ⟨c, rfl⟩ : ∃ c : ℤ, b = 4 * c + 1 := ⟨(b - 1) / 4, by omega⟩
    rcases (show c = 0 ∨ 1 ≤ c by omega) with rfl | hc
    · left; rw [hN]; norm_num
    · right; right
      refine ⟨6 * c + 1, 1, 2 * c + 1, ⟨by omega, by omega, by omega, by omega, by omega,
        by omega, by omega, ?_⟩, by omega, by omega⟩
      rw [hN]; ring
  · obtain ⟨c, rfl⟩ : ∃ c : ℤ, b = 4 * c + 3 := ⟨(b - 3) / 4, by omega⟩
    rcases (show c = 0 ∨ 1 ≤ c by omega) with rfl | hc
    · right; left; rw [hN]; norm_num
    · right; right
      rcases (show c % 2 = 0 ∨ c % 2 = 1 by omega) with he | ho
      · obtain ⟨e, rfl⟩ : ∃ e : ℤ, c = 2 * e := ⟨c / 2, by omega⟩
        refine ⟨6 * e + 1, 6 * e + 3, 4 * e + 1, ⟨by omega, by omega, by omega, by omega,
          by omega, by omega, by omega, ?_⟩, by omega, by omega⟩
        rw [hN]; ring
      · obtain ⟨e, rfl⟩ : ∃ e : ℤ, c = 2 * e + 1 := ⟨(c - 1) / 2, by omega⟩
        refine ⟨6 * e + 7, 6 * e + 5, 4 * e + 3, ⟨by omega, by omega, by omega, by omega,
          by omega, by omega, by omega, ?_⟩, by omega, by omega⟩
        rw [hN]; ring

/-- **Theorem 3.8.** If `N ∉ {7, 31}` and `v² + 3a² + 3b² = N` has a solution in odd positive
integers that is not diagonal, then it has such a solution with `v ≡ 1 (mod 3)` and `v > 1`. -/
theorem exists_residue1_gt {N v a b : ℤ} (h : IsS N v a b) (hnd : ¬(v = a ∧ a = b))
    (hN7 : N ≠ 7) (hN31 : N ≠ 31) :
    ∃ v' a' b', IsS N v' a' b' ∧ v' % 3 = 1 ∧ 1 < v' := by
  by_contra hcon
  have hg : ∀ v' a' b', IsS N v' a' b' → v' % 3 = 1 → 1 < v' → False :=
    fun v' a' b' hS h1 h2 => hcon ⟨v', a', b', hS, h1, h2⟩
  have hex1 : ∀ b', ¬ IsS N 1 1 b' := by
    intro b' hb'
    rcases hb'.one_one with h7 | h31 | ⟨v', a', b'', hS, h1, h2⟩
    · exact hN7 h7
    · exact hN31 h31
    · exact hg v' a' b'' hS h1 h2
  have keyA : ∀ x a b, IsSh N x a b → IsSh N ((3 * a - x) / 2) ((a + x) / 2) b := by
    rintro x a b ⟨hx, ha0, hb0, hxo, ha, hb, hx3, heq⟩
    have hne : ¬(a = 1 ∧ x = -1) := by
      rintro ⟨rfl, rfl⟩
      exact hex1 b ⟨by norm_num, by norm_num, hb0, by norm_num, by norm_num, hb, by norm_num,
        by linear_combination heq⟩
    rcases partnerHat a x ha0 hx ha hxo hx3 hne with
      ⟨a', v', ha'0, hv'1, ha', hv', hv'3, hn⟩ | ⟨h1, h2, h3, h4, h5, hn⟩
    · exfalso
      exact hg v' a' b ⟨by omega, ha'0, hb0, hv', ha', hb, by omega,
        by linear_combination hn + heq⟩ hv'3 hv'1
    · exact ⟨h2, h1, hb0, h4, h3, hb, h5, by linear_combination hn + heq⟩
  have keyB : ∀ x a b, IsSh N x a b → IsSh N ((3 * b - x) / 2) a ((b + x) / 2) :=
    fun x a b hs => (keyA x b a hs.swap).swap
  have hdiag : ∀ x a b, IsSh N x a b → x = a ∧ a = b := fun x a b hs =>
    orbitS (IsSh N) N.toNat (fun _ _ _ h' => h'.box)
      (fun _ _ _ h' => ⟨h'.2.2.2.1, h'.2.2.2.2.1, h'.2.2.2.2.2.1⟩) keyA keyB hs
  obtain ⟨hv0, ha0, hb0, hv, ha, hb, hv3, heq⟩ := h
  rcases (show v % 3 = 2 ∨ v % 3 = 1 by omega) with h2 | h1
  · exact hnd (hdiag v a b ⟨by omega, ha0, hb0, hv, ha, hb, h2, heq⟩)
  · have hv1 : v = 1 := by
      by_contra hne
      exact hg v a b ⟨hv0, ha0, hb0, hv, ha, hb, hv3, heq⟩ h1 (by omega)
    subst hv1
    have := hdiag (-1) a b ⟨by norm_num, ha0, hb0, by norm_num, ha, hb, by norm_num,
      by linear_combination heq⟩
    omega

/-- Signed solutions of `3u² + v² + w² = N`: the entries `x, y ≥ -1` stand for `v, w` that are
`≡ 2 (mod 3)` (`x = v`) or equal to `1` (`x = -1`). -/
def IsTh (N u x y : ℤ) : Prop :=
  0 < u ∧ -1 ≤ x ∧ -1 ≤ y ∧ u % 2 = 1 ∧ x % 2 = 1 ∧ y % 2 = 1 ∧ x % 3 = 2 ∧ y % 3 = 2 ∧
    3 * u ^ 2 + x ^ 2 + y ^ 2 = N

theorem IsTh.swap {N u x y : ℤ} (h : IsTh N u x y) : IsTh N u y x := by
  obtain ⟨hu0, hx, hy, hu, hxo, hyo, hx3, hy3, heq⟩ := h
  exact ⟨hu0, hy, hx, hu, hyo, hxo, hy3, hx3, by linarith⟩

theorem IsTh.box {N u x y : ℤ} (h : IsTh N u x y) :
    -((N.toNat : ℕ) : ℤ) ≤ u ∧ u ≤ (N.toNat : ℕ) ∧ -((N.toNat : ℕ) : ℤ) ≤ x ∧ x ≤ (N.toNat : ℕ) ∧
      -((N.toNat : ℕ) : ℤ) ≤ y ∧ y ≤ (N.toNat : ℕ) := by
  obtain ⟨hu0, hx, hy, -, -, -, -, -, heq⟩ := h
  have h1 : u ≤ N := by nlinarith [sq_nonneg x, sq_nonneg (u - 1), sq_nonneg y]
  have h2 : x ≤ N := by nlinarith [sq_nonneg (x - 1), sq_nonneg (u - 1), sq_nonneg y]
  have h3 : y ≤ N := by nlinarith [sq_nonneg (y - 1), sq_nonneg (u - 1), sq_nonneg x]
  omega

/-- From `(1, 1, w)` with `w ≡ 2 (mod 3)` or `w = 1`: `N ∈ {5, 29}`, or there is a solution
`(u', v', w')` with `v' ≡ 1 (mod 3)`, `v' > 1` and `w' = 1`. -/
theorem IsT.one_one {N w : ℤ} (h : IsT N 1 1 w) (hw : w % 3 = 2 ∨ w = 1) :
    N = 5 ∨ N = 29 ∨
      ∃ u' v' w', IsT N u' v' w' ∧ v' % 3 = 1 ∧ 1 < v' ∧ (w' % 3 = 2 ∨ w' = 1) := by
  obtain ⟨-, -, hw0, -, -, hwo, -, hw3, heq⟩ := h
  have hN : N = 4 + w ^ 2 := by rw [← heq]; ring
  rcases hw with hw2 | rfl
  · rcases (show w % 12 = 5 ∨ w % 12 = 11 by omega) with h5 | h11
    · obtain ⟨c, rfl⟩ : ∃ c : ℤ, w = 12 * c + 5 := ⟨(w - 5) / 12, by omega⟩
      rcases (show c = 0 ∨ 1 ≤ c by omega) with rfl | hc
      · right; left; rw [hN]; norm_num
      · right; right
        refine ⟨6 * c + 3, 6 * c + 1, 1, ⟨by omega, by omega, by omega, by omega, by omega,
          by omega, by omega, by omega, ?_⟩, by omega, by omega, Or.inr rfl⟩
        rw [hN]; ring
    · obtain ⟨c, rfl⟩ : ∃ c : ℤ, w = 12 * c + 11 := ⟨(w - 11) / 12, by omega⟩
      right; right
      refine ⟨6 * c + 5, 6 * c + 7, 1, ⟨by omega, by omega, by omega, by omega, by omega,
        by omega, by omega, by omega, ?_⟩, by omega, by omega, Or.inr rfl⟩
      rw [hN]; ring
  · left; rw [hN]; norm_num

/-- **Theorem 3.9.** If `N ∉ {5, 29}` and `3u² + v² + w² = N` has a solution in odd positive
integers with `3 ∤ vw` that is not diagonal, then it has such a solution with `v ≡ 1 (mod 3)`,
`v > 1`, and `w ≡ 2 (mod 3)` or `w = 1`. -/
theorem exists_high_low {N u v w : ℤ} (h : IsT N u v w) (hnd : ¬(u = v ∧ v = w))
    (hN5 : N ≠ 5) (hN29 : N ≠ 29) :
    ∃ u' v' w', IsT N u' v' w' ∧ v' % 3 = 1 ∧ 1 < v' ∧ (w' % 3 = 2 ∨ w' = 1) := by
  by_contra hcon
  have hg : ∀ u' v' w', IsT N u' v' w' → v' % 3 = 1 → 1 < v' → (w' % 3 = 2 ∨ w' = 1) → False :=
    fun u' v' w' hT h1 h2 h3 => hcon ⟨u', v', w', hT, h1, h2, h3⟩
  have hg' : ∀ u' v' w', IsT N u' v' w' → w' % 3 = 1 → 1 < w' → (v' % 3 = 2 ∨ v' = 1) → False :=
    fun u' v' w' hT h1 h2 h3 => hg u' w' v' hT.swap h1 h2 h3
  have hex1 : ∀ w', ¬ IsT N 1 1 w' := by
    intro w' hw'
    have hlow : w' % 3 = 2 ∨ w' = 1 := by
      by_contra hl
      have h3 := hw'.2.2.2.2.2.2.2.1
      have h0 := hw'.2.2.1
      exact hg' 1 1 w' hw' (by omega) (by omega) (Or.inr rfl)
    rcases hw'.one_one hlow with h5 | h29 | ⟨u', v', w'', hT, a1, a2, a3⟩
    · exact hN5 h5
    · exact hN29 h29
    · exact hg u' v' w'' hT a1 a2 a3
  -- the triples with both entries low
  have keyA : ∀ u x y, IsTh N u x y → IsTh N ((u + x) / 2) ((3 * u - x) / 2) y := by
    rintro u x y ⟨hu0, hx, hy, hu, hxo, hyo, hx3, hy3, heq⟩
    have hne : ¬(u = 1 ∧ x = -1) := by
      rintro ⟨rfl, rfl⟩
      rcases (show y = -1 ∨ 0 < y by omega) with rfl | hy0
      · exact hex1 1 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
          by norm_num, by norm_num, by norm_num, by linear_combination heq⟩
      · exact hex1 y ⟨by norm_num, by norm_num, hy0, by norm_num, by norm_num, hyo,
          by norm_num, by omega, by linear_combination heq⟩
    rcases partnerHat u x hu0 hx hu hxo hx3 hne with
      ⟨u', v', hu'0, hv'1, hu', hv', hv'3, hn⟩ | ⟨h1, h2, h3, h4, h5, hn⟩
    · exfalso
      rcases (show y = -1 ∨ 0 < y by omega) with rfl | hy0
      · exact hg u' v' 1 ⟨hu'0, by omega, by norm_num, hu', hv', by norm_num, by omega,
          by norm_num, by linear_combination hn + heq⟩ hv'3 hv'1 (Or.inr rfl)
      · exact hg u' v' y ⟨hu'0, by omega, hy0, hu', hv', hyo, by omega, by omega,
          by linear_combination hn + heq⟩ hv'3 hv'1 (Or.inl hy3)
    · exact ⟨h1, h2, hy, h3, h4, hyo, h5, hy3, by linear_combination hn + heq⟩
  have keyB : ∀ u x y, IsTh N u x y → IsTh N ((u + y) / 2) x ((3 * u - y) / 2) :=
    fun u x y hs => (keyA u y x hs.swap).swap
  have hlowdiag : ∀ u x y, IsTh N u x y → u = x ∧ x = y := fun u x y hs =>
    orbitT (IsTh N) N.toNat (fun _ _ _ h' => h'.box)
      (fun _ _ _ h' => ⟨h'.2.2.2.1, h'.2.2.2.2.1, h'.2.2.2.2.2.1⟩) keyA keyB hs
  -- the triples with both entries high
  have highA : ∀ u v w, (IsT N u v w ∧ v % 3 = 1 ∧ 1 < v ∧ w % 3 = 1 ∧ 1 < w) →
      (IsT N ((u + v) / 2) ((3 * u - v) / 2) w ∧ ((3 * u - v) / 2) % 3 = 1 ∧
        1 < (3 * u - v) / 2 ∧ w % 3 = 1 ∧ 1 < w) := by
    rintro u v w ⟨hT, hv1, hv2, hw1, hw2⟩
    obtain ⟨hu0, hv0, hw0, hu, hv, hw, hv3, hw3, heq⟩ := hT
    obtain ⟨u', v', hu'0, hv'0, hu', hv', hv'3, hn, hcase⟩ := partner u v hu0 hv0 hu hv hv3
    have hT' : IsT N u' v' w := ⟨hu'0, hv'0, hw0, hu', hv', hw, hv'3, hw3, by linarith⟩
    rcases hcase with hne | ⟨_, e1, e2⟩
    · exfalso
      exact hg' u' v' w hT' hw1 hw2 (Or.inl (by omega))
    · have e1' : (u + v) / 2 = u' := by omega
      have e2' : (3 * u - v) / 2 = v' := by omega
      rw [e1', e2']
      refine ⟨hT', by omega, ?_, hw1, hw2⟩
      by_contra hle
      exact hg' u' v' w hT' hw1 hw2 (Or.inr (by omega))
  have highB : ∀ u v w, (IsT N u v w ∧ v % 3 = 1 ∧ 1 < v ∧ w % 3 = 1 ∧ 1 < w) →
      (IsT N ((u + w) / 2) v ((3 * u - w) / 2) ∧ v % 3 = 1 ∧ 1 < v ∧
        ((3 * u - w) / 2) % 3 = 1 ∧ 1 < (3 * u - w) / 2) := by
    rintro u v w ⟨hT, hv1, hv2, hw1, hw2⟩
    obtain ⟨hT', a1, a2, a3, a4⟩ := highA u w v ⟨hT.swap, hw1, hw2, hv1, hv2⟩
    exact ⟨hT'.swap, a3, a4, a1, a2⟩
  have hN0 : ∀ u v w, IsT N u v w →
      -((N.toNat : ℕ) : ℤ) ≤ u ∧ u ≤ (N.toNat : ℕ) ∧ -((N.toNat : ℕ) : ℤ) ≤ v ∧
        v ≤ (N.toNat : ℕ) ∧ -((N.toNat : ℕ) : ℤ) ≤ w ∧ w ≤ (N.toNat : ℕ) := by
    rintro u v w ⟨hu0, hv0, hw0, -, -, -, -, -, heq⟩
    have h1 : u ≤ N := by nlinarith
    have h2 : v ≤ N := by nlinarith
    have h3 : w ≤ N := by nlinarith
    omega
  obtain ⟨hu0, hv0, hw0, hu, hv, hw, hv3, hw3, heq⟩ := h
  have hT : IsT N u v w := ⟨hu0, hv0, hw0, hu, hv, hw, hv3, hw3, heq⟩
  by_cases hvh : v % 3 = 1 ∧ 1 < v
  · by_cases hwh : w % 3 = 1 ∧ 1 < w
    · exact hnd (orbitT (fun u v w => IsT N u v w ∧ v % 3 = 1 ∧ 1 < v ∧ w % 3 = 1 ∧ 1 < w)
        N.toNat (fun _ _ _ h' => hN0 _ _ _ h'.1)
        (fun _ _ _ h' => ⟨h'.1.2.2.2.1, h'.1.2.2.2.2.1, h'.1.2.2.2.2.2.1⟩) highA highB
        ⟨hT, hvh.1, hvh.2, hwh.1, hwh.2⟩)
    · exact hg u v w hT hvh.1 hvh.2 (by omega)
  · by_cases hwh : w % 3 = 1 ∧ 1 < w
    · exact hg' u v w hT hwh.1 hwh.2 (by omega)
    · have hx : v % 3 = 2 ∨ v = 1 := by omega
      have hy : w % 3 = 2 ∨ w = 1 := by omega
      rcases hx with hx | rfl <;> rcases hy with hy | rfl
      · exact hnd (hlowdiag u v w ⟨hu0, by omega, by omega, hu, hv, hw, hx, hy, heq⟩)
      · have := hlowdiag u v (-1) ⟨hu0, by omega, by norm_num, hu, hv, by norm_num, hx,
          by norm_num, by linear_combination heq⟩
        omega
      · have := hlowdiag u (-1) w ⟨hu0, by norm_num, by omega, hu, by norm_num, hw,
          by norm_num, hy, by linear_combination heq⟩
        omega
      · have := hlowdiag u (-1) (-1) ⟨hu0, by norm_num, by norm_num, hu, by norm_num,
          by norm_num, by norm_num, by norm_num, by linear_combination heq⟩
        omega

/-! ## The tuples `(3,7,1,1,1,1)`, `(3,7,2,2,2,0)` and `(3,7,3,-1,1,1)` (Theorem 1.5) -/

theorem even_37 (x : ℕ) : Even (x * (3 * x + 7)) := by
  rcases Nat.even_or_odd x with h | h
  · exact Nat.even_mul.mpr (Or.inl h)
  · refine Nat.even_mul.mpr (Or.inr ?_)
    obtain ⟨k, rfl⟩ := h
    exact ⟨3 * k + 5, by omega⟩

theorem repr_p7 (n : ℕ) {v a b : ℤ} (h : IsS (24 * n + 55) v a b) (hv : v % 3 = 1)
    (hv1 : 1 < v) :
    ∃ x y z : ℕ, n = x * (3 * x + 7) / 2 + y * (y + 1) / 2 + z * (z + 1) / 2 := by
  obtain ⟨hv0, ha0, hb0, hv2, ha2, hb2, -, heq⟩ := h
  obtain ⟨x, hx⟩ : ∃ x : ℕ, v = 6 * x + 7 := ⟨((v - 7) / 6).toNat, by omega⟩
  obtain ⟨y, hy⟩ : ∃ y : ℕ, a = 2 * y + 1 := ⟨((a - 1) / 2).toNat, by omega⟩
  obtain ⟨z, hz⟩ : ∃ z : ℕ, b = 2 * z + 1 := ⟨((b - 1) / 2).toNat, by omega⟩
  subst hx hy hz
  have h24 : (24 : ℤ) * n = 12 * (x * (3 * x + 7)) + 12 * (y * (y + 1)) + 12 * (z * (z + 1)) := by
    linear_combination (-1 : ℤ) * heq
  have hN : 2 * n = x * (3 * x + 7) + y * (y + 1) + z * (z + 1) := by
    zify
    linarith
  obtain ⟨X, hX⟩ := even_37 x
  obtain ⟨Y, hY⟩ := Nat.even_mul_succ_self y
  obtain ⟨Z, hZ⟩ := Nat.even_mul_succ_self z
  refine ⟨x, y, z, ?_⟩
  rw [hX, hY, hZ] at hN ⊢
  omega

/-- The tuple `(3,7,1,1,1,1)`: every natural number is `x(3x+7)/2 + y(y+1)/2 + z(z+1)/2`. -/
theorem tuple_3_7_1_1_1_1 (hP : PrimRep133) (n : ℕ) :
    ∃ x y z : ℕ, n = x * (3 * x + 7) / 2 + y * (y + 1) / 2 + z * (z + 1) / 2 := by
  obtain ⟨v, a, b, heq, hprim⟩ := hP (24 * n + 55) (by omega) (by omega)
  obtain ⟨v', a', b', hS, hnd⟩ := seedS (N := 24 * n + 55) (by omega) (by omega) heq hprim
  obtain ⟨v'', a'', b'', hS', h1, h2⟩ := exists_residue1_gt hS hnd (by omega) (by omega)
  exact repr_p7 n hS' h1 h2

/-- The tuple `(3,7,2,2,2,0)`: every natural number is `x(3x+7)/2 + y(y+1) + z²`. -/
theorem tuple_3_7_2_2_2_0 (hP : PrimRep133) (n : ℕ) :
    ∃ x y z : ℕ, n = x * (3 * x + 7) / 2 + y * (y + 1) + z ^ 2 := by
  obtain ⟨x, y, z, h⟩ := tuple_3_7_1_1_1_1 hP n
  obtain ⟨r, s, hrs⟩ := two_tri_eq y z
  exact ⟨x, r, s, by omega⟩

theorem repr_p7_mixed (n : ℕ) {u v w : ℤ} (h : IsT (24 * n + 53) u v w) (hv : v % 3 = 1)
    (hv1 : 1 < v) (hw : w % 3 = 2 ∨ w = 1) :
    ∃ x y z : ℕ, n = x * (3 * x + 7) / 2 + y * (3 * y - 1) / 2 + z * (z + 1) / 2 := by
  obtain ⟨hu0, hv0, hw0, hu2, hv2, hw2, -, -, heq⟩ := h
  obtain ⟨x, hx⟩ : ∃ x : ℕ, v = 6 * x + 7 := ⟨((v - 7) / 6).toNat, by omega⟩
  obtain ⟨z, hz⟩ : ∃ z : ℕ, u = 2 * z + 1 := ⟨((u - 1) / 2).toNat, by omega⟩
  rcases hw with hw | rfl
  · obtain ⟨y, hy⟩ : ∃ y : ℕ, w = 6 * y - 1 := ⟨((w + 1) / 6).toNat, by omega⟩
    have hy1 : 1 ≤ y := by omega
    subst hx hy hz
    have h24 : (24 : ℤ) * n =
        12 * (x * (3 * x + 7)) + 12 * (y * (3 * y - 1)) + 12 * (z * (z + 1)) := by
      linear_combination (-1 : ℤ) * heq
    have hN : 2 * n = x * (3 * x + 7) + y * (3 * y - 1) + z * (z + 1) := by
      zify [show 1 ≤ 3 * y by omega]
      linarith
    obtain ⟨X, hX⟩ := even_37 x
    obtain ⟨Y, hY⟩ := even_pent y
    obtain ⟨Z, hZ⟩ := Nat.even_mul_succ_self z
    refine ⟨x, y, z, ?_⟩
    rw [hX, hY, hZ] at hN ⊢
    omega
  · subst hx hz
    have h24 : (24 : ℤ) * n = 12 * (x * (3 * x + 7)) + 12 * (z * (z + 1)) := by
      linear_combination (-1 : ℤ) * heq
    have hN : 2 * n = x * (3 * x + 7) + z * (z + 1) := by
      zify
      linarith
    obtain ⟨X, hX⟩ := even_37 x
    obtain ⟨Z, hZ⟩ := Nat.even_mul_succ_self z
    refine ⟨x, 0, z, ?_⟩
    rw [hX, hZ] at hN ⊢
    omega

/-- The tuple `(3,7,3,-1,1,1)`: every natural number is `x(3x+7)/2 + y(3y-1)/2 + z(z+1)/2`. -/
theorem tuple_3_7_3_m1_1_1 (hP : PrimRep113) (n : ℕ) :
    ∃ x y z : ℕ, n = x * (3 * x + 7) / 2 + y * (3 * y - 1) / 2 + z * (z + 1) / 2 := by
  obtain ⟨u, v, w, heq, hprim⟩ := hP (24 * n + 53) (by omega) (by omega)
  obtain ⟨u', v', w', hT, hnd⟩ := seedT (N := 24 * n + 53) (by omega) (by omega) heq hprim
  obtain ⟨u'', v'', w'', hT', h1, h2, h3⟩ := exists_high_low hT hnd (by omega) (by omega)
  exact repr_p7_mixed n hT' h1 h2 h3

/-! ## Primitive solutions and two triangular numbers with different indices (Section 6) -/

theorem odd_of_dvd_odd {k x : ℤ} (hx : x % 2 = 1) (h : k ∣ x) : k % 2 = 1 := by
  obtain ⟨m, rfl⟩ := h
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · exfalso
    rw [Int.mul_emod, h0] at hx
    simp at hx
  · exact h1

theorem dvd_of_dvd_two_mul {k x : ℤ} (hk : k % 2 = 1) (h : k ∣ 2 * x) : k ∣ x := by
  have e : x = ((k + 1) / 2) * (2 * x) - k * x := by
    have h2 : 2 * ((k + 1) / 2) = k + 1 := by omega
    linear_combination (-x) * h2
  rw [e]
  exact dvd_sub (Dvd.dvd.mul_left h _) (dvd_mul_right k x)

/-- No integer `k > 1` divides `v`, `a` and `b`. -/
def Prim (v a b : ℤ) : Prop := ∀ k : ℤ, 1 < k → k ∣ v → k ∣ a → k ∣ b → False

theorem Prim.swap {v a b : ℤ} (h : Prim v a b) : Prim v b a :=
  fun k hk h1 h2 h3 => h k hk h1 h3 h2

theorem prim_of_gcd {v a b : ℤ} (hprim : Int.gcd (Int.gcd v a) b = 1) : Prim v a b := by
  intro k hk h1 h2 h3
  have h12 : k ∣ ((Int.gcd v a : ℕ) : ℤ) := Int.dvd_coe_gcd h1 h2
  have h123 : k ∣ ((Int.gcd (Int.gcd v a) b : ℕ) : ℤ) := Int.dvd_coe_gcd h12 h3
  rw [hprim] at h123
  have h1' : k = 1 := Int.eq_one_of_dvd_one (by omega) (by simpa using h123)
  omega

/-- Primitivity is preserved by a move: `2a` and `2v` are integral combinations of `a'`, `v'`. -/
theorem Prim.move {v a b v' a' : ℤ} (h : Prim v a b) (ha' : a' % 2 = 1)
    (h1 : ∃ c d : ℤ, 2 * a = c * a' + d * v') (h2 : ∃ c d : ℤ, 2 * v = c * a' + d * v') :
    Prim v' a' b := by
  intro k hk kv ka kb
  have hko := odd_of_dvd_odd ha' ka
  obtain ⟨c, d, e1⟩ := h1
  obtain ⟨c', d', e2⟩ := h2
  have k2a : k ∣ 2 * a := by
    rw [e1]; exact dvd_add (Dvd.dvd.mul_left ka c) (Dvd.dvd.mul_left kv d)
  have k2v : k ∣ 2 * v := by
    rw [e2]; exact dvd_add (Dvd.dvd.mul_left ka c') (Dvd.dvd.mul_left kv d')
  exact h k hk (dvd_of_dvd_two_mul hko k2v) (dvd_of_dvd_two_mul hko k2a) kb

/-- Definition 2.1 and Lemma 2.2(a) with the four cases explicit. -/
theorem partnerFull (u v : ℤ) (hu0 : 0 < u) (hv0 : 0 < v) (hu : u % 2 = 1) (hv : v % 2 = 1)
    (hv3 : v % 3 ≠ 0) :
    ∃ u' v' : ℤ, 0 < u' ∧ 0 < v' ∧ u' % 2 = 1 ∧ v' % 2 = 1 ∧ v' % 3 ≠ 0 ∧
      3 * u' ^ 2 + v' ^ 2 = 3 * u ^ 2 + v ^ 2 ∧
      (((u - v) % 4 = 0 ∧ v < 3 * u ∧ 2 * u' = u + v ∧ 2 * v' = 3 * u - v) ∨
       ((u - v) % 4 = 0 ∧ 3 * u < v ∧ 2 * u' = u + v ∧ 2 * v' = v - 3 * u) ∨
       ((u - v) % 4 ≠ 0 ∧ v < u ∧ 2 * u' = u - v ∧ 2 * v' = 3 * u + v) ∨
       ((u - v) % 4 ≠ 0 ∧ u < v ∧ 2 * u' = v - u ∧ 2 * v' = 3 * u + v)) := by
  by_cases h4 : (u - v) % 4 = 0
  · rcases lt_or_gt_of_ne (show v ≠ 3 * u by omega) with hlt | hgt
    · obtain ⟨u', h1⟩ : ∃ u' : ℤ, 2 * u' = u + v := ⟨(u + v) / 2, by omega⟩
      obtain ⟨v', h2⟩ : ∃ v' : ℤ, 2 * v' = 3 * u - v := ⟨(3 * u - v) / 2, by omega⟩
      exact ⟨u', v', by omega, by omega, by omega, by omega, by omega, normI h1 h2,
        Or.inl ⟨h4, hlt, h1, h2⟩⟩
    · obtain ⟨u', h1⟩ : ∃ u' : ℤ, 2 * u' = u + v := ⟨(u + v) / 2, by omega⟩
      obtain ⟨v', h2⟩ : ∃ v' : ℤ, 2 * v' = v - 3 * u := ⟨(v - 3 * u) / 2, by omega⟩
      exact ⟨u', v', by omega, by omega, by omega, by omega, by omega, normII h1 h2,
        Or.inr (Or.inl ⟨h4, hgt, h1, h2⟩)⟩
  · obtain ⟨v', h2⟩ : ∃ v' : ℤ, 2 * v' = 3 * u + v := ⟨(3 * u + v) / 2, by omega⟩
    rcases lt_or_gt_of_ne (show u ≠ v by omega) with hlt | hgt
    · obtain ⟨u', h1⟩ : ∃ u' : ℤ, 2 * u' = v - u := ⟨(v - u) / 2, by omega⟩
      exact ⟨u', v', by omega, by omega, by omega, by omega, by omega, normIII' h1 h2,
        Or.inr (Or.inr (Or.inr ⟨h4, hlt, h1, h2⟩))⟩
    · obtain ⟨u', h1⟩ : ∃ u' : ℤ, 2 * u' = u - v := ⟨(u - v) / 2, by omega⟩
      exact ⟨u', v', by omega, by omega, by omega, by omega, by omega, normIII h1 h2,
        Or.inr (Or.inr (Or.inl ⟨h4, hgt, h1, h2⟩))⟩

/-- A primitive solution of `v² + 3a² + 3b² = N` in odd positive integers. -/
def IsPS (N v a b : ℤ) : Prop := IsS N v a b ∧ Prim v a b

theorem IsPS.swap {N v a b : ℤ} (h : IsPS N v a b) : IsPS N v b a := ⟨h.1.swap, h.2.swap⟩

/-- The move `α` on primitive solutions, with the four cases of Definition 2.1. -/
theorem IsPS.stepA {N v a b : ℤ} (h : IsPS N v a b) :
    ∃ v' a' : ℤ, IsPS N v' a' b ∧
      (((a - v) % 4 = 0 ∧ v < 3 * a ∧ 2 * a' = a + v ∧ 2 * v' = 3 * a - v) ∨
       ((a - v) % 4 = 0 ∧ 3 * a < v ∧ 2 * a' = a + v ∧ 2 * v' = v - 3 * a) ∨
       ((a - v) % 4 ≠ 0 ∧ v < a ∧ 2 * a' = a - v ∧ 2 * v' = 3 * a + v) ∨
       ((a - v) % 4 ≠ 0 ∧ a < v ∧ 2 * a' = v - a ∧ 2 * v' = 3 * a + v)) := by
  obtain ⟨⟨hv0, ha0, hb0, hv, ha, hb, hv3, heq⟩, hp⟩ := h
  obtain ⟨a', v', ha'0, hv'0, ha', hv', hv'3, hn, hc⟩ := partnerFull a v ha0 hv0 ha hv hv3
  refine ⟨v', a', ⟨⟨hv'0, ha'0, hb0, hv', ha', hb, hv'3, by linarith⟩, ?_⟩, hc⟩
  rcases hc with ⟨-, -, h1, h2⟩ | ⟨-, -, h1, h2⟩ | ⟨-, -, h1, h2⟩ | ⟨-, -, h1, h2⟩
  · exact hp.move ha' ⟨1, 1, by linarith⟩ ⟨3, -1, by linarith⟩
  · exact hp.move ha' ⟨1, -1, by linarith⟩ ⟨3, 1, by linarith⟩
  · exact hp.move ha' ⟨1, 1, by linarith⟩ ⟨-3, 1, by linarith⟩
  · exact hp.move ha' ⟨-1, 1, by linarith⟩ ⟨3, 1, by linarith⟩

/-- The move `β` on primitive solutions. -/
theorem IsPS.stepB {N v a b : ℤ} (h : IsPS N v a b) :
    ∃ v' b' : ℤ, IsPS N v' a b' ∧
      (((b - v) % 4 = 0 ∧ v < 3 * b ∧ 2 * b' = b + v ∧ 2 * v' = 3 * b - v) ∨
       ((b - v) % 4 = 0 ∧ 3 * b < v ∧ 2 * b' = b + v ∧ 2 * v' = v - 3 * b) ∨
       ((b - v) % 4 ≠ 0 ∧ v < b ∧ 2 * b' = b - v ∧ 2 * v' = 3 * b + v) ∨
       ((b - v) % 4 ≠ 0 ∧ b < v ∧ 2 * b' = v - b ∧ 2 * v' = 3 * b + v)) := by
  obtain ⟨v', b', h', hc⟩ := h.swap.stepA
  exact ⟨v', b', h'.swap, hc⟩

/-! ### The four triples left over in Step 5 -/

theorem shape_5_1_1 {N v a : ℤ}
    (hcon : ∀ v a b : ℤ, IsS N v a b → (v % 3 = 2 ∨ v = 1) → a = b)
    (h : IsPS N v a a) (e : v = 5 * a) : False := by
  obtain ⟨⟨hv0, ha0, -, -, -, -, -, heq⟩, hp⟩ := h
  have ha1 : a = 1 := by
    by_contra hne
    exact hp a (by omega) ⟨5, by rw [e]; ring⟩ dvd_rfl dvd_rfl
  subst ha1
  subst e
  have hN : N = 31 := by rw [← heq]; norm_num
  have hg := hcon 1 3 1 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by rw [hN]; norm_num⟩ (Or.inr rfl)
  norm_num at hg

theorem shape_23_3_3 {N v a : ℤ}
    (hcon : ∀ v a b : ℤ, IsS N v a b → (v % 3 = 2 ∨ v = 1) → a = b)
    (h : IsPS N v a a) (e : 3 * v = 23 * a) : False := by
  obtain ⟨⟨hv0, ha0, -, -, -, -, -, heq⟩, hp⟩ := h
  obtain ⟨t, ht⟩ : ∃ t : ℤ, a = 3 * t := ⟨a / 3, by omega⟩
  have hv : v = 23 * t := by omega
  have ht1 : t = 1 := by
    by_contra hne
    exact hp t (by omega) ⟨23, by rw [hv]; ring⟩ ⟨3, by rw [ht]; ring⟩ ⟨3, by rw [ht]; ring⟩
  subst ht1
  subst ht hv
  have hN : N = 583 := by rw [← heq]; norm_num
  have hg := hcon 1 13 5 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by rw [hN]; norm_num⟩ (Or.inr rfl)
  norm_num at hg

theorem shape_17_7_7 {N v a : ℤ}
    (hcon : ∀ v a b : ℤ, IsS N v a b → (v % 3 = 2 ∨ v = 1) → a = b)
    (h : IsPS N v a a) (e : 7 * v = 17 * a) : False := by
  obtain ⟨⟨hv0, ha0, -, -, -, -, -, heq⟩, hp⟩ := h
  obtain ⟨t, ht⟩ : ∃ t : ℤ, a = 7 * t := ⟨a / 7, by omega⟩
  have hv : v = 17 * t := by omega
  have ht1 : t = 1 := by
    by_contra hne
    exact hp t (by omega) ⟨17, by rw [hv]; ring⟩ ⟨7, by rw [ht]; ring⟩ ⟨7, by rw [ht]; ring⟩
  subst ht1
  subst ht hv
  have hN : N = 583 := by rw [← heq]; norm_num
  have hg := hcon 1 5 13 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by rw [hN]; norm_num⟩ (Or.inr rfl)
  norm_num at hg

theorem shape_5_3_3 {N v a : ℤ}
    (hcon : ∀ v a b : ℤ, IsS N v a b → (v % 3 = 2 ∨ v = 1) → a = b)
    (h : IsPS N v a a) (e : 3 * v = 5 * a) : False := by
  obtain ⟨⟨hv0, ha0, -, -, -, -, -, heq⟩, hp⟩ := h
  obtain ⟨t, ht⟩ : ∃ t : ℤ, a = 3 * t := ⟨a / 3, by omega⟩
  have hv : v = 5 * t := by omega
  have ht1 : t = 1 := by
    by_contra hne
    exact hp t (by omega) ⟨5, by rw [hv]; ring⟩ ⟨3, by rw [ht]; ring⟩ ⟨3, by rw [ht]; ring⟩
  subst ht1
  subst ht hv
  have hN : N = 79 := by rw [← heq]; norm_num
  have hg := hcon 1 1 5 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by rw [hN]; norm_num⟩ (Or.inr rfl)
  norm_num at hg

theorem shape_7_1_1 {N v a : ℤ} (h : IsPS N v a a) (hv2 : v % 3 = 2) (e : v = 7 * a) : False := by
  have ha0 := h.1.2.1
  have ha1 : a = 1 := by
    by_contra hne
    exact h.2 a (by omega) ⟨7, by rw [e]; ring⟩ dvd_rfl dvd_rfl
  omega

/-! ### Step 5: symmetric triples of type II and III⁻ -/

theorem res_flipII {v u v' : ℤ} (e : 2 * v' = v - 3 * u) (h : v % 3 = 1) : v' % 3 = 2 := by
  omega

theorem res_flipIII {v u v' : ℤ} (e : 2 * v' = 3 * u + v) (h : v % 3 = 1) : v' % 3 = 2 := by
  omega

theorem res_keep {v u v' : ℤ} (e : 2 * v' = 3 * u - v) (h : v % 3 = 1) : v' % 3 = 1 := by
  omega

theorem res_startII {v u v' : ℤ} (e : 2 * v' = v - 3 * u) (h : v % 3 = 2) : v' % 3 = 1 := by
  omega

theorem res_startIII {v u v' : ℤ} (e : 2 * v' = 3 * u + v) (h : v % 3 = 2) : v' % 3 = 1 := by
  omega

theorem no_7_27 {v a : ℤ} (e : 7 * v = 27 * a) (h : v % 3 = 2) : False := by omega

theorem no_17_39 {v a : ℤ} (e : 17 * v = 39 * a) (h : v % 3 = 2) : False := by omega

theorem no_1_3 {v a : ℤ} (e : v = 3 * a) (h : v % 3 = 2) : False := by omega

/-- A primitive symmetric triple `(v, a, a)` with `v ≡ 2 (mod 3)` of type II cannot exist if
there is no good triple. -/
theorem typeII_false {N v a : ℤ}
    (hcon : ∀ v a b : ℤ, IsS N v a b → (v % 3 = 2 ∨ v = 1) → a = b)
    (h : IsPS N v a a) (hv2 : v % 3 = 2) (h4 : (a - v) % 4 = 0) (hlt : 3 * a < v) : False := by
  obtain ⟨hv0, ha0, -, -, -, -, -, -⟩ := h.1
  -- x₁ = α(s) = (v₁, a₁, a)
  obtain ⟨v₁, a₁, hx₁, c₁⟩ := h.stepA
  have r₁ : 2 * a₁ = a + v ∧ 2 * v₁ = v - 3 * a := by
    rcases c₁ with ⟨_, c, _, _⟩ | ⟨_, _, e1, e2⟩ | ⟨c, _, _, _⟩ | ⟨c, _, _, _⟩
    · exfalso; linarith
    · exact ⟨e1, e2⟩
    · exact absurd h4 c
    · exact absurd h4 c
  obtain ⟨r11, r12⟩ := r₁
  obtain ⟨hv₁0, ha₁0, -, -, -, -, -, -⟩ := hx₁.1
  have hv₁1 : v₁ % 3 = 1 := res_startII r12 hv2
  -- x₂ = (v₂, a₁, b₂): the pair (a, v₁)
  obtain ⟨v₂, b₂, hx₂, c₂⟩ := hx₁.stepB
  have r₂ : 2 * b₂ = a + v₁ ∧ 2 * v₂ = 3 * a - v₁ := by
    rcases c₂ with ⟨_, _, e1, e2⟩ | ⟨_, _, e1, e2⟩ | ⟨_, _, e1, e2⟩ | ⟨_, _, e1, e2⟩
    · exact ⟨e1, e2⟩
    · exfalso; have hs := hcon _ _ _ hx₂.1 (Or.inl (res_flipII e2 hv₁1)); linarith
    · exfalso; have hs := hcon _ _ _ hx₂.1 (Or.inl (res_flipIII e2 hv₁1)); linarith
    · exfalso; have hs := hcon _ _ _ hx₂.1 (Or.inl (res_flipIII e2 hv₁1)); linarith
  obtain ⟨r21, r22⟩ := r₂
  obtain ⟨hv₂0, -, hb₂0, -, -, -, -, -⟩ := hx₂.1
  have hv₂1 : v₂ % 3 = 1 := res_keep r22 hv₁1
  -- x₃ = (v₃, a₃, b₂): the pair (a₁, v₂)
  obtain ⟨v₃, a₃, hx₃, c₃⟩ := hx₂.stepA
  have r₃ : 2 * a₃ = a₁ + v₂ ∧ 2 * v₃ = 3 * a₁ - v₂ := by
    rcases c₃ with ⟨_, _, e1, e2⟩ | ⟨_, _, e1, e2⟩ | ⟨_, _, e1, e2⟩ | ⟨_, _, e1, e2⟩
    · exact ⟨e1, e2⟩
    · exfalso; have hs := hcon _ _ _ hx₃.1 (Or.inl (res_flipII e2 hv₂1)); linarith
    · exfalso; have hs := hcon _ _ _ hx₃.1 (Or.inl (res_flipIII e2 hv₂1))
      exact shape_5_1_1 hcon h (by linarith)
    · exfalso; have hs := hcon _ _ _ hx₃.1 (Or.inl (res_flipIII e2 hv₂1)); linarith
  obtain ⟨r31, r32⟩ := r₃
  obtain ⟨hv₃0, ha₃0, -, -, -, -, -, -⟩ := hx₃.1
  have hv₃1 : v₃ % 3 = 1 := res_keep r32 hv₂1
  -- the next triple (v₄, a₃, b₄): the pair (b₂, v₃)
  obtain ⟨v₄, b₄, hx₄, c₄⟩ := hx₃.stepB
  rcases c₄ with ⟨_, c, e1, e2⟩ | ⟨_, _, e1, e2⟩ | ⟨_, _, e1, e2⟩ | ⟨_, _, e1, e2⟩
  · linarith
  · have hs := hcon _ _ _ hx₄.1 (Or.inl (res_flipII e2 hv₃1))
    exact no_7_27 (a := a) (by linarith) hv2
  · have hs := hcon _ _ _ hx₄.1 (Or.inl (res_flipIII e2 hv₃1)); linarith
  · have hs := hcon _ _ _ hx₄.1 (Or.inl (res_flipIII e2 hv₃1))
    exact shape_23_3_3 hcon h (by linarith)

/-- The same for type III⁻. -/
theorem typeIIIm_false {N v a : ℤ}
    (hcon : ∀ v a b : ℤ, IsS N v a b → (v % 3 = 2 ∨ v = 1) → a = b)
    (h : IsPS N v a a) (hv2 : v % 3 = 2) (h4 : (a - v) % 4 ≠ 0) (hlt : a < v) : False := by
  obtain ⟨hv0, ha0, -, -, -, -, -, -⟩ := h.1
  -- x₁ = α(s) = (v₁, a₁, a)
  obtain ⟨v₁, a₁, hx₁, c₁⟩ := h.stepA
  have r₁ : 2 * a₁ = v - a ∧ 2 * v₁ = 3 * a + v := by
    rcases c₁ with ⟨c, _, _, _⟩ | ⟨c, _, _, _⟩ | ⟨_, c, _, _⟩ | ⟨_, _, e1, e2⟩
    · exact absurd c h4
    · exact absurd c h4
    · exfalso; linarith
    · exact ⟨e1, e2⟩
  obtain ⟨r11, r12⟩ := r₁
  obtain ⟨hv₁0, ha₁0, -, -, -, -, -, -⟩ := hx₁.1
  have hv₁1 : v₁ % 3 = 1 := res_startIII r12 hv2
  -- x₂ = (v₂, a₁, b₂): the pair (a, v₁)
  obtain ⟨v₂, b₂, hx₂, c₂⟩ := hx₁.stepB
  have r₂ : 2 * b₂ = a + v₁ ∧ 2 * v₂ = 3 * a - v₁ := by
    rcases c₂ with ⟨_, _, e1, e2⟩ | ⟨_, _, e1, e2⟩ | ⟨_, c, e1, e2⟩ | ⟨_, _, e1, e2⟩
    · exact ⟨e1, e2⟩
    · exfalso; have hs := hcon _ _ _ hx₂.1 (Or.inl (res_flipII e2 hv₁1))
      exact shape_7_1_1 h hv2 (by linarith)
    · exfalso; linarith
    · exfalso; have hs := hcon _ _ _ hx₂.1 (Or.inl (res_flipIII e2 hv₁1))
      exact no_1_3 (a := a) (by linarith) hv2
  obtain ⟨r21, r22⟩ := r₂
  obtain ⟨hv₂0, -, hb₂0, -, -, -, -, -⟩ := hx₂.1
  have hv₂1 : v₂ % 3 = 1 := res_keep r22 hv₁1
  -- x₃ = (v₃, a₃, b₂): the pair (a₁, v₂)
  obtain ⟨v₃, a₃, hx₃, c₃⟩ := hx₂.stepA
  have r₃ : 2 * a₃ = a₁ + v₂ ∧ 2 * v₃ = 3 * a₁ - v₂ := by
    rcases c₃ with ⟨_, _, e1, e2⟩ | ⟨_, _, e1, e2⟩ | ⟨_, _, e1, e2⟩ | ⟨_, _, e1, e2⟩
    · exact ⟨e1, e2⟩
    · exfalso; have hs := hcon _ _ _ hx₃.1 (Or.inl (res_flipII e2 hv₂1)); linarith
    · exfalso; have hs := hcon _ _ _ hx₃.1 (Or.inl (res_flipIII e2 hv₂1)); linarith
    · exfalso; have hs := hcon _ _ _ hx₃.1 (Or.inl (res_flipIII e2 hv₂1)); linarith
  obtain ⟨r31, r32⟩ := r₃
  obtain ⟨hv₃0, ha₃0, -, -, -, -, -, -⟩ := hx₃.1
  have hv₃1 : v₃ % 3 = 1 := res_keep r32 hv₂1
  -- x₄ = (v₄, a₃, b₄): the pair (b₂, v₃)
  obtain ⟨v₄, b₄, hx₄, c₄⟩ := hx₃.stepB
  have r₄ : 2 * b₄ = b₂ + v₃ ∧ 2 * v₄ = 3 * b₂ - v₃ := by
    rcases c₄ with ⟨_, _, e1, e2⟩ | ⟨_, _, e1, e2⟩ | ⟨_, _, e1, e2⟩ | ⟨_, _, e1, e2⟩
    · exact ⟨e1, e2⟩
    · exfalso; have hs := hcon _ _ _ hx₄.1 (Or.inl (res_flipII e2 hv₃1)); linarith
    · exfalso; have hs := hcon _ _ _ hx₄.1 (Or.inl (res_flipIII e2 hv₃1))
      exact shape_17_7_7 hcon h (by linarith)
    · exfalso; have hs := hcon _ _ _ hx₄.1 (Or.inl (res_flipIII e2 hv₃1)); linarith
  obtain ⟨r41, r42⟩ := r₄
  obtain ⟨hv₄0, -, hb₄0, -, -, -, -, -⟩ := hx₄.1
  have hv₄1 : v₄ % 3 = 1 := res_keep r42 hv₃1
  -- the next triple (v₅, a₅, b₄): the pair (a₃, v₄)
  obtain ⟨v₅, a₅, hx₅, c₅⟩ := hx₄.stepA
  rcases c₅ with ⟨_, c, e1, e2⟩ | ⟨_, _, e1, e2⟩ | ⟨_, _, e1, e2⟩ | ⟨_, _, e1, e2⟩
  · linarith
  · have hs := hcon _ _ _ hx₅.1 (Or.inl (res_flipII e2 hv₄1))
    exact no_17_39 (a := a) (by linarith) hv2
  · have hs := hcon _ _ _ hx₅.1 (Or.inl (res_flipIII e2 hv₄1)); linarith
  · have hs := hcon _ _ _ hx₅.1 (Or.inl (res_flipIII e2 hv₄1))
    exact shape_5_3_3 hcon h (by linarith)

/-! ### Steps 1–4: the set closed under `A` and `B` -/

/-- Triples `(x, y, z)`: either a primitive solution with `x ≡ 1 (mod 3)`, or `(-v, a, a)` for a
primitive symmetric solution `(v, a, a)` with `v ≡ 2 (mod 3)`. -/
def PSet (N x y z : ℤ) : Prop :=
  (IsPS N x y z ∧ x % 3 = 1) ∨ (x < 0 ∧ y = z ∧ IsPS N (-x) y z ∧ (-x) % 3 = 2)

theorem PSet.swap {N x y z : ℤ} (h : PSet N x y z) : PSet N x z y := by
  unfold PSet at h ⊢
  rcases h with ⟨hs, hx1⟩ | ⟨hx0, hyz, hs, hx2⟩
  · exact Or.inl ⟨hs.swap, hx1⟩
  · exact Or.inr ⟨hx0, hyz.symm, hs.swap, hx2⟩

theorem PSet.box {N x y z : ℤ} (h : PSet N x y z) :
    -((N.toNat : ℕ) : ℤ) ≤ x ∧ x ≤ (N.toNat : ℕ) ∧ -((N.toNat : ℕ) : ℤ) ≤ y ∧
      y ≤ (N.toNat : ℕ) ∧ -((N.toNat : ℕ) : ℤ) ≤ z ∧ z ≤ (N.toNat : ℕ) := by
  unfold PSet at h
  rcases h with ⟨hs, -⟩ | ⟨hx0, -, hs, -⟩
  · obtain ⟨b1, b2, b3⟩ := hs.1.le
    have p1 := hs.1.1
    have p2 := hs.1.2.1
    have p3 := hs.1.2.2.1
    omega
  · obtain ⟨b1, b2, b3⟩ := hs.1.le
    have p1 := hs.1.1
    have p2 := hs.1.2.1
    have p3 := hs.1.2.2.1
    omega

theorem PSet.odd {N x y z : ℤ} (h : PSet N x y z) : x % 2 = 1 ∧ y % 2 = 1 ∧ z % 2 = 1 := by
  unfold PSet at h
  rcases h with ⟨hs, -⟩ | ⟨hx0, -, hs, -⟩
  · exact ⟨hs.1.2.2.2.1, hs.1.2.2.2.2.1, hs.1.2.2.2.2.2.1⟩
  · have o1 := hs.1.2.2.2.1
    exact ⟨by omega, hs.1.2.2.2.2.1, hs.1.2.2.2.2.2.1⟩

/-- If there is no good triple and all primitive symmetric triples `(v, a, a)` with
`v ≡ 2 (mod 3)` are of type III⁺, the set `PSet` is closed under the linear map `A`. -/
theorem PSet.stepA {N : ℤ}
    (hcon : ∀ v a b : ℤ, IsS N v a b → (v % 3 = 2 ∨ v = 1) → a = b)
    (hno : ∀ v a : ℤ, IsPS N v a a → v % 3 = 2 → (a - v) % 4 ≠ 0 ∧ v < a)
    {x y z : ℤ} (h : PSet N x y z) : PSet N ((3 * y - x) / 2) ((y + x) / 2) z := by
  unfold PSet at h ⊢
  rcases h with ⟨hs, hx1⟩ | ⟨hx0, hyz, hs, hx2⟩
  · obtain ⟨hv0, ha0, -, hvo, hao, -, -, -⟩ := hs.1
    obtain ⟨v', a', hx', c⟩ := hs.stepA
    obtain ⟨hv'0, ha'0, -, hv'o, ha'o, -, -, -⟩ := hx'.1
    rcases c with ⟨_, _, e1, e2⟩ | ⟨_, _, e1, e2⟩ | ⟨_, _, e1, e2⟩ | ⟨_, _, e1, e2⟩
    · have E1 : (3 * y - x) / 2 = v' := by omega
      have E2 : (y + x) / 2 = a' := by omega
      rw [E1, E2]
      exact Or.inl ⟨hx', by omega⟩
    · have hsym := hcon _ _ _ hx'.1 (Or.inl (by omega))
      have E1 : (3 * y - x) / 2 = -v' := by omega
      have E2 : (y + x) / 2 = a' := by omega
      rw [E1, E2]
      refine Or.inr ⟨by omega, hsym, ?_, ?_⟩
      · rw [neg_neg]; exact hx'
      · rw [neg_neg]; omega
    · exfalso
      have hsym := hcon _ _ _ hx'.1 (Or.inl (by omega))
      rw [← hsym] at hx'
      obtain ⟨t1, t2⟩ := hno v' a' hx' (by omega)
      omega
    · exfalso
      have hsym := hcon _ _ _ hx'.1 (Or.inl (by omega))
      rw [← hsym] at hx'
      obtain ⟨t1, t2⟩ := hno v' a' hx' (by omega)
      omega
  · subst hyz
    obtain ⟨t1, t2⟩ := hno (-x) y hs hx2
    obtain ⟨hv0, ha0, -, hvo, hao, -, -, -⟩ := hs.1
    obtain ⟨v', a', hx', c⟩ := hs.stepA
    rcases c with ⟨_, _, e1, e2⟩ | ⟨_, _, e1, e2⟩ | ⟨_, _, e1, e2⟩ | ⟨_, _, e1, e2⟩
    · exfalso; omega
    · exfalso; omega
    · have E1 : (3 * y - x) / 2 = v' := by omega
      have E2 : (y + x) / 2 = a' := by omega
      rw [E1, E2]
      exact Or.inl ⟨hx', by omega⟩
    · exfalso; omega

/-- **Theorem 6.1.** If `N ≠ 7` and `v² + 3a² + 3b² = N` has a primitive solution in odd
positive integers, then it has a solution with `a ≠ b` and `v ≡ 2 (mod 3)` or `v = 1`. -/
theorem exists_good {N v a b : ℤ} (h : IsS N v a b) (hp : Prim v a b) (hN : N ≠ 7) :
    ∃ v' a' b', IsS N v' a' b' ∧ (v' % 3 = 2 ∨ v' = 1) ∧ a' ≠ b' := by
  by_contra hcon0
  have hcon : ∀ v a b : ℤ, IsS N v a b → (v % 3 = 2 ∨ v = 1) → a = b := by
    intro v a b hS hl
    by_contra hne
    exact hcon0 ⟨v, a, b, hS, hl, hne⟩
  -- all primitive symmetric triples with `v ≡ 2` are of type III⁺
  have hno : ∀ v a : ℤ, IsPS N v a a → v % 3 = 2 → (a - v) % 4 ≠ 0 ∧ v < a := by
    intro v a hs hv2
    obtain ⟨hv0, ha0, -, hvo, hao, -, hv3, -⟩ := hs.1
    by_cases h4 : (a - v) % 4 = 0
    · exfalso
      rcases lt_or_gt_of_ne (show v ≠ 3 * a by omega) with hlt | hgt
      · -- type I: `α(s)` would be good
        obtain ⟨v', a', hx, c⟩ := hs.stepA
        rcases c with ⟨_, _, e1, e2⟩ | ⟨_, _, e1, e2⟩ | ⟨_, _, e1, e2⟩ | ⟨_, _, e1, e2⟩
        · have hsym := hcon _ _ _ hx.1 (Or.inl (by omega))
          have hva : a = v := by omega
          exact hs.2 v (by omega) dvd_rfl ⟨1, by omega⟩ ⟨1, by omega⟩
        · omega
        · omega
        · omega
      · exact typeII_false hcon hs hv2 h4 hgt
    · refine ⟨h4, ?_⟩
      by_contra hge
      exact typeIIIm_false hcon hs hv2 h4 (by omega)
  -- hence every element of `PSet` is diagonal
  have hdiag : ∀ x y z : ℤ, PSet N x y z → x = y ∧ y = z := fun x y z hP =>
    orbitS (PSet N) N.toNat (fun _ _ _ h' => h'.box) (fun _ _ _ h' => h'.odd)
      (fun _ _ _ h' => h'.stepA hcon hno) (fun _ _ _ h' => (h'.swap.stepA hcon hno).swap) hP
  obtain ⟨hv0, ha0, hb0, hvo, hao, hbo, hv3, heq⟩ := h
  have hS : IsS N v a b := ⟨hv0, ha0, hb0, hvo, hao, hbo, hv3, heq⟩
  rcases (show v % 3 = 1 ∨ v % 3 = 2 by omega) with h1 | h2
  · have hP : PSet N v a b := by
      unfold PSet
      exact Or.inl ⟨⟨hS, hp⟩, h1⟩
    obtain ⟨e1, e2⟩ := hdiag v a b hP
    have hv1 : v = 1 := by
      by_contra hne
      exact hp v (by omega) dvd_rfl ⟨1, by omega⟩ ⟨1, by omega⟩
    rw [show a = 1 by omega, show b = 1 by omega, hv1] at heq
    norm_num at heq
    omega
  · have hab := hcon v a b hS (Or.inl h2)
    subst hab
    have hP : PSet N (-v) a a := by
      unfold PSet
      exact Or.inr ⟨by omega, rfl, by rw [neg_neg]; exact ⟨hS, hp⟩, by rw [neg_neg]; exact h2⟩
    obtain ⟨e1, e2⟩ := hdiag (-v) a a hP
    omega

/-! ### A primitive starting point (Lemma 6.2) -/

theorem seedS_even_prim {N V A B : ℤ} (hN3 : N % 3 = 1) (hV : 0 ≤ V) (hB : 0 ≤ B)
    (hA0 : 0 < A) (heq : V ^ 2 + 3 * A ^ 2 + 3 * B ^ 2 = N) (hA1 : A % 2 = 1)
    (hV0 : V % 2 = 0) (hB0 : B % 2 = 0) (h4 : (V + B) % 4 = 2) (hp : Prim V A B) :
    ∃ v₁ b₁ : ℤ, IsS N v₁ A b₁ ∧ Prim v₁ A b₁ := by
  obtain ⟨v₁, h2⟩ : ∃ v₁ : ℤ, 2 * v₁ = 3 * B + V := ⟨(3 * B + V) / 2, by omega⟩
  rcases lt_or_gt_of_ne (show B ≠ V by omega) with hlt | hgt
  · obtain ⟨b₁, h1⟩ : ∃ b₁ : ℤ, 2 * b₁ = V - B := ⟨(V - B) / 2, by omega⟩
    have hn := normIII' h1 h2
    have heq' : v₁ ^ 2 + 3 * A ^ 2 + 3 * b₁ ^ 2 = N := by linarith
    refine ⟨v₁, b₁, ⟨by omega, hA0, by omega, by omega, hA1, by omega, mod3_S heq' hN3, heq'⟩, ?_⟩
    intro k hk kv kA kb
    have hko := odd_of_dvd_odd hA1 kA
    have k2B : k ∣ 2 * B := by
      have e : 2 * B = v₁ - b₁ := by linarith
      rw [e]; exact dvd_sub kv kb
    have k2V : k ∣ 2 * V := by
      have e : 2 * V = v₁ + 3 * b₁ := by linarith
      rw [e]; exact dvd_add kv (Dvd.dvd.mul_left kb 3)
    exact hp k hk (dvd_of_dvd_two_mul hko k2V) kA (dvd_of_dvd_two_mul hko k2B)
  · obtain ⟨b₁, h1⟩ : ∃ b₁ : ℤ, 2 * b₁ = B - V := ⟨(B - V) / 2, by omega⟩
    have hn := normIII h1 h2
    have heq' : v₁ ^ 2 + 3 * A ^ 2 + 3 * b₁ ^ 2 = N := by linarith
    refine ⟨v₁, b₁, ⟨by omega, hA0, by omega, by omega, hA1, by omega, mod3_S heq' hN3, heq'⟩, ?_⟩
    intro k hk kv kA kb
    have hko := odd_of_dvd_odd hA1 kA
    have k2B : k ∣ 2 * B := by
      have e : 2 * B = v₁ + b₁ := by linarith
      rw [e]; exact dvd_add kv kb
    have k2V : k ∣ 2 * V := by
      have e : 2 * V = v₁ - 3 * b₁ := by linarith
      rw [e]; exact dvd_sub kv (Dvd.dvd.mul_left kb 3)
    exact hp k hk (dvd_of_dvd_two_mul hko k2V) kA (dvd_of_dvd_two_mul hko k2B)

/-- **Lemma 6.2.** A primitive solution of `v² + 3a² + 3b² = N`, `N ≡ 7 (mod 24)`, gives a
primitive solution in odd positive integers. -/
theorem seedSP {N : ℤ} (hN : N % 24 = 7) {v a b : ℤ}
    (heq : v ^ 2 + 3 * a ^ 2 + 3 * b ^ 2 = N) (hprim : Int.gcd (Int.gcd v a) b = 1) :
    ∃ v' a' b', IsS N v' a' b' ∧ Prim v' a' b' := by
  have hp0 := prim_of_gcd hprim
  obtain ⟨V, hVd⟩ : ∃ V : ℤ, V = |v| := ⟨_, rfl⟩
  obtain ⟨A, hAd⟩ : ∃ A : ℤ, A = |a| := ⟨_, rfl⟩
  obtain ⟨B, hBd⟩ : ∃ B : ℤ, B = |b| := ⟨_, rfl⟩
  have hV : 0 ≤ V := hVd ▸ abs_nonneg v
  have hA : 0 ≤ A := hAd ▸ abs_nonneg a
  have hB : 0 ≤ B := hBd ▸ abs_nonneg b
  have hdvV : ∀ k : ℤ, k ∣ V → k ∣ v := fun k h => (dvd_abs k v).mp (hVd ▸ h)
  have hdvA : ∀ k : ℤ, k ∣ A → k ∣ a := fun k h => (dvd_abs k a).mp (hAd ▸ h)
  have hdvB : ∀ k : ℤ, k ∣ B → k ∣ b := fun k h => (dvd_abs k b).mp (hBd ▸ h)
  have hpVAB : Prim V A B := fun k hk h1 h2 h3 => hp0 k hk (hdvV k h1) (hdvA k h2) (hdvB k h3)
  have heq' : V ^ 2 + 3 * A ^ 2 + 3 * B ^ 2 = N := by
    rw [hVd, hAd, hBd, sq_abs, sq_abs, sq_abs]; exact heq
  have hN3 : N % 3 = 1 := by omega
  have pattern : (V % 2 = 1 ∧ A % 2 = 1 ∧ B % 2 = 1) ∨
      (A % 2 = 1 ∧ V % 2 = 0 ∧ B % 2 = 0 ∧ (V + B) % 4 = 2) ∨
      (B % 2 = 1 ∧ V % 2 = 0 ∧ A % 2 = 0 ∧ (V + A) % 4 = 2) := by
    rcases sq_mod8 V with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;>
    rcases sq_mod8 A with ⟨h2, h2'⟩ | ⟨h2, h2'⟩ | ⟨h2, h2'⟩ <;>
    rcases sq_mod8 B with ⟨h3, h3'⟩ | ⟨h3, h3'⟩ | ⟨h3, h3'⟩ <;> omega
  rcases pattern with ⟨h1, h2, h3⟩ | ⟨h2, h1, h3, h4⟩ | ⟨h3, h1, h2, h4⟩
  · exact ⟨V, A, B, ⟨by omega, by omega, by omega, h1, h2, h3, mod3_S heq' hN3, heq'⟩, hpVAB⟩
  · obtain ⟨v₁, b₁, hS, hP⟩ :=
      seedS_even_prim hN3 hV hB (by omega : 0 < A) heq' h2 h1 h3 h4 hpVAB
    exact ⟨v₁, A, b₁, hS, hP⟩
  · have heq'' : V ^ 2 + 3 * B ^ 2 + 3 * A ^ 2 = N := by linarith
    obtain ⟨v₁, a₁, hS, hP⟩ :=
      seedS_even_prim hN3 hV hA (by omega : 0 < B) heq'' h3 h1 h2 h4 hpVAB.swap
    exact ⟨v₁, a₁, B, hS.swap, hP.swap⟩

/-! ### Theorem 1.6 and the tuple `(3,-1,2,4,2,2)` -/

theorem repr_distinct (n : ℕ) {v a b : ℤ} (h : IsS (24 * n + 7) v a b)
    (hv : v % 3 = 2 ∨ v = 1) (hab : a ≠ b) :
    ∃ x r s : ℕ, r ≠ s ∧ n = x * (3 * x - 1) / 2 + r * (r + 1) / 2 + s * (s + 1) / 2 := by
  obtain ⟨hv0, ha0, hb0, hv2, ha2, hb2, -, heq⟩ := h
  obtain ⟨r, hr⟩ : ∃ r : ℕ, a = 2 * r + 1 := ⟨((a - 1) / 2).toNat, by omega⟩
  obtain ⟨s, hs⟩ : ∃ s : ℕ, b = 2 * s + 1 := ⟨((b - 1) / 2).toNat, by omega⟩
  have hrs : r ≠ s := by
    intro e
    apply hab
    rw [hr, hs, e]
  rcases hv with hv | rfl
  · obtain ⟨x, hx⟩ : ∃ x : ℕ, v = 6 * x - 1 := ⟨((v + 1) / 6).toNat, by omega⟩
    subst hr hs hx
    have h24 : (24 : ℤ) * n =
        12 * (x * (3 * x - 1)) + 12 * (r * (r + 1)) + 12 * (s * (s + 1)) := by
      linear_combination (-1 : ℤ) * heq
    have hN : 2 * n = x * (3 * x - 1) + r * (r + 1) + s * (s + 1) := by
      zify [show 1 ≤ 3 * x by omega]
      linarith
    obtain ⟨X, hX⟩ := even_pent x
    obtain ⟨R, hR⟩ := Nat.even_mul_succ_self r
    obtain ⟨S, hS⟩ := Nat.even_mul_succ_self s
    refine ⟨x, r, s, hrs, ?_⟩
    rw [hX, hR, hS] at hN ⊢
    omega
  · subst hr hs
    have h24 : (24 : ℤ) * n = 12 * (r * (r + 1)) + 12 * (s * (s + 1)) := by
      linear_combination (-1 : ℤ) * heq
    have hN : 2 * n = r * (r + 1) + s * (s + 1) := by
      zify
      linarith
    obtain ⟨R, hR⟩ := Nat.even_mul_succ_self r
    obtain ⟨S, hS⟩ := Nat.even_mul_succ_self s
    refine ⟨0, r, s, hrs, ?_⟩
    rw [hR, hS] at hN ⊢
    omega

/-- **Theorem 1.6.** Every positive integer is `x(3x-1)/2 + r(r+1)/2 + s(s+1)/2` with
`x r s : ℕ` and `r ≠ s`. -/
theorem pentagonal_two_distinct_triangular (hP : PrimRep133) (n : ℕ) (hn : 1 ≤ n) :
    ∃ x r s : ℕ, r ≠ s ∧ n = x * (3 * x - 1) / 2 + r * (r + 1) / 2 + s * (s + 1) / 2 := by
  obtain ⟨v, a, b, heq, hprim⟩ := hP (24 * n + 7) (by omega) (by omega)
  obtain ⟨v', a', b', hS, hp⟩ := seedSP (N := 24 * n + 7) (by omega) heq hprim
  obtain ⟨v'', a'', b'', hS', hl, hne⟩ := exists_good hS hp (by omega)
  exact repr_distinct n hS' hl hne

/-- A sum of two triangular numbers with different indices is `r(r+1) + s²` with `s ≥ 1`. -/
theorem two_tri_distinct (y z : ℕ) (hyz : y ≠ z) :
    ∃ r s : ℕ, 1 ≤ s ∧ y * (y + 1) / 2 + z * (z + 1) / 2 = r * (r + 1) + s ^ 2 := by
  have aux : ∀ y z : ℕ, z < y →
      ∃ r s : ℕ, 1 ≤ s ∧ y * (y + 1) / 2 + z * (z + 1) / 2 = r * (r + 1) + s ^ 2 := by
    intro y z hzy
    obtain ⟨Y, hY⟩ := Nat.even_mul_succ_self y
    obtain ⟨Z, hZ⟩ := Nat.even_mul_succ_self z
    rcases Nat.even_or_odd (y - z) with ⟨k, hk⟩ | ⟨k, hk⟩
    · have hy : y = z + k + k := by omega
      have hk1 : 1 ≤ k := by omega
      subst hy
      have key : (z + k + k) * (z + k + k + 1) + z * (z + 1) =
          2 * ((z + k) * (z + k + 1) + k ^ 2) := by
        ring
      refine ⟨z + k, k, hk1, ?_⟩
      rw [hY, hZ] at *
      omega
    · have hy : y = z + 2 * k + 1 := by omega
      subst hy
      have key : (z + 2 * k + 1) * (z + 2 * k + 1 + 1) + z * (z + 1) =
          2 * (k * (k + 1) + (z + k + 1) ^ 2) := by
        ring
      refine ⟨k, z + k + 1, by omega, ?_⟩
      rw [hY, hZ] at *
      omega
  rcases lt_or_gt_of_ne hyz with h | h
  · obtain ⟨r, s, hs, hrs⟩ := aux z y h
    exact ⟨r, s, hs, by omega⟩
  · exact aux y z h

/-- The tuple `(3,-1,2,4,2,2)`: every natural number is `x(3x-1)/2 + y(y+2) + z(z+1)`. -/
theorem tuple_3_m1_2_4_2_2 (hP : PrimRep133) (n : ℕ) :
    ∃ x y z : ℕ, n = x * (3 * x - 1) / 2 + y * (y + 2) + z * (z + 1) := by
  obtain ⟨x, r, s, hrs, h⟩ := pentagonal_two_distinct_triangular hP (n + 1) (by omega)
  obtain ⟨z, w, hw, hzw⟩ := two_tri_distinct r s hrs
  obtain ⟨y, rfl⟩ : ∃ y, w = y + 1 := ⟨w - 1, by omega⟩
  have e : (y + 1) ^ 2 = y * (y + 2) + 1 := by ring
  exact ⟨x, y, z, by omega⟩

end TriPent

#print axioms TriPent.exists_other_residue
#print axioms TriPent.exists_mixed
#print axioms TriPent.two_triangular_pentagonal
#print axioms TriPent.two_triangular_second_pentagonal
#print axioms TriPent.triangular_two_pentagonal_mixed
#print axioms TriPent.family_m1
#print axioms TriPent.family_p1
#print axioms TriPent.family_p5
#print axioms TriPent.tuple_3_m1_2_2_2_0
#print axioms TriPent.tuple_3_1_2_2_2_0
#print axioms TriPent.tuple_3_5_2_2_2_0
#print axioms TriPent.tuple_3_5_3_1_1_1
#print axioms TriPent.exists_residue1_gt
#print axioms TriPent.exists_high_low
#print axioms TriPent.tuple_3_7_1_1_1_1
#print axioms TriPent.tuple_3_7_2_2_2_0
#print axioms TriPent.tuple_3_7_3_m1_1_1
#print axioms TriPent.exists_good
#print axioms TriPent.pentagonal_two_distinct_triangular
#print axioms TriPent.tuple_3_m1_2_4_2_2
