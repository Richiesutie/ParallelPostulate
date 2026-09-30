/-
Copyright (c) 2026 Richard Sutton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Sutton
-/
import ParallelPostulate.Hilbert.Model

/-!
# The axioms of continuity in the plane of a bound

The plane of every bound that is not positive meets Dedekind's axiom and Archimedes' axiom. A
line is an interval of numbers, so Dedekind's axiom is the least upper bound of the real
numbers. Archimedes' axiom follows from a length of segments that adds along a segment: Klein's
distance under a negative bound, and the square root of `apart` under the bound 0.

## Contents

* a cut of an interval of real numbers: `cut_point_ordered`, `cut_point`
* Dedekind's axiom in the plane of a bound: `model_dedekind`
* Archimedes' axiom in the plane of a bound: `archimedes_of_length`, `model_archimedes`
-/

namespace Hilbert

open Pairs HyperbolicPlane

/-! ## A cut of an interval of real numbers -/

/-- A cut of an interval, with the first part below the second, has one cut point. -/
theorem cut_point_ordered {I S T : Set ℝ} (hI : ∀ a ∈ I, ∀ b ∈ I, ∀ c, a ≤ c → c ≤ b → c ∈ I)
    (hST : ∀ t, t ∈ I ↔ t ∈ S ∨ t ∈ T) (hSne : S.Nonempty) (hTne : T.Nonempty)
    (hsep : ∀ s ∈ S, ∀ t ∈ T, s < t) :
    ∃! c, c ∈ I ∧ ∀ a ∈ S, ∀ b ∈ T, a ≠ c → b ≠ c → StrictBetween a c b := by
  obtain ⟨s0, hs0⟩ := hSne
  obtain ⟨t0, ht0⟩ := hTne
  have hbdd : BddAbove S := ⟨t0, fun s hs => (hsep s hs t0 ht0).le⟩
  have hle : ∀ s ∈ S, s ≤ sSup S := fun s hs => le_csSup hbdd hs
  have hge : ∀ t ∈ T, sSup S ≤ t := fun t ht => csSup_le ⟨s0, hs0⟩ fun s hs => (hsep s hs t ht).le
  have hcI : sSup S ∈ I :=
    hI s0 ((hST s0).mpr (Or.inl hs0)) t0 ((hST t0).mpr (Or.inr ht0)) _ (hle s0 hs0) (hge t0 ht0)
  refine ⟨sSup S, ⟨hcI, fun a ha b hb hac hbc =>
    Or.inl ⟨lt_of_le_of_ne (hle a ha) hac, lt_of_le_of_ne (hge b hb) hbc.symm⟩⟩, ?_⟩
  rintro c' ⟨hc'I, hc'⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨s, hs, hcs⟩ := exists_lt_of_lt_csSup ⟨s0, hs0⟩ hlt
    have ht0c : c' < t0 := lt_of_lt_of_le hlt (hge t0 ht0)
    rcases hc' s hs t0 ht0 hcs.ne' ht0c.ne' with ⟨h1, -⟩ | ⟨h1, -⟩ <;> linarith
  · set m := (sSup S + c') / 2 with hm
    have hm1 : sSup S < m := by linarith
    have hm2 : m < c' := by linarith
    have hmI : m ∈ I := hI _ hcI _ hc'I m hm1.le hm2.le
    have hmT : m ∈ T := by
      rcases (hST m).mp hmI with h | h
      · exact absurd (hle m h) (not_le.mpr hm1)
      · exact h
    have hs0c : s0 < c' := lt_of_le_of_lt (hle s0 hs0) hgt
    rcases hc' s0 hs0 m hmT hs0c.ne hm2.ne with ⟨-, h2⟩ | ⟨-, h2⟩ <;> linarith

/-- **A cut of an interval of real numbers has one cut point.** -/
theorem cut_point {I S T : Set ℝ} (hI : ∀ a ∈ I, ∀ b ∈ I, ∀ c, a ≤ c → c ≤ b → c ∈ I)
    (hST : ∀ t, t ∈ I ↔ t ∈ S ∨ t ∈ T) (hdisj : ∀ t ∈ S, t ∉ T) (hSne : S.Nonempty)
    (hTne : T.Nonempty) (hS : ∀ x ∈ S, ∀ y ∈ T, ∀ z ∈ T, ¬ StrictBetween y x z)
    (hT : ∀ x ∈ T, ∀ y ∈ S, ∀ z ∈ S, ¬ StrictBetween y x z) :
    ∃! c, c ∈ I ∧ ∀ a ∈ S, ∀ b ∈ T, a ≠ c → b ≠ c → StrictBetween a c b := by
  obtain ⟨s0, hs0⟩ := hSne
  obtain ⟨t0, ht0⟩ := hTne
  have hst0 : s0 ≠ t0 := fun e => hdisj s0 hs0 (e ▸ ht0)
  rcases lt_or_gt_of_ne hst0 with hlt | hgt
  · apply cut_point_ordered hI hST ⟨s0, hs0⟩ ⟨t0, ht0⟩
    intro s hs t ht
    by_contra hts
    have hts' : t < s := lt_of_le_of_ne (not_lt.mp hts) (fun e => hdisj s hs (e ▸ ht))
    have hts0 : t ≠ s0 := fun e => hdisj s0 hs0 (e ▸ ht)
    rcases lt_or_gt_of_ne hts0 with h | h
    · exact hS s0 hs0 t ht t0 ht0 (Or.inl ⟨h, hlt⟩)
    · exact hT t ht s0 hs0 s hs (Or.inl ⟨h, hts'⟩)
  · have hST' : ∀ t, t ∈ I ↔ t ∈ T ∨ t ∈ S := fun t => (hST t).trans or_comm
    have hsep : ∀ t ∈ T, ∀ s ∈ S, t < s := by
      intro t ht s hs
      by_contra hst
      have hst' : s < t := lt_of_le_of_ne (not_lt.mp hst) (fun e => hdisj s hs (e ▸ ht))
      have hts0 : t ≠ s0 := fun e => hdisj s0 hs0 (e ▸ ht)
      rcases lt_or_gt_of_ne hts0 with h | h
      · exact hT t ht s hs s0 hs0 (Or.inl ⟨hst', h⟩)
      · exact hS s0 hs0 t0 ht0 t ht (Or.inl ⟨hgt, h⟩)
    obtain ⟨c, ⟨hcI, hc⟩, huniq⟩ := cut_point_ordered hI hST' ⟨t0, ht0⟩ ⟨s0, hs0⟩ hsep
    have hsymm : ∀ a c b : ℝ, StrictBetween a c b ↔ StrictBetween b c a :=
      fun _ _ _ => or_comm
    refine ⟨c, ⟨hcI, fun a ha b hb hac hbc => (hsymm _ _ _).mpr (hc b hb a ha hbc hac)⟩, ?_⟩
    rintro c' ⟨hc'I, hc'⟩
    exact huniq c' ⟨hc'I, fun b hb a ha hbc hac => (hsymm _ _ _).mpr (hc' a ha b hb hac hbc)⟩

/-! ## Dedekind's axiom in the plane of a bound -/

/-- **Dedekind's axiom holds in the plane of a bound that is not positive.** -/
theorem model_dedekind (κ : ℝ) (hκ : κ ≤ 0) : (model κ hκ).Dedekind := by
  intro l S T hST hdisj hSne hTne hS hT
  obtain ⟨M, hM, hl, -⟩ := l.2
  have hlies : ∀ X : Pt κ, (model κ hκ).lies X l ↔ X.1 ∈ M.points := by
    intro X
    change X.1 ∈ l.1 ↔ _
    rw [hl]
    exact ⟨fun h => h.1, fun h => ⟨h, X.2⟩⟩
  let I : Set ℝ := {t | M.pt t ∈ plane κ}
  let S' : Set ℝ := {t | ∃ h : M.pt t ∈ plane κ, (⟨M.pt t, h⟩ : Pt κ) ∈ S}
  let T' : Set ℝ := {t | ∃ h : M.pt t ∈ plane κ, (⟨M.pt t, h⟩ : Pt κ) ∈ T}
  have hpar : ∀ X : Pt κ, (model κ hκ).lies X l → ∃ t, ∃ h : M.pt t ∈ plane κ,
      X = ⟨M.pt t, h⟩ := by
    intro X hX
    obtain ⟨t, ht⟩ := (hlies X).mp hX
    exact ⟨t, ht ▸ X.2, Subtype.ext ht.symm⟩
  have hI : ∀ a ∈ I, ∀ b ∈ I, ∀ c, a ≤ c → c ≤ b → c ∈ I :=
    fun a ha b hb c hac hcb => pt_mem_plane_of_le M ha hb hac hcb
  have hST' : ∀ t, t ∈ I ↔ t ∈ S' ∨ t ∈ T' := by
    intro t
    constructor
    · intro h
      rcases (hST ⟨M.pt t, h⟩).mp ((hlies _).mpr ⟨t, rfl⟩) with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr ⟨h, h'⟩
    · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
  have hdisj' : ∀ t ∈ S', t ∉ T' := fun t ⟨h, hs⟩ ⟨_, ht⟩ => hdisj _ hs ht
  have hne' : ∀ {U : Set (Pt κ)} {U' : Set ℝ}, (∀ X ∈ U, (model κ hκ).lies X l) →
      U' = {t | ∃ h : M.pt t ∈ plane κ, (⟨M.pt t, h⟩ : Pt κ) ∈ U} → U.Nonempty →
      U'.Nonempty := by
    rintro U U' hU rfl ⟨X, hX⟩
    obtain ⟨t, h, rfl⟩ := hpar X (hU X hX)
    exact ⟨t, h, hX⟩
  have hSl : ∀ X ∈ S, (model κ hκ).lies X l := fun X hX => (hST X).mpr (Or.inl hX)
  have hTl : ∀ X ∈ T, (model κ hκ).lies X l := fun X hX => (hST X).mpr (Or.inr hX)
  have hS' : ∀ x ∈ S', ∀ y ∈ T', ∀ z ∈ T', ¬ StrictBetween y x z :=
    fun x ⟨hx, hxS⟩ y ⟨hy, hyT⟩ z ⟨hz, hzT⟩ h =>
      hS _ hxS _ hyT _ hzT (between_pt_of_strictBetween M hM h)
  have hT' : ∀ x ∈ T', ∀ y ∈ S', ∀ z ∈ S', ¬ StrictBetween y x z :=
    fun x ⟨hx, hxT⟩ y ⟨hy, hyS⟩ z ⟨hz, hzS⟩ h =>
      hT _ hxT _ hyS _ hzS (between_pt_of_strictBetween M hM h)
  obtain ⟨c, ⟨hcI, hc⟩, huniq⟩ := cut_point hI hST' hdisj' (hne' hSl rfl hSne)
    (hne' hTl rfl hTne) hS' hT'
  refine ⟨⟨M.pt c, hcI⟩, ⟨(hlies _).mpr ⟨c, rfl⟩, ?_⟩, ?_⟩
  · intro A hA B hB hAQ hBQ
    obtain ⟨a, ha, rfl⟩ := hpar A (hSl A hA)
    obtain ⟨b, hb, rfl⟩ := hpar B (hTl B hB)
    exact between_pt_of_strictBetween M hM (hc a ⟨ha, hA⟩ b ⟨hb, hB⟩
      (fun e => hAQ (by subst e; rfl)) (fun e => hBQ (by subst e; rfl)))
  · rintro Q ⟨hQl, hQ⟩
    obtain ⟨c', hc', rfl⟩ := hpar Q hQl
    have := huniq c' ⟨hc', fun a ⟨ha, hA⟩ b ⟨hb, hB⟩ hac hbc =>
      strictBetween_of_between_pt M hM (hQ _ hA _ hB
        (fun e => hac (M.pt_injective hM (congrArg Subtype.val e)))
        (fun e => hbc (M.pt_injective hM (congrArg Subtype.val e))))⟩
    subst this
    rfl

/-! ## Archimedes' axiom in the plane of a bound -/

/-- **Archimedes' axiom, from a length.** Suppose a length of segments of the plane is 0 for
a point and positive for two different points, adds along a segment, is equal for two segments
exactly when `apart` is, and takes every positive value on every ray. Then the plane meets
Archimedes' axiom. -/
theorem archimedes_of_length {κ : ℝ} (hκ : κ ≤ 0) (len : ℝ × ℝ → ℝ × ℝ → ℝ)
    (hcong : ∀ {P Q R S : ℝ × ℝ}, P ∈ plane κ → Q ∈ plane κ → R ∈ plane κ → S ∈ plane κ →
      (apart κ P Q = apart κ R S ↔ len P Q = len R S))
    (hadd : ∀ {A B C : ℝ × ℝ}, A ∈ plane κ → C ∈ plane κ → Between A B C →
      len A C = len A B + len B C)
    (hpos : ∀ {P Q : ℝ × ℝ}, P ∈ plane κ → Q ∈ plane κ → P ≠ Q → 0 < len P Q)
    (hzero : ∀ {P : ℝ × ℝ}, P ∈ plane κ → len P P = 0)
    (hexist : ∀ {O D : ℝ × ℝ}, O ∈ plane κ → O ≠ D → ∀ d, 0 < d →
      ∃ t, 0 < t ∧ (Dim.mk O D).pt t ∈ plane κ ∧ len O ((Dim.mk O D).pt t) = d) :
    (model κ hκ).Archimedes := by
  intro A B C D hAB hCD
  have hAB' : A.1 ≠ B.1 := fun e => hAB (Subtype.ext e)
  have hM : (Dim.mk A.1 B.1).zero ≠ (Dim.mk A.1 B.1).one := hAB'
  have hpt0 : (Dim.mk A.1 B.1).pt 0 = A.1 := Dim.pt_zero _
  have hpt1 : (Dim.mk A.1 B.1).pt 1 = B.1 := Dim.pt_one _
  have hδ : 0 < len C.1 D.1 := hpos C.2 D.2 (fun e => hCD (Subtype.ext e))
  have hch : ∀ i : ℕ, ∃ t, 0 < t ∧ (Dim.mk A.1 B.1).pt t ∈ plane κ ∧
      len A.1 ((Dim.mk A.1 B.1).pt t) = ((i : ℝ) + 1) * len C.1 D.1 :=
    fun i => hexist A.2 hAB' _ (by positivity)
  choose u hu0 hum hul using hch
  let σ : ℕ → ℝ := fun i => match i with
    | 0 => 0
    | i + 1 => u i
  have hσm : ∀ i, (Dim.mk A.1 B.1).pt (σ i) ∈ plane κ := by
    rintro (_ | i)
    · change (Dim.mk A.1 B.1).pt 0 ∈ plane κ
      rw [hpt0]
      exact A.2
    · exact hum i
  have hσl : ∀ i : ℕ, len A.1 ((Dim.mk A.1 B.1).pt (σ i)) = (i : ℝ) * len C.1 D.1 := by
    rintro (_ | i)
    · change len A.1 ((Dim.mk A.1 B.1).pt 0) = _
      rw [hpt0, hzero A.2]
      simp
    · change len A.1 ((Dim.mk A.1 B.1).pt (u i)) = _
      rw [hul i]
      push_cast
      ring
  have hσ0 : ∀ i, 0 ≤ σ i := by
    rintro (_ | i)
    · exact le_rfl
    · exact (hu0 i).le
  have hmono : ∀ s t : ℝ, 0 ≤ t → (Dim.mk A.1 B.1).pt s ∈ plane κ →
      (Dim.mk A.1 B.1).pt t ∈ plane κ →
      len A.1 ((Dim.mk A.1 B.1).pt s) < len A.1 ((Dim.mk A.1 B.1).pt t) → s < t := by
    intro s t ht hsm htm hlt
    by_contra hts
    rcases (not_lt.mp hts).eq_or_lt with e | e
    · rw [e] at hlt
      exact lt_irrefl _ hlt
    · rcases ht.eq_or_lt with e0 | e0
      · rw [← e0, hpt0, hzero A.2] at hlt
        rw [← e0] at e
        have hne : A.1 ≠ (Dim.mk A.1 B.1).pt s :=
          fun h => e.ne (Dim.pt_injective _ hM (hpt0.trans h))
        linarith [hpos A.2 hsm hne]
      · have hb := between_pt_of_strictBetween (Dim.mk A.1 B.1) hM (Or.inl ⟨e0, e⟩)
        rw [hpt0] at hb
        have hsum := hadd A.2 hsm hb
        have hne : (Dim.mk A.1 B.1).pt t ≠ (Dim.mk A.1 B.1).pt s :=
          fun h => e.ne (Dim.pt_injective _ hM h)
        linarith [hpos htm hsm hne]
  have hσlt : ∀ i j : ℕ, i < j → σ i < σ j := by
    intro i j hij
    apply hmono _ _ (hσ0 j) (hσm i) (hσm j)
    rw [hσl, hσl]
    exact mul_lt_mul_of_pos_right (by exact_mod_cast hij) hδ
  let X : ℕ → Pt κ := fun i => ⟨(Dim.mk A.1 B.1).pt (σ i), hσm i⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (len A.1 B.1 / len C.1 D.1)
  refine ⟨n, X, Subtype.ext hpt0, ?_, ?_, ?_, ?_⟩
  · intro i _
    change apart κ C.1 D.1 = apart κ ((Dim.mk A.1 B.1).pt (σ i)) ((Dim.mk A.1 B.1).pt (σ (i + 1)))
    rw [hcong C.2 D.2 (hσm i) (hσm (i + 1))]
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · have h1 := hσl 1
      change len C.1 D.1 = len ((Dim.mk A.1 B.1).pt 0) ((Dim.mk A.1 B.1).pt (σ 1))
      rw [hpt0, h1]
      simp
    · have hb := between_pt_of_strictBetween (Dim.mk A.1 B.1) hM
        (Or.inl ⟨(hσlt 0 i hi : 0 < σ i), hσlt i (i + 1) (by omega)⟩)
      rw [hpt0] at hb
      have hsum := hadd A.2 (hσm (i + 1)) hb
      rw [hσl i, hσl (i + 1)] at hsum
      push_cast at hsum
      linarith
  · intro i _
    exact model_onRay_of hAB' ⟨σ (i + 1), hσlt 0 (i + 1) (by omega), rfl⟩
  · intro i _
    exact between_pt_of_strictBetween (Dim.mk A.1 B.1) hM
      (Or.inl ⟨hσlt i (i + 1) (by omega), hσlt (i + 1) (i + 2) (by omega)⟩)
  · left
    have hB1 : (Dim.mk A.1 B.1).pt 1 ∈ plane κ := by
      rw [hpt1]
      exact B.2
    have h1 : 1 < σ n := by
      apply hmono 1 (σ n) (hσ0 n) hB1 (hσm n)
      rw [hpt1, hσl]
      rwa [div_lt_iff₀ hδ] at hn
    have hb := between_pt_of_strictBetween (Dim.mk A.1 B.1) hM (Or.inl ⟨zero_lt_one, h1⟩)
    rw [hpt0, hpt1] at hb
    exact hb

/-- **Archimedes' axiom holds in the plane of a bound that is not positive.** Under a negative
bound the length is Klein's distance; under the bound 0 it is the square root of `apart`. -/
theorem model_archimedes (κ : ℝ) (hκ : κ ≤ 0) : (model κ hκ).Archimedes := by
  rcases hκ.lt_or_eq with h | rfl
  · have hk : 0 < √(-κ) := Real.sqrt_pos.mpr (neg_pos.mpr h)
    apply archimedes_of_length hκ (kleinDist κ)
    · intro P Q R S hP hQ hR hS
      exact apart_eq_iff_kleinDist_eq h hP hQ hR hS
    · intro A B C hA hC hABC
      exact (kleinDist_add_of_between h hA hC hABC).2
    · intro P Q hP hQ hPQ
      exact kleinDist_pos h hP hQ hPQ
    · intro P hP
      rw [kleinDist_eq_arsinh h hP hP, apart_self]
      simp
    · intro O D hO hOD d hd
      have hsinh : 0 < Real.sinh (√(-κ) * d) := Real.sinh_pos_iff.mpr (mul_pos hk hd)
      obtain ⟨t, ht, hX, hap⟩ := exists_onRay_apart h hO hOD
        (α := Real.sinh (√(-κ) * d) ^ 2 / (-κ)) (div_pos (by positivity) (neg_pos.mpr h))
      refine ⟨t, ht, hX, ?_⟩
      have e : -κ * (Real.sinh (√(-κ) * d) ^ 2 / (-κ)) = Real.sinh (√(-κ) * d) ^ 2 := by
        field_simp [h.ne]
      rw [kleinDist_eq_arsinh h hO hX, hap, e, Real.sqrt_sq hsinh.le, Real.arsinh_sinh]
      field_simp
  · apply archimedes_of_length hκ (fun P Q => √(apart 0 P Q))
    · intro P Q R S _ _ _ _
      exact (Real.sqrt_inj (apart_zero_nonneg _ _) (apart_zero_nonneg _ _)).symm
    · intro A B C _ _ hABC
      exact euclid_sqrt_apart_add hABC
    · intro P Q hP hQ hPQ
      exact Real.sqrt_pos.mpr (apart_pos hP hQ hPQ)
    · intro P _
      simp [apart_self]
    · intro O D _ hOD d hd
      have hV : 0 < (D.1 - O.1) ^ 2 + (D.2 - O.2) ^ 2 := by
        have hne : ((D.1 - O.1, D.2 - O.2) : ℝ × ℝ) ≠ (0, 0) := by
          intro e
          apply hOD
          have h1 := congrArg Prod.fst e
          have h2 := congrArg Prod.snd e
          simp only [] at h1 h2
          exact Prod.ext (by linarith) (by linarith)
        exact sq_add_sq_pos hne
      have hsV := Real.sqrt_pos.mpr hV
      refine ⟨d / √((D.1 - O.1) ^ 2 + (D.2 - O.2) ^ 2), div_pos hd hsV, mem_plane_zero _, ?_⟩
      have e : apart 0 O ((Dim.mk O D).pt (d / √((D.1 - O.1) ^ 2 + (D.2 - O.2) ^ 2)))
          = (d / √((D.1 - O.1) ^ 2 + (D.2 - O.2) ^ 2)) ^ 2
            * ((D.1 - O.1) ^ 2 + (D.2 - O.2) ^ 2) := by
        rw [apart_zero_bound]
        simp only [Dim.pt]
        ring
      change √(apart 0 O _) = d
      rw [e, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (div_pos hd hsV).le]
      field_simp

end Hilbert
