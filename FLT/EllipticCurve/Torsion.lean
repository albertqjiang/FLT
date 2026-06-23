/-
Copyright (c) 2024 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.Topology.Instances.ZMod
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import FLT.Deformations.RepresentationTheory.GaloisRep
/-!

See
https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/n-torsion.20or.20multiplication.20by.20n.20as.20an%20additive%20group%20hom/near/429096078

The main theorems in this file are part of the PhD thesis work of David Angdinata, one of KB's
PhD students. It would be great if anyone who is interested in working on these results
could talk to David first. Note that he has already made substantial progress.

-/

@[expose] public section

universe u

variable {k : Type u} [Field k] (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k]

open WeierstrassCurve WeierstrassCurve.Affine

open scoped DirectSum

/-- The `n`-torsion subgroup of an elliptic curve `E` over `k`: the kernel of multiplication
by `n` on the group of `k`-points of `E`. -/
abbrev WeierstrassCurve.nTorsion (n : ℕ) : Type u := Submodule.torsionBy ℤ (E⁄k).Point n

--variable (n : ℕ) in
--#synth AddCommGroup (E.nTorsion n)

-- not sure if this instance will cause more trouble than it's worth
noncomputable instance (n : ℕ) : Module (ZMod n) (E.nTorsion n) :=
  AddCommGroup.zmodModule <| by
  intro ⟨P, hP⟩
  simpa using hP

-- This theorem needs e.g. a theory of division polynomials. It's ongoing work of David Angdinata.
-- Please do not work on it without talking to KB and David first.
theorem WeierstrassCurve.n_torsion_finite {n : ℕ} (hn : 0 < n) : Finite (E.nTorsion n) := sorry

-- This theorem needs e.g. a theory of division polynomials. It's ongoing work of David Angdinata.
-- Please do not work on it without talking to KB and David first.
theorem WeierstrassCurve.n_torsion_card [IsSepClosed k] {n : ℕ} (hn : (n : k) ≠ 0) :
    Nat.card (E.nTorsion n) = n^2 := sorry

/-- The size of the n-torsion of ZMod m is gcd(m, n). -/
lemma card_torsionBy_zmod (m n : ℕ) (hm : 0 < m) :
    Nat.card (Submodule.torsionBy ℤ (ZMod m) n) = Nat.gcd m n := by
  haveI : NeZero m := NeZero.of_pos hm
  have h_card_ker : Nat.card (AddMonoidHom.ker (nsmulAddMonoidHom n : ZMod m →+ ZMod m)) = Nat.gcd m n := by
    calc
      Nat.card (AddMonoidHom.ker (nsmulAddMonoidHom n : ZMod m →+ ZMod m)) =
          (Nat.card (ZMod m)).gcd n := by
        simpa using IsAddCyclic.card_nsmulAddMonoidHom_ker (ZMod m) n
      _ = Nat.gcd m n := by simp
  have h_eq_mem : ∀ x, x ∈ Submodule.torsionBy ℤ (ZMod m) n ↔
      x ∈ AddMonoidHom.ker (nsmulAddMonoidHom n : ZMod m →+ ZMod m) := by
    intro x
    simp [AddMonoidHom.mem_ker]
  -- Both are subsets of ZMod m with the same underlying set, so the identity map gives a bijection
  let f : (Submodule.torsionBy ℤ (ZMod m) n) → (AddMonoidHom.ker (nsmulAddMonoidHom n : ZMod m →+ ZMod m)) :=
    fun x => ⟨x.1, ((h_eq_mem x.1).mp x.2)⟩
  have hf_bijective : Function.Bijective f := by
    constructor
    · intro a b h
      apply Subtype.ext
      have := congr_arg Subtype.val h
      simpa [f] using this
    · intro ⟨x, hx⟩
      refine ⟨⟨x, ((h_eq_mem x).mpr hx)⟩, ?_⟩
      rfl
  exact (Nat.card_congr (Equiv.ofBijective f hf_bijective)).trans h_card_ker

/-- If `f i ≤ e` for all `i` and the sum of `f i` over a fintype `ι`
equals `e * card ι`, then `f i = e` for all `i`. -/
lemma all_eq_of_sum_eq_mul_card {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℕ) (e : ℕ)
    (h_le : ∀ i, f i ≤ e) (h_sum : (∑ i, f i) = e * Fintype.card ι) : ∀ i, f i = e := by
  intro i
  by_contra! hi
  have h_lt : f i < e := Nat.lt_of_le_of_ne (h_le i) hi
  have hc : 1 ≤ Fintype.card ι := by
    by_contra! h
    have h0 : Fintype.card ι = 0 := by omega
    have : IsEmpty ι := Fintype.card_eq_zero_iff.mp h0
    exact this.false i
  have he_pos : 1 ≤ e := by
    have h0 : 0 < e := Nat.lt_of_le_of_lt (Nat.zero_le _) h_lt
    omega
  -- ∑ f j = f i + ∑_{j≠i} f j
  have h_sum_decomp : (∑ j, f j) = f i + Finset.sum (Finset.univ.erase i) f :=
    ((Finset.sum_erase_add Finset.univ f (Finset.mem_univ i)).symm.trans (add_comm _ _))
  -- ∑_{j≠i} f j ≤ (card-1)*e
  have h_erase_le : Finset.sum (Finset.univ.erase i) f ≤ (Fintype.card ι - 1) * e := by
    calc
      Finset.sum (Finset.univ.erase i) f ≤ Finset.sum (Finset.univ.erase i) (fun _ => e) :=
        Finset.sum_le_sum (fun j _ => h_le j)
      _ = (Finset.card (Finset.univ.erase i)) * e := by simp
      _ = (Fintype.card ι - 1) * e := by
        simp [Finset.card_erase_of_mem (Finset.mem_univ i)]
  -- Key identity: card*e = (card-1)*e + e (using card ≥ 1)
  have h_card_mul : Fintype.card ι * e = (Fintype.card ι - 1) * e + e := by
    calc
      Fintype.card ι * e = ((Fintype.card ι - 1) + 1) * e := by
        rw [Nat.sub_add_cancel hc]
      _ = (Fintype.card ι - 1) * e + 1 * e := by rw [Nat.add_mul]
      _ = (Fintype.card ι - 1) * e + e := by simp
  -- Combine: f i + sum + 1 ≤ card*e, but sum = card*e, contradiction
  have h_bound : f i + Finset.sum (Finset.univ.erase i) f + 1 ≤ Fintype.card ι * e := by
    calc
      f i + Finset.sum (Finset.univ.erase i) f + 1
          = (f i + 1) + Finset.sum (Finset.univ.erase i) f := by omega
      _ ≤ e + Finset.sum (Finset.univ.erase i) f := by
        omega
      _ ≤ e + (Fintype.card ι - 1) * e := Nat.add_le_add_left h_erase_le _
      _ = (Fintype.card ι - 1) * e + e := Nat.add_comm _ _
      _ = Fintype.card ι * e := by rw [h_card_mul]
  rw [← h_sum_decomp] at h_bound
  rw [h_sum, Nat.mul_comm e (Fintype.card ι)] at h_bound
  omega

/-- The natural equivalence `(∀ i, A i) × (∀ i, B i) ≃+ (∀ i, A i × B i)`. -/
def piProdAddEquiv {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : ι → Type*) [∀ i, AddCommGroup (A i)] [∀ i, AddCommGroup (B i)] :
    ((∀ i, A i) × (∀ i, B i)) ≃+ (∀ i, (A i × B i)) :=
  { toFun := λ ⟨f, g⟩ i => (f i, g i)
    invFun := λ h => (λ i => (h i).1, λ i => (h i).2)
    left_inv := λ ⟨f, g⟩ => by
      ext i <;> rfl
    right_inv := λ h => by
      ext i <;> rfl
    map_add' := λ x y => by
      rcases x with ⟨f, g⟩
      rcases y with ⟨f', g'⟩
      ext i <;> rfl }

/-- `AddEquiv.prodCongr` packaged as a top-level lemma for reuse. -/
def prodAddEquivCongr {M N P Q : Type*} [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup P] [AddCommGroup Q] (f : M ≃+ N) (g : P ≃+ Q) :
    (M × P) ≃+ (N × Q) :=
  AddEquiv.prodCongr f g


/-- The p-torsion of an `AddEquiv` gives an isomorphism of p-torsion subgroups. -/
def torsionByAddEquiv {M N : Type*} [AddCommGroup M] [AddCommGroup N] (f : M ≃+ N) (n : ℤ) :
    (Submodule.torsionBy ℤ M n) ≃+ (Submodule.torsionBy ℤ N n) :=
  { toFun := fun x => ⟨f x.1, by
      have hx : n • (x.1 : M) = 0 :=
        (Submodule.mem_torsionBy_iff n (x.1 : M)).mp x.2
      apply (Submodule.mem_torsionBy_iff n _).mpr
      have h_f_zsmul : n • (f x.1) = f (n • x.1) := by
        simpa using (f.toAddMonoidHom.map_zsmul n x.1).symm
      rw [h_f_zsmul, hx]
      simp
    ⟩
    invFun := fun y => ⟨f.symm y.1, by
      have hy : n • (y.1 : N) = 0 :=
        (Submodule.mem_torsionBy_iff n (y.1 : N)).mp y.2
      apply (Submodule.mem_torsionBy_iff n _).mpr
      have h_symm_zsmul : n • (f.symm y.1) = f.symm (n • y.1) := by
        simpa using (f.symm.toAddMonoidHom.map_zsmul n y.1).symm
      rw [h_symm_zsmul, hy]
      simp
    ⟩
    left_inv := fun x => by ext; simp
    right_inv := fun y => by ext; simp
    map_add' := fun x y => by ext; simp }

/-- The p-torsion of `∀ i, ZMod (ns i)` is isomorphic to `∀ i, Submodule.torsionBy ℤ (ZMod (ns i)) p`. -/
def piTorsionAddEquiv {ι : Type*} [Fintype ι] (ns : ι → ℕ) (p : ℤ) :
    (Submodule.torsionBy ℤ (∀ i, ZMod (ns i)) p) ≃+ (∀ i, Submodule.torsionBy ℤ (ZMod (ns i)) p) :=
  { toFun := fun f i => ⟨f.1 i, by
      have h := (Submodule.mem_torsionBy_iff p f.1).mp f.2
      have hi : p • (f.1 i) = 0 := by
        simpa [Pi.smul_apply] using congrArg (fun g => g i) h
      exact (Submodule.mem_torsionBy_iff p (f.1 i)).mpr hi
    ⟩
    invFun := fun g => ⟨fun i => (g i).1, by
      have h : ∀ i, p • ((g i).1 : ZMod (ns i)) = 0 := by
        intro i
        exact ((Submodule.mem_torsionBy_iff p ((g i).1 : ZMod (ns i))).mp (g i).2)
      have h' : p • (fun i => (g i).1 : ∀ i, ZMod (ns i)) = 0 := by
        ext i; simpa [Pi.smul_apply] using h i
      exact (Submodule.mem_torsionBy_iff p _).mpr h'
    ⟩
    left_inv := fun f => by ext i; rfl
    right_inv := fun g => by ext i; rfl
    map_add' := fun x y => by ext i; rfl }

theorem group_theory_lemma {A : Type*} [AddCommGroup A] {n : ℕ} (hn : 0 < n) (r : ℕ)
    (h : ∀ d : ℕ, d ∣ n → Nat.card (Submodule.torsionBy ℤ A d) = d ^ r) :
    Nonempty ((Submodule.torsionBy ℤ A n) ≃+ (Fin r → (ZMod n))) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn1 : n = 1
    · subst hn1
      apply Nonempty.intro
      have h_card_A : Nat.card (Submodule.torsionBy ℤ A 1) = 1 := by
        simpa using h 1 (by simp)
      have h_card_B : Nat.card (Fin r → ZMod 1) = 1 := by simp
      have h_subsingleton_A : Subsingleton (Submodule.torsionBy ℤ A 1) :=
        ((Nat.card_eq_one_iff_unique).mp h_card_A).1
      have h_subsingleton_B : Subsingleton (Fin r → ZMod 1) :=
        ((Nat.card_eq_one_iff_unique).mp h_card_B).1
      let f : Submodule.torsionBy ℤ A 1 →+ (Fin r → ZMod 1) :=
        { toFun := fun _ => 0
          map_add' := by intro x y; simp
          map_zero' := rfl }
      have h_inj : Function.Injective f := by
        intro x y h; exact Subsingleton.elim _ _
      have h_surj : Function.Surjective f := by
        intro y; refine ⟨0, ?_⟩; simpa [f] using Subsingleton.elim (f 0) y
      exact AddEquiv.ofBijective f ⟨h_inj, h_surj⟩
    · have hn_gt1 : 1 < n := by omega
      obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd hn1
      set pe := ordProj[p] n with hpe_def
      have hpe_pos : 0 < pe := by
        rw [hpe_def]
        exact pow_pos (Nat.Prime.pos hp_prime) _
      have hpe_dvd : pe ∣ n := by
        rw [hpe_def]
        exact Nat.ordProj_dvd n p
      set m := ordCompl[p] n with hm_def
      have hm_pos : 0 < m := by
        rw [hm_def]
        exact Nat.div_pos (Nat.le_of_dvd hn hpe_dvd) (pow_pos (Nat.Prime.pos hp_prime) _)
      have h_coprime : Nat.Coprime pe m := by
        rw [hpe_def, hm_def]
        exact (Nat.Prime.coprime_pow_of_not_dvd hp_prime
          (Nat.not_dvd_ordCompl hp_prime hn.ne.symm)).symm
      have h_prod : pe * m = n := by
        rw [hm_def, hpe_def]
        exact Nat.mul_div_cancel' (Nat.ordProj_dvd n p)
      have hm_dvd : m ∣ n := by
        rw [← h_prod]
        exact ⟨pe, mul_comm pe m⟩
      -- Cardinalities of the torsion subgroups
      have h_card_n : Nat.card (Submodule.torsionBy ℤ A n) = n ^ r := h n (dvd_refl n)
      have h_card_pe : Nat.card (Submodule.torsionBy ℤ A pe) = pe ^ r := h pe hpe_dvd
      have h_card_m : Nat.card (Submodule.torsionBy ℤ A m) = m ^ r := h m hm_dvd
      -- The product A[pe] × A[m] has cardinality n^r
      have h_card_prod : Nat.card ((Submodule.torsionBy ℤ A pe) × (Submodule.torsionBy ℤ A m)) = n ^ r := by
        rw [Nat.card_prod, h_card_pe, h_card_m, ← h_prod]
        simp [mul_pow]
      -- All three groups are finite (since their cardinality is positive)
      have h_fin_n : Finite (Submodule.torsionBy ℤ A n) :=
        Nat.finite_of_card_ne_zero (by
          rw [h_card_n]
          exact (pow_pos hn r).ne.symm)
      have h_fin_pe : Finite (Submodule.torsionBy ℤ A pe) :=
        Nat.finite_of_card_ne_zero (by
          rw [h_card_pe]
          exact (pow_pos hpe_pos r).ne.symm)
      have h_fin_m : Finite (Submodule.torsionBy ℤ A m) :=
        Nat.finite_of_card_ne_zero (by
          rw [h_card_m]
          exact (pow_pos hm_pos r).ne.symm)
      -- The intersection A[pe] ∩ A[m] is trivial
      have h_inter_trivial : Submodule.torsionBy ℤ A pe ⊓ Submodule.torsionBy ℤ A m = ⊥ := by
        refine eq_bot_iff.mpr fun x hx => ?_
        rcases Submodule.mem_inf.mp hx with ⟨hxp, hxm⟩
        have hxp_nat : (pe : ℕ) • (x : A) = 0 := by
          simpa using (Submodule.mem_torsionBy_iff (pe : ℤ) (x : A)).mp hxp
        have hxm_nat : (m : ℕ) • (x : A) = 0 := by
          simpa using (Submodule.mem_torsionBy_iff (m : ℤ) (x : A)).mp hxm
        have hx_zero : (x : A) = 0 :=
          ((nsmul_eq_zero_iff_of_coprime (a := (x : A)) h_coprime).mp ⟨hxp_nat, hxm_nat⟩)
        simpa [Submodule.mem_bot ℤ] using hx_zero
      -- The sum map φ_raw : A[pe] × A[m] → A
      let φ_raw : (Submodule.torsionBy ℤ A pe) × (Submodule.torsionBy ℤ A m) →+ A :=
        AddMonoidHom.coprod
          (Submodule.subtype (Submodule.torsionBy ℤ A pe))
          (Submodule.subtype (Submodule.torsionBy ℤ A m))
      -- Show φ_raw lands in A[n]
      have h_sum_mem (x : Submodule.torsionBy ℤ A pe) (y : Submodule.torsionBy ℤ A m) :
          (x : A) + (y : A) ∈ Submodule.torsionBy ℤ A n := by
        rw [Submodule.mem_torsionBy_iff]
        have hx : (pe : ℤ) • (x : A) = 0 := (Submodule.mem_torsionBy_iff (pe : ℤ) (x : A)).mp x.2
        have hy : (m : ℤ) • (y : A) = 0 := (Submodule.mem_torsionBy_iff (m : ℤ) (y : A)).mp y.2
        calc
          (n : ℤ) • ((x : A) + (y : A)) = ((pe * m : ℕ) : ℤ) • ((x : A) + (y : A)) := by
            simp [h_prod]
          _ = ((pe : ℤ) * (m : ℤ)) • (x : A) + ((pe : ℤ) * (m : ℤ)) • (y : A) := by
            rw [smul_add]; simp
          _ = (pe : ℤ) • ((m : ℤ) • (x : A)) + (pe : ℤ) • ((m : ℤ) • (y : A)) := by
            rw [mul_smul, mul_smul]
          _ = (m : ℤ) • ((pe : ℤ) • (x : A)) + (pe : ℤ) • ((m : ℤ) • (y : A)) := by
            have h_first : (pe : ℤ) • ((m : ℤ) • (x : A)) = (m : ℤ) • ((pe : ℤ) • (x : A)) := by
              calc
                (pe : ℤ) • ((m : ℤ) • (x : A)) = ((pe : ℤ) * (m : ℤ)) • (x : A) := by rw [mul_smul]
                _ = ((m : ℤ) * (pe : ℤ)) • (x : A) := by rw [mul_comm]
                _ = (m : ℤ) • ((pe : ℤ) • (x : A)) := by rw [mul_smul]
            rw [h_first]
          _ = (m : ℤ) • (0 : A) + (pe : ℤ) • (0 : A) := by rw [hx, hy]
          _ = 0 := by simp
      -- Restrict codomain to A[n]
      let φ : (Submodule.torsionBy ℤ A pe) × (Submodule.torsionBy ℤ A m) →+ (Submodule.torsionBy ℤ A n) :=
        AddMonoidHom.codRestrict φ_raw (Submodule.torsionBy ℤ A n) (fun p => h_sum_mem p.1 p.2)
      -- φ is injective because its kernel is trivial
      have h_inj : Function.Injective φ := by
        intro a b h_eq
        have h_sub_zero : φ (a - b) = 0 := by rw [map_sub, h_eq, sub_self]
        have h_sum_zero : ((a.1 : A) - (b.1 : A)) + ((a.2 : A) - (b.2 : A)) = 0 := by
          have h := congrArg (fun x : Submodule.torsionBy ℤ A n => (x : A)) h_sub_zero
          simpa [φ, φ_raw, AddMonoidHom.coprod_apply] using h
        have hxpa : (pe : ℤ) • (a.1 : A) = 0 :=
          (Submodule.mem_torsionBy_iff _ _).mp a.1.2
        have hxpb : (pe : ℤ) • (b.1 : A) = 0 :=
          (Submodule.mem_torsionBy_iff _ _).mp b.1.2
        have hxma : (m : ℤ) • (a.2 : A) = 0 :=
          (Submodule.mem_torsionBy_iff _ _).mp a.2.2
        have hxmb : (m : ℤ) • (b.2 : A) = 0 :=
          (Submodule.mem_torsionBy_iff _ _).mp b.2.2
        have h_mem_inter : (a.1 : A) - (b.1 : A) ∈ Submodule.torsionBy ℤ A pe ⊓ Submodule.torsionBy ℤ A m := by
          apply Submodule.mem_inf.mpr
          constructor
          · rw [Submodule.mem_torsionBy_iff, smul_sub, hxpa, hxpb, sub_self]
          · have h_mem_aux : (a.2 : A) - (b.2 : A) ∈ Submodule.torsionBy ℤ A m := by
              rw [Submodule.mem_torsionBy_iff, smul_sub, hxma, hxmb, sub_self]
            have h_eq' : (a.1 : A) - (b.1 : A) = -((a.2 : A) - (b.2 : A)) := by
              apply eq_neg_of_add_eq_zero_left
              rw [h_sum_zero]
            rw [h_eq']
            exact Submodule.neg_mem _ h_mem_aux
        rw [h_inter_trivial, Submodule.mem_bot] at h_mem_inter
        have hxp_eq : a.1 = b.1 := Subtype.ext (sub_eq_zero.mp h_mem_inter)
        have hxm_eq : a.2 = b.2 := Subtype.ext (sub_eq_zero.mp (by
          simpa [h_mem_inter] using h_sum_zero))
        exact Prod.ext hxp_eq hxm_eq
      have h_bijective : Function.Bijective φ :=
        ((Nat.bijective_iff_injective_and_card φ).mpr
          ⟨h_inj, by rw [h_card_prod, h_card_n]⟩)
      have h_isom : Nonempty ((Submodule.torsionBy ℤ A pe) × (Submodule.torsionBy ℤ A m) ≃+ (Submodule.torsionBy ℤ A n)) :=
        ⟨AddEquiv.ofBijective φ h_bijective⟩
      -- If m = 1, then n = pe and we are in the prime power case
      by_cases hm1 : m = 1
      · -- Then n = pe, use h_isom directly
        rw [hm1, mul_one] at h_prod
        -- Now h_prod : pe = n
        have hn_eq_pe : n = pe := h_prod.symm
        rw [hn_eq_pe]
        -- We are in the case n = pe (a prime power). Goal: A[pe] ≃+ (Fin r → ZMod pe)
        -- Use the structure theorem for finite abelian groups
        have h_decomp : ∃ (ι : Type) (_ : Fintype ι) (ns : ι → ℕ),
            (∀ i, 1 < ns i) ∧ Nonempty (Submodule.torsionBy ℤ A pe ≃+ ⨁ i, ZMod (ns i)) :=
          AddCommGroup.equiv_directSum_zmod_of_finite' (Submodule.torsionBy ℤ A pe)
        rcases h_decomp with ⟨ι, hι, ns, hns_gt1, h_iso_decomp⟩
        haveI : Fintype ι := hι
        have h_iso := h_iso_decomp.some
        -- |A[pe]| = pe^r, so the direct sum also has size pe^r
        have h_card_ds : Nat.card (⨁ i, ZMod (ns i)) = pe ^ r := by
          rw [← h_card_pe, Nat.card_congr h_iso.symm.toEquiv]
        -- Use DirectSum.addEquivProd to relate direct sum to pi type
        let h_iso_pi : (⨁ i, ZMod (ns i)) ≃+ (∀ i, ZMod (ns i)) :=
          (DirectSum.linearEquivFunOnFintype ℤ ι (fun i => ZMod (ns i))).toAddEquiv
        have h_card_pi : Nat.card (∀ i, ZMod (ns i)) = pe ^ r := by
          rw [← h_card_ds, Nat.card_congr h_iso_pi.toEquiv]
        -- Product of ns i equals pe^r
        have h_prod_n : (∏ i, ns i) = pe ^ r := by
          rw [← h_card_pi, Nat.card_pi]
          refine Finset.prod_congr rfl fun i _ => ?_
          simp
        -- pe = p^e for e = factorization pe > 0
        have hp_dvd_pe : p ∣ pe := by
          rw [hpe_def]
          have h_exp_pos : 0 < n.factorization p :=
            Nat.Prime.factorization_pos_of_dvd hp_prime hn.ne.symm hp_dvd
          have h_one_le : 1 ≤ n.factorization p := by omega
          have := pow_dvd_pow p h_one_le
          simpa [pow_one] using this
        have he_pos : 0 < Nat.factorization pe p :=
          Nat.Prime.factorization_pos_of_dvd hp_prime (by
            rw [hpe_def]
            exact pow_ne_zero _ (Nat.Prime.ne_zero hp_prime)) hp_dvd_pe
        set e := Nat.factorization pe p with he_def
        have hpe_eq : pe = p ^ e := by
          rw [hpe_def, he_def, Nat.factorization_pow_self hp_prime]
        -- Therefore ∏ ns i = p^(e*r)
        have h_prod_pow : (∏ i, ns i) = p ^ (e * r) := by
          rw [h_prod_n, hpe_eq, pow_mul]
        -- Each ns i is a power of p (since the product is a power of p)
        have h_ns_pow_p : ∀ i, ∃ f, ns i = p ^ f := by
          intro i
          have h_dvd : ns i ∣ p ^ (e * r) := by
            rw [← h_prod_pow]
            exact Finset.dvd_prod_of_mem (fun j => ns j) (Finset.mem_univ i)
          rcases (Nat.dvd_prime_pow hp_prime).mp h_dvd with ⟨f, _, hf⟩
          exact ⟨f, hf⟩
        -- Get exponents f i such that ns i = p^(f i)
        let f : ι → ℕ := fun i => Classical.choose (h_ns_pow_p i)
        have hf : ∀ i, ns i = p ^ (f i) := fun i => Classical.choose_spec (h_ns_pow_p i)
        -- Each f i ≥ 1 (since ns i > 1)
        have hf_pos : ∀ i, 1 ≤ f i := by
          intro i
          by_contra! h
          have hf0 : f i = 0 := by omega
          have h1 : ns i = 1 := by rw [hf i, hf0, pow_zero]
          have h1_lt : 1 < ns i := hns_gt1 i
          omega
        -- ∑ f i = e * r, via p^(∑ f i) = ∏ p^(f i) = ∏ ns i = p^(e*r)
        have h_pow_eq : p ^ (∑ i, f i) = p ^ (e * r) := by
          have h_prod_f' : (∏ i, p ^ (f i)) = p ^ (∑ i, f i) := by
            simpa using Finset.prod_pow_eq_pow_sum Finset.univ f p
          calc
            p ^ (∑ i, f i) = (∏ i, p ^ (f i)) := by rw [h_prod_f']
            _ = (∏ i, ns i) := by simp [hf]
            _ = p ^ (e * r) := h_prod_pow
        have h_sum_f : (∑ i, f i) = e * r :=
          (Nat.pow_right_injective hp_prime.one_lt) h_pow_eq
        -- Now prove |ι| = r using p-torsion comparison.
        -- First, p divides each ns i (since ns i = p^(f i) with f i ≥ 1)
        have h_p_dvd_ns : ∀ i, p ∣ ns i := by
          intro i
          rw [hf i]
          have hpos : 0 < f i := Nat.lt_of_lt_of_le (by omega) (hf_pos i)
          exact dvd_pow_self p hpos.ne.symm
        -- Therefore gcd (ns i) p = p for each i
        have h_gcd_ns_p : ∀ i, Nat.gcd (ns i) p = p := by
          intro i
          rw [Nat.gcd_eq_right (h_p_dvd_ns i)]
        -- The p-torsion of ZMod (ns i) has cardinality gcd (ns i) p = p
        have h_card_torsion_ns : ∀ i, Nat.card (Submodule.torsionBy ℤ (ZMod (ns i)) (p : ℤ)) = p := by
          intro i
          have hpos : 0 < ns i := by
            have h1 : 1 < ns i := hns_gt1 i
            omega
          rw [card_torsionBy_zmod (ns i) p hpos, h_gcd_ns_p i]
        -- The p-torsion of the pi type (∀ i, ZMod (ns i)) has size p^|ι|
        have h_card_pi_torsion : Nat.card (Submodule.torsionBy ℤ (∀ i, ZMod (ns i)) (p : ℤ)) = p ^ (Fintype.card ι) :=
          calc
            Nat.card (Submodule.torsionBy ℤ (∀ i, ZMod (ns i)) (p : ℤ)) =
                Nat.card (∀ i, Submodule.torsionBy ℤ (ZMod (ns i)) (p : ℤ)) :=
              Nat.card_congr (piTorsionAddEquiv ns (p : ℤ))
            _ = ∏ i, Nat.card (Submodule.torsionBy ℤ (ZMod (ns i)) (p : ℤ)) := by rw [Nat.card_pi]
            _ = ∏ i, p := by
              refine Finset.prod_congr rfl fun i _ => ?_
              rw [h_card_torsion_ns i]
            _ = p ^ (Fintype.card ι) := by simp
        -- The p-torsion of A[pe] has size p^|ι| (via isomorphism with direct sum)
        have h_card_pe_torsion : Nat.card (Submodule.torsionBy ℤ (Submodule.torsionBy ℤ A pe) (p : ℤ)) = p ^ (Fintype.card ι) := by
          calc
            Nat.card (Submodule.torsionBy ℤ (Submodule.torsionBy ℤ A pe) (p : ℤ)) =
                Nat.card (Submodule.torsionBy ℤ (∀ i, ZMod (ns i)) (p : ℤ)) :=
              Nat.card_congr (torsionByAddEquiv (h_iso.trans (DirectSum.addEquivProd (fun i => ZMod (ns i)))) (p : ℤ))
            _ = p ^ (Fintype.card ι) := h_card_pi_torsion
        have h_card_p : Nat.card (Submodule.torsionBy ℤ A p) = p ^ r :=
          h p hp_dvd
        -- A[p] is contained in A[pe] because pe = p^e with e > 0
        have h_torsion_sub : Submodule.torsionBy ℤ A p ≤ Submodule.torsionBy ℤ A pe := by
          intro x hx
          rw [Submodule.mem_torsionBy_iff] at hx ⊢
          rw [hpe_eq]
          have he_pos' : 0 < e := by
            rw [he_def]
            exact he_pos
          obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero he_pos'.ne.symm
          rw [hk, pow_succ, Nat.cast_mul, mul_smul, hx, smul_zero]
        -- Therefore |ι| = r (via cardinality comparison of p-torsion subgroups)
        have h_card_ι : Fintype.card ι = r := by
          -- The p-torsion of A[pe] is isomorphic to A[p] (since A[p] ⊆ A[pe])
          have h_iso_torsion : (Submodule.torsionBy ℤ (Submodule.torsionBy ℤ A pe) (p : ℤ)) ≃+
              (Submodule.torsionBy ℤ A p) :=
            { toFun := fun x => ⟨x.1.1, by
                have hpx : (p : ℤ) • (x.1 : Submodule.torsionBy ℤ A pe) = 0 :=
                  (Submodule.mem_torsionBy_iff _ _).mp x.2
                have h_ann : (p : ℤ) • ((x.1).1 : A) = 0 := by
                  have hzero' := congrArg (fun (z : Submodule.torsionBy ℤ A pe) => (z : A)) hpx
                  rw [Submodule.coe_smul] at hzero'
                  simpa using hzero'
                exact (Submodule.mem_torsionBy_iff _ _).mpr h_ann
              ⟩
              invFun := fun y => ⟨⟨y.1, h_torsion_sub y.2⟩, by
                have hpy : (p : ℤ) • (y.1 : A) = 0 :=
                  (Submodule.mem_torsionBy_iff _ _).mp y.2
                simpa [Submodule.mem_torsionBy_iff] using hpy
              ⟩
              left_inv := fun _ => rfl
              right_inv := fun _ => rfl
              map_add' := fun _ _ => rfl }
          have h_pow_eq : p ^ (Fintype.card ι) = p ^ r :=
            calc
              p ^ (Fintype.card ι) = Nat.card (Submodule.torsionBy ℤ (Submodule.torsionBy ℤ A pe) (p : ℤ)) :=
                (h_card_pe_torsion).symm
              _ = Nat.card (Submodule.torsionBy ℤ A p) := Nat.card_congr h_iso_torsion
              _ = p ^ r := h_card_p
          exact (Nat.pow_right_injective hp_prime.one_lt) h_pow_eq
        -- First prove each ns i divides pe using the basis vector and the isomorphism
        classical
        have h_ns_dvd_pe : ∀ i, ns i ∣ pe := by
          intro i
          -- Let v be the basis vector in the direct sum
          let v := DirectSum.of (fun i => ZMod (ns i)) i (1 : ZMod (ns i))
          -- v corresponds to an element in A[pe] via h_iso.symm
          let x := h_iso.symm v
          -- Since x ∈ A[pe], pe annihilates x in A
          have h_pe_ann : (pe : ℤ) • (x : A) = 0 :=
            (Submodule.mem_torsionBy_iff _ _).mp x.2
          -- Convert to the direct sum: (pe : ℤ) • v = 0
          have hzero : (pe : ℤ) • x = 0 := Subtype.ext (by simpa using h_pe_ann)
          have h_pe_ann_ds : (pe : ℤ) • v = 0 :=
            calc
              (pe : ℤ) • v = (pe : ℤ) • (h_iso (h_iso.symm v)) := by rw [h_iso.apply_symm_apply]
              _ = h_iso ((pe : ℤ) • (h_iso.symm v)) :=
                (h_iso.toAddMonoidHom.map_zsmul (pe : ℤ) (h_iso.symm v)).symm
              _ = h_iso 0 := by rw [hzero]
              _ = 0 := by rw [h_iso.map_zero]
          -- Convert to pi type using h_iso_pi
          have h_pe_ann_pi : (pe : ℤ) • (h_iso_pi v) = 0 :=
            calc
              (pe : ℤ) • (h_iso_pi v) = h_iso_pi ((pe : ℤ) • v) :=
                (h_iso_pi.toAddMonoidHom.map_zsmul (pe : ℤ) v).symm
              _ = h_iso_pi 0 := by rw [h_pe_ann_ds]
              _ = 0 := by rw [h_iso_pi.map_zero]
          -- Evaluate at i: (h_iso_pi v) i = 1
          have h_at_i : (h_iso_pi v) i = (1 : ZMod (ns i)) := by
            simp [h_iso_pi, v, DirectSum.linearEquivFunOnFintype_apply]
          -- Therefore (pe : ZMod (ns i)) = 0, so ns i ∣ pe
          simpa [h_at_i, Pi.smul_apply, ZMod.natCast_eq_zero_iff] using congrArg (· i) h_pe_ann_pi
        -- Since the sum of |ι| = r positive integers is e*r, each must be e
        classical
        have h_fi_le_e : ∀ i, f i ≤ e := by
          intro i
          have h_dvd : ns i ∣ pe := h_ns_dvd_pe i
          rw [hf i, hpe_eq] at h_dvd
          exact (pow_dvd_pow_iff (Nat.Prime.ne_zero hp_prime)
            (by rw [Nat.isUnit_iff]; exact Nat.Prime.ne_one hp_prime)).mp h_dvd
        have h_all_f_eq_e : ∀ i, f i = e :=
          all_eq_of_sum_eq_mul_card f e h_fi_le_e (by rw [h_card_ι, h_sum_f])
        -- Now each ns i = p^e = pe, and |ι| = r
        have hn_all_pe : ∀ i, ns i = pe := by
          intro i
          rw [hf i, h_all_f_eq_e i, ← hpe_eq]
        -- The direct sum is isomorphic to (Fin r → ZMod pe)
        have h_card_ι' : Fintype.card ι = r := h_card_ι
        let ι_equiv : ι ≃ Fin r := Fintype.equivFinOfCardEq h_card_ι'
        -- The direct sum is isomorphic to (Fin r → ZMod pe)
        -- Step 1: cast each summand ZMod (ns i) to ZMod pe
        -- Step 1: reindex from ι to Fin r, then cast summands
        have h_reindex : (⨁ i, ZMod (ns i)) ≃+ (Fin r → ZMod pe) := by
          have h_ds_pi' : (⨁ i, ZMod (ns i)) ≃+ (∀ i, ZMod (ns i)) :=
            DirectSum.addEquivProd (fun i => ZMod (ns i))
          let reindex_pi : (∀ i, ZMod (ns i)) ≃+ (∀ j : Fin r, ZMod (ns (ι_equiv.symm j))) :=
            { (Equiv.piCongrLeft (fun i => ZMod (ns i)) ι_equiv.symm).symm with
              map_add' := by intro x y; rfl }
          have h_replace_factors : (∀ j : Fin r, ZMod (ns (ι_equiv.symm j))) ≃+ (Fin r → ZMod pe) :=
            AddEquiv.piCongrRight (fun j => AddEquiv.cast (hn_all_pe (ι_equiv.symm j)))
          exact h_ds_pi'.trans (reindex_pi.trans h_replace_factors)
        -- Chain everything together
        exact ⟨h_iso.trans h_reindex⟩
      · -- m > 1, so pe < n and m < n
        have hm_gt1 : 1 < m := by omega
        have hpe_gt1 : 1 < pe := by
          rw [hpe_def]
          exact lt_of_lt_of_le (Nat.Prime.one_lt hp_prime)
            (Nat.le_self_pow (Nat.Prime.factorization_pos_of_dvd hp_prime hn.ne.symm hp_dvd).ne.symm p)
        have hpe_lt_n : pe < n := by
          simpa [mul_one, h_prod] using Nat.mul_lt_mul_of_pos_left hm_gt1 hpe_pos
        have hm_lt_n : m < n := by
          simpa [one_mul, h_prod] using Nat.mul_lt_mul_of_pos_right hpe_gt1 hm_pos
        -- From induction hypothesis, A[pe] ≃+ Fin r → ZMod pe and A[m] ≃+ Fin r → ZMod m

        have hpe_ih : Nonempty ((Submodule.torsionBy ℤ A pe) ≃+ (Fin r → ZMod pe)) :=
          ih pe hpe_lt_n hpe_pos (λ d hd => h d (Nat.dvd_trans hd hpe_dvd))
        have hm_ih : Nonempty ((Submodule.torsionBy ℤ A m) ≃+ (Fin r → ZMod m)) :=
          ih m hm_lt_n hm_pos (λ d hd => h d (Nat.dvd_trans hd hm_dvd))
        rcases hpe_ih with ⟨φ_pe⟩
        rcases hm_ih with ⟨φ_m⟩
        -- Chain: A[n] ≃+ A[pe] × A[m] ≃+ (Fin r → ZMod pe) × (Fin r → ZMod m) ≃+ Fin r → ZMod n
        have pi_congr : ((Fin r → ZMod pe) × (Fin r → ZMod m)) ≃+
            (Fin r → (ZMod pe × ZMod m)) :=
          piProdAddEquiv (A := λ _ => ZMod pe) (B := λ _ => ZMod m)
        have h_prod_part : ((Submodule.torsionBy ℤ A pe) × (Submodule.torsionBy ℤ A m)) ≃+
            ((Fin r → ZMod pe) × (Fin r → ZMod m)) :=
          prodAddEquivCongr φ_pe φ_m
        have h_chain : ((Submodule.torsionBy ℤ A pe) × (Submodule.torsionBy ℤ A m)) ≃+
            (Fin r → (ZMod pe × ZMod m)) :=
          h_prod_part.trans pi_congr
        let crt_iso : (ZMod pe × ZMod m) ≃+ ZMod n :=
          (ZMod.chineseRemainder h_coprime).symm.toAddEquiv.trans
            ((AddEquiv.cast h_prod.symm).symm)
        let h_pi : (Fin r → (ZMod pe × ZMod m)) ≃+ (Fin r → ZMod n) :=
          AddEquiv.piCongrRight (λ _ => crt_iso)
        exact ⟨h_isom.some.symm.trans (h_chain.trans h_pi)⟩

-- I only need this if n is prime but there's no harm thinking about it in general I guess.
-- It follows from the previous theorem using pure group theory (possibly including the
-- structure theorem for finite abelian groups)
theorem WeierstrassCurve.n_torsion_dimension [IsSepClosed k] {n : ℕ} (hn : (n : k) ≠ 0) :
    Nonempty (E.nTorsion n ≃+ (ZMod n) × (ZMod n)) := by
  obtain ⟨φ⟩ : Nonempty (E.nTorsion n ≃+ (Fin 2 → (ZMod n))) := by
    apply group_theory_lemma (Nat.pos_of_ne_zero fun h ↦ by simp [h] at hn)
    intro d hd
    apply E.n_torsion_card
    contrapose! hn
    rcases hd with ⟨c, rfl⟩
    simp [hn]
  exact ⟨φ.trans (RingEquiv.piFinTwo _).toAddEquiv⟩

-- follows easily from the above
noncomputable instance (n : ℕ) [NeZero n] : Module.Finite (ZMod n) (E.nTorsion n) := by
  haveI : Finite (E.nTorsion n) := n_torsion_finite E (NeZero.pos n)
  exact inferInstance

-- This should be a straightforward but perhaps long unravelling of the definition
/-- The map on points for an elliptic curve over `k` induced by a morphism of `k`-algebras
is a group homomorphism. -/
noncomputable def WeierstrassCurve.Points.map {K L : Type u} [Field K] [Field L] [Algebra k K]
    [Algebra k L] [DecidableEq K] [DecidableEq L]
    (f : K →ₐ[k] L) : (E⁄K).Point →+ (E⁄L).Point := WeierstrassCurve.Affine.Point.map f

omit [E.IsElliptic] [DecidableEq k] in
lemma WeierstrassCurve.Points.map_id (K : Type u) [Field K] [DecidableEq K] [Algebra k K] :
    WeierstrassCurve.Points.map E (AlgHom.id k K) = AddMonoidHom.id _ := by
  ext
  exact WeierstrassCurve.Affine.Point.map_id _

omit [E.IsElliptic] [DecidableEq k] in
lemma WeierstrassCurve.Points.map_comp (K L M : Type u) [Field K] [Field L] [Field M]
    [DecidableEq K] [DecidableEq L] [DecidableEq M] [Algebra k K] [Algebra k L] [Algebra k M]
    (f : K →ₐ[k] L) (g : L →ₐ[k] M) :
    (WeierstrassCurve.Affine.Point.map g).comp (WeierstrassCurve.Affine.Point.map f) =
    WeierstrassCurve.Affine.Point.map (W' := E) (g.comp f) := by
  ext P
  exact WeierstrassCurve.Affine.Point.map_map _ _ _

/-- The Galois action on the points of an elliptic curve. -/
noncomputable instance WeierstrassCurve.galoisRepresentationSmul
    (K : Type u) [Field K] [DecidableEq K] [Algebra k K] :
    SMul (K ≃ₐ[k] K) (E⁄K).Point := ⟨
  fun g P ↦ WeierstrassCurve.Affine.Point.map (g : K →ₐ[k] K) P⟩

/-- The Galois action on the points of an elliptic curve. -/
noncomputable instance WeierstrassCurve.galoisRepresentation
    (K : Type u) [Field K] [DecidableEq K] [Algebra k K] :
    DistribMulAction (K ≃ₐ[k] K) (E⁄K).Point where
      one_smul P := by
        have h1 : ((1 : K ≃ₐ[k] K) : K →ₐ[k] K) = AlgHom.id k K := by ext; rfl
        calc
          (1 : K ≃ₐ[k] K) • P = WeierstrassCurve.Affine.Point.map
            ((1 : K ≃ₐ[k] K) : K →ₐ[k] K) P := rfl
          _ = WeierstrassCurve.Affine.Point.map (AlgHom.id k K) P := by rw [h1]
          _ = P := by
            have h := WeierstrassCurve.Points.map_id E K
            simpa [WeierstrassCurve.Points.map] using congrArg (· P) h
      mul_smul g h P := by
        have h1 : ((g * h : K ≃ₐ[k] K) : K →ₐ[k] K) = (g : K →ₐ[k] K).comp (h : K →ₐ[k] K) := by
          ext; rfl
        have hmap := WeierstrassCurve.Points.map_comp (E := E) (K := K) (L := K) (M := K)
          (f := (h : K →ₐ[k] K)) (g := (g : K →ₐ[k] K))
        calc
          (g * h) • P = WeierstrassCurve.Affine.Point.map
            ((g * h : K ≃ₐ[k] K) : K →ₐ[k] K) P := rfl
          _ = WeierstrassCurve.Affine.Point.map ((g : K →ₐ[k] K).comp (h : K →ₐ[k] K)) P := by
            rw [h1]
          _ = ((WeierstrassCurve.Affine.Point.map (g : K →ₐ[k] K)).comp
                (WeierstrassCurve.Affine.Point.map (h : K →ₐ[k] K))) P := by
            simpa [WeierstrassCurve.Points.map] using congrArg (· P) hmap.symm
          _ = WeierstrassCurve.Affine.Point.map (g : K →ₐ[k] K)
                (WeierstrassCurve.Affine.Point.map (h : K →ₐ[k] K) P) := rfl
          _ = g • (h • P) := rfl
      smul_zero g :=
        calc
          g • (0 : (E⁄K).Point) = WeierstrassCurve.Affine.Point.map (g : K →ₐ[k] K) 0 := rfl
          _ = 0 := by simp
      smul_add g P Q :=
        calc
          g • (P + Q) = WeierstrassCurve.Affine.Point.map (g : K →ₐ[k] K) (P + Q) := rfl
          _ = WeierstrassCurve.Affine.Point.map (g : K →ₐ[k] K) P +
              WeierstrassCurve.Affine.Point.map (g : K →ₐ[k] K) Q := by simp
          _ = g • P + g • Q := rfl

-- the next `sorry` is data but the only thing which should be missing is
-- the continuity argument, which follows from the finiteness asserted above.

/-- The continuous Galois representation associated to an elliptic curve over a field. -/
def WeierstrassCurve.galoisRep {K : Type u} [Field K] (E : WeierstrassCurve K) [E.IsElliptic]
    [DecidableEq K] [DecidableEq (AlgebraicClosure K)] (n : ℕ) (hn : 0 < n) :
  GaloisRep K (ZMod n) ((E.map (algebraMap K (AlgebraicClosure K))).nTorsion n) := sorry
