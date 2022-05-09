import linear_algebra.projective_space.basic
import linear_algebra.linear_independent
import algebra.field.basic
import tactic
variables {K V : Type*} [field K] [add_comm_group V] [module K V]

open projectivization

--/-Projection into the quotient is a left inverse for the representative function-/
--lemma mk_left_inverse_of_rep (v : ℙ K V) :
--  (projectivization.mk K v.rep (rep_nonzero v)) = v :=
--mk_rep _

/-Composition of function and a finite indexing commute-/
lemma fin_comp_commutes₂ {α β : Type*} {a b : α} {f: α → β} : (f ∘ (![a, b])) = (![f a, f b]) :=
by { ext, fin_cases x; refl }

lemma fin_comp_commutes₃ {α β : Type*} {a b c : α} {f: α → β} : (f ∘ (![a, b, c])) = (![f a, f b, f c]) :=
by { ext, fin_cases x; refl }

/-Two nonzero vectors go to the same point in projective space iff one is in the span of the other-/
lemma mk_eq_mk_iff' (v w: V) (hv : v ≠ 0) (hw : w ≠ 0) : mk K v hv = mk K w hw ↔ ∃ a : K, a • w = v :=
begin
  rw mk_eq_mk_iff K v w hv hw,
  split,
  { rintro ⟨a, ha⟩, 
    exact ⟨a, ha⟩ },
  { rintro ⟨a, ha⟩, 
    refine ⟨units.mk0 a (λ c, hv.symm _), ha⟩, 
    rwa [c, zero_smul] at ha }
end

/-Two points are equal iff their representatives are multiples of eachother-/
lemma eq_iff (v w : ℙ K V) : v = w ↔ ∃ a : Kˣ, a • w.rep = v.rep :=
begin
  conv_lhs { rw [← mk_rep v, ← mk_rep w] },
  rw mk_eq_mk_iff,
end

/- An inductive definition of independence wherein a linearly independent familty of nonzero vectors
gives an independent family in the projective space -/
inductive independent {ι : Type*} : (ι → ℙ K V) → Prop
| mk (f : ι → V) (hf : ∀ i : ι, f i ≠ 0) (hl : linear_independent K f) : 
    independent (λ i, mk K (f i) (hf i))

-- The definitions of independence in a projective space are equivalent
lemma independent_iff (ι : Type*) (f : ι → (ℙ K V)) : (independent f) ↔ 
  (linear_independent K (projectivization.rep ∘ f)) := 
begin
  split,
  { rintro h, induction h with ff hff hh,
    choose a ha using λ (i : ι), exists_smul_eq_mk_rep K (ff i) (hff i),
    convert hh.units_smul a,
    ext i, exact (ha i).symm },
  { intro h, 
    convert independent.mk _ _ h, 
    { ext, simp only [mk_rep] },
    { intro i, apply rep_nonzero } }
end

/-An inductive definition of dependence wherein a linearly dependent family of nonzero vectors
gives a dependent family in the projective space -/
inductive dependent {ι : Type*} : (ι → ℙ K V) → Prop
| mk (f : ι → V) (hf : ∀ i : ι, f i ≠ 0) (h : ¬linear_independent K f) : 
    dependent (λ i, mk K (f i) (hf i))

/-The definitons of dependence are equivalent-/
lemma dependent_iff (ι : Type*) (f : ι → (ℙ K V)) : (dependent f) ↔
  (¬ linear_independent K (projectivization.rep ∘ f)) :=
begin
  split,
  { rw ← independent_iff,
    intros h1, induction h1 with ff hff hh1, 
    contrapose! hh1, rw independent_iff at hh1,
    choose a ha using λ (i : ι), exists_smul_eq_mk_rep K (ff i) (hff i),
    convert hh1.units_smul a⁻¹,
    ext i, simp only [← ha, inv_smul_smul, pi.smul_apply', pi.inv_apply, function.comp_app] },
  { intro h, 
    convert dependent.mk _ _ h, 
    { ext, simp only [mk_rep] },
    { intro i, apply rep_nonzero } }
end

/-Dependence is the negation of independence-/
lemma dependent_iff_not_independent {ι : Type*} (f : ι → ℙ K V) :
  dependent f ↔ ¬ independent f :=
by { rw [dependent_iff, independent_iff] }  

/-Independence is the negation of dependence-/
lemma independent_iff_not_dependent {ι : Type*} (f : ι → ℙ K V) :
  independent f ↔ ¬ dependent f :=
by { rw [dependent_iff, independent_iff, not_not] }  


/-A pair of points in a projective space are dependent iff they are equal-/
@[simp] lemma pair_dependent_iff_eq (u v : ℙ K V) : (dependent ![u, v]) ↔ u = v :=
begin
  rw dependent_iff_not_independent,
  split,
  { intro h, rw independent_iff at h,
    rw linear_independent_fin2 at h,
    simp at h,
    specialize h (rep_nonzero v),
    cases h with a ha,
    rw [← (mk_rep u), ←(mk_rep v),
      mk_eq_mk_iff' u.rep v.rep (rep_nonzero u) (rep_nonzero v)],
    use a,
    assumption  },
  { intro h, rw independent_iff,
    rw [h, linear_independent_fin2],
    simp,
    intro hv,
    use 1,
    simp, },
end

/-A pair of points in a projective space are independent iff they are not equal-/
@[simp] lemma pair_independent_iff_neq (u v : ℙ K V) : (independent ![u, v]) ↔
  u ≠ v :=
by {  rw independent_iff_not_dependent, simp,  }

lemma nt_lin_comb_implies_in_span {u v : V} {a b : K} (ha : a ≠ 0) (hz : a • u + b • v = 0) :
  (-a⁻¹*b) • v = u :=
begin
have huv : a • u = -(b • v), by {rw ← eq_neg_iff_add_eq_zero at hz, exact hz},
have hv : u = (- a⁻¹*b) • v, by
  {  calc
  u = 1 • u : (one_smul _ (u)).symm
  ... = (a⁻¹ * a) • u : by {  rw (inv_mul_cancel ha), simp  }
  ... = (- a⁻¹*b) • v : by {  rw [mul_smul, huv, mul_smul], simp  }  },
exact hv.symm
end

lemma dependent_iff_reps_dependent₂ (u v : ℙ K V) : dependent ![u, v] ↔
  ∃ (a b : K) (hnt : ![a, b] ≠ 0), a • u.rep + b • v.rep = 0 :=
begin
  rw [dependent_iff, fin_comp_commutes₂, linear_independent_fin2],
  split,
  { intro h,
    simp at h,
    specialize h (rep_nonzero v),
    cases h with a ha,
    use [-1, a],
    split; simp,
    rw ha,
    simp,  },
  { rintros ⟨a, b, ⟨hnt, hz⟩⟩,
    simp,
    intro hv,
    suffices ha : a ≠ 0, by {  use (-a⁻¹*b), exact nt_lin_comb_implies_in_span ha hz,  },
    by_contradiction,
    rw h at hz,
    simp at *,
    cases hz,
    { exact hnt h hz },
    { exact rep_nonzero v hz, } }
end

open_locale big_operators

lemma dependent_iff_reps_dependent₃ (u v w : ℙ K V) : dependent ![u, v, w] ↔
  ∃ (a b c : K) (hnt : ![a, b, c] ≠ 0), a • u.rep + b • v.rep + c • w.rep = 0 :=
begin
  rw [dependent_iff, fintype.not_linear_independent_iff],
  simp only [fin.sum_univ_succ, function.comp_app, matrix.cons_val_zero, matrix.cons_val_succ, 
    fin.succ_zero_eq_one, fintype.univ_of_subsingleton, fin.mk_eq_subtype_mk, fin.mk_zero, 
    finset.sum_singleton, fin.succ_one_eq_two, eq_iff_true_of_subsingleton, and_true, 
    not_and, exists_prop, add_assoc],
  split,
  { rintro ⟨g,h1,⟨i,h2⟩⟩, 
    refine ⟨g 0, g 1, g 2, _, h1⟩,
    rw function.ne_iff, use i, fin_cases i; exact h2 },
  { rintros ⟨a,b,c,h1,h2⟩, 
    refine ⟨![a,b,c], h2, _⟩,
    rwa ← function.ne_iff, }
end

/-A nontrivial linear combination of representatives which is zero implies both scalars are nonzero-/
lemma lc_implies_both_nz {u v : ℙ K V} {a b : K} (ht: ![a, b] ≠ 0) (hs : a • u.rep + b • v.rep = 0) : a ≠ 0 ∧ b ≠ 0 :=
begin
split;
by_contradiction;
rw h at hs;
simp at hs;
cases hs,
  {  have hz : ![a,b] = 0, by {  simp at *, split; assumption,  },
  exact ht hz,  },
  {  exact rep_nonzero v hs,  },
  {  have hz : ![a,b] = 0, by {  simp at *, split; assumption,  },
  exact ht hz,  },
  {  exact rep_nonzero u hs,  },
end

/-If in a -/
@[simp] lemma nontrivial_and_zero₁ {a b c : K} (ht : ![a, b, c] ≠ 0)
  (ha : a = (0 : K)) : ![b, c] ≠ 0 :=
begin
simp at *,
intro hb,
by_contradiction,
exact ((ht ha) hb) h,
end


@[simp] lemma nontrivial_and_zero₂ {a b c : K} (ht : ![a, b, c] ≠ 0)
  (hb : b = (0 : K)) : ![a, c] ≠ 0 :=
begin
simp at *,
intro ha,
by_contradiction,
exact ((ht ha) hb) h,
end


lemma neq_implies_sc_neq_zero {u v w : ℙ K V} {a b c : K} (hneq : v ≠ w)
  (hnz : ![a, b, c] ≠ 0) (hsz : a • u.rep + b • v.rep + c • w.rep = 0) : a ≠ 0 :=
begin
by_contradiction,
rw h at hsz,
simp at hsz,
have hz, from nontrivial_and_zero₁ hnz h,
have h2, from lc_implies_both_nz hz hsz,
cases h2 with hb hc,
have heq : v = w, by
  {  rw [← mk_rep v, ← mk_rep w,
  mk_eq_mk_iff' v.rep w.rep (rep_nonzero v) (rep_nonzero w)],
  use -b⁻¹*c,
  exact nt_lin_comb_implies_in_span hb hsz,  },
exact hneq heq,
end



/-Three points of a projective geometry are collinear if they are dependent-/
def collinear (u v w : ℙ K V) : Prop :=
  dependent _ ![u, v, w]

/--The collinear relation satisfies the axioms of a projective geometry as defined in
Modern Projective Geometry by Faure and Frolicher-/

/-Any two points of a projective space are collinear-/
lemma L1 (u v : ℙ K V) : collinear u v u :=
begin
unfold collinear,
rw dependent_iff_reps_dependent₃,
use [1, 0, -1],
split;
simp,
end


/-Two distinct points determine a line-/
lemma L2 (a b p q : ℙ K V) (h1 : collinear a p q) (h2 : collinear b p q)
  (hneq : p ≠ q) : collinear a b p :=
begin
unfold collinear at *,
rw dependent_iff_reps_dependent₃ at *,
rcases h1 with ⟨x₁, y₁, z₁, ⟨h1nt, h1z⟩⟩,
rcases h2 with ⟨x₂, y₂, z₂, ⟨h2nt, h2z⟩⟩,
cases classical.em (z₁ = 0) with hz₁ hz₁,
  { rw hz₁ at h1z,
  use [x₁, 0, y₁],
  split,
    {  by_contradiction,
    simp at *,
    exact h1nt h.1 h.2 hz₁,  },
    {  simp at *, assumption  },  },
  {  use  [- z₂*z₁⁻¹*x₁, x₂, y₂ - z₂*z₁⁻¹*y₁],
  split,
    {  have hx₂ : x₂ ≠ 0, from neq_implies_sc_neq_zero hneq h2nt h2z,
    simp, intros _ _, contradiction,  },
    {  have h2: 0 + (-z₂*z₁⁻¹) • (x₁ • a.rep + y₁ • p.rep + z₁ • q.rep)  = 0, by {  rw h1z, simp  },
    nth_rewrite 0 [ ← h2z] at h2,
    rw [smul_add, smul_add, ← mul_smul(-z₂*z₁⁻¹) z₁,
      (@mul_assoc K _ (-z₂) z₁⁻¹ z₁), inv_mul_cancel hz₁] at h2,
    simp at h2,
    rw ← h2,
    abel,
    repeat {  rw ← mul_smul  },
    rw [add_left_cancel_iff, add_comm (y₂ • p.rep) _, add_assoc _ _ (y₂ • p.rep)],
    simp,
    rw [add_comm],
    abel,
    rw [add_smul, add_left_cancel_iff, smul_assoc],  },  },
end

/-If a point belongs to two lines, then-/
lemma L3 (a b c d p : ℙ K V) (h1 : collinear p a b) (h2 : collinear p c d) :
  ∃ q : ℙ K V, collinear q a c ∧ collinear q b d :=
begin
unfold collinear at *,
rw dependent_iff_reps_dependent₃ at *,
rcases h1 with ⟨x₁, y₁, z₁, ⟨h1nt, h1z⟩⟩,
rcases h2 with ⟨x₂, y₂, z₂, ⟨h2nt, h2z⟩⟩,
simp_rw dependent_iff_reps_dependent₃,
cases classical.em (c = a) with hca hnca,
  {  rw hca,
  use b,
  split,
    {  use [ 0, -1, 1], simp  },
    {  use [-1, 1, 0], simp  }  },
  {  cases classical.em (x₁ = 0) with hx₁ hx₁,
    {  rw hx₁ at h1z,
    simp at h1z,
    have hab : a = b, by {rw [← pair_dependent_iff_eq, dependent_iff_reps_dependent₂], use [y₁, z₁], split, exact nontrivial_and_zero₁ h1nt hx₁, assumption,  },
    rw hab,
    use b,
    split; use [1,-1,0]; split; simp,  },
    {  cases classical.em (x₂ = 0) with hx₂ hx₂,
      {  rw hx₂ at h2z,
      simp at h2z,
      have hcd : c = d, by {  rw [← pair_dependent_iff_eq, dependent_iff_reps_dependent₂], use [y₂, z₂], split, exact nontrivial_and_zero₁ h2nt hx₂, assumption,  },
      rw hcd,
      use d,
      split; use [1, 0, -1]; split; simp,  },
      cases classical.em (y₂ = 0) with hy₂ hy₂,
        {  use a,
        rw hy₂ at h2z,
        simp at h2z,
        have hpd : p = d, by {  rw [← pair_dependent_iff_eq, dependent_iff_reps_dependent₂], use [x₂, z₂], split, exact nontrivial_and_zero₂ h2nt hy₂, exact h2z  },
        split,
          {  use [1, -1, 0], simp,  },
          {  rw ← hpd, use [y₁, z₁, x₁], simp, split,
            {  simp at h1nt, intros hy₁ hz₁, by_contradiction, exact h1nt h hy₁ hz₁  },
            {  rw [add_comm, ← add_assoc], exact h1z  },  },  },
        {  let q := (x₂⁻¹*y₂) • c.rep + (-x₁⁻¹*y₁) • a.rep,
        have hqneq : q ≠ 0, by
          {  by_contradiction,
          have hq : (x₂⁻¹*y₂) • c.rep + (-x₁⁻¹*y₁) • a.rep = 0, from h,
          have hx₂y₂ : x₂⁻¹*y₂ ≠ 0, by {  refine mul_ne_zero _ hy₂,  exact left_ne_zero_of_mul_eq_one (inv_mul_cancel hx₂),  },
          have tttt, from nt_lin_comb_implies_in_span hx₂y₂ hq,
          have hca : c = a, by {  rw [← mk_rep a, ← mk_rep c, mk_eq_mk_iff'], use -(x₂⁻¹*y₂)⁻¹*(-x₁⁻¹*y₁), exact tttt  },
          exact hnca hca, },
        use mk K q hqneq,
        have hk, from exists_smul_eq_mk_rep K q hqneq,
        cases hk with k hk,
        have hk' : (k : K) • q = (mk K q hqneq).rep, by {  exact hk  },
        have hnk : (k : K) ≠ 0, by {  rw ← units.exists_iff_ne_zero, use k  },
        rw ← hk',
        split,
          {  use [((↑k)⁻¹ : K), x₁⁻¹*y₁, -x₂⁻¹*y₂ ],
          rw [← mul_smul _ _ q, inv_mul_cancel hnk],
          simp,  },
          {  use [x₂*((↑k)⁻¹ : K), -(x₂*x₁⁻¹*z₁), z₂],
          split,
            {  simp, intro hzx₂, exfalso, exact hx₂ hzx₂  },
            { rw [← mul_smul _ _ q, mul_assoc, inv_mul_cancel hnk],
            simp,
            have h2 : 0 + (-x₂*x₁⁻¹) • (x₁ • p.rep + y₁ • a.rep + z₁ • b.rep) = 0, by {  rw h1z, simp  },
            nth_rewrite 0 [← h2z] at h2,
            repeat {  rw [smul_add, ← mul_smul] at h2  },
            repeat {  rw ← mul_smul  },
            rw [← mul_assoc, mul_inv_cancel hx₂],
            simp,
            rw [mul_assoc (-x₂) _ _, inv_mul_cancel hx₁, ← mul_smul] at h2,
            simp at h2,
            abel at h2,
            abel,
            rw ← mul_assoc x₂ x₁⁻¹ _,
            exact h2,  },  },  },  },  },
end



/- Dependence of points in the projective space is preserved by linear equivalences -/

variables {W : Type*} [add_comm_group W] [module K W]
variable (T : V ≃ₗ[K] W)

/- Projecting a nonzero vector to the quotient and evaluating an injective linear map
at that vector commute -/
@[simp] lemma map_mk_eq_mk' (T : V →ₗ[K] W) (hT : function.injective T)
  (v : V) (hv : v ≠ 0) :
  map T hT (mk K v hv) = mk K (T v) (by {rw ← (T.map_zero), exact hT.ne hv}) := by {  refl  }

lemma map_mk_eq_mk (v : V) (hv : v ≠ 0) :
  map T.to_linear_map T.injective (mk K v hv) =
  mk _ (T v) (T.map_ne_zero_iff.mpr hv) :=
  by {  refl  }


/-The map induced by an Isomorphism of vector spaces preserves independence-/
/- lemma independent_comp_iso_independent {ι : Type*} (f : ι → ℙ K V) (hi : independent _ f) :
  independent _ ((map T.to_linear_map T.injective) ∘ f) :=
begin
unfold independent at *,
suffices hsmul: ∃ g : ι → Kˣ, (projectivization.rep ∘ map T.to_linear_map T.injective ∘ f) = g • (T.to_linear_map ∘ projectivization.rep ∘ f), by
  {cases hsmul with g hg,
  rw hg,
  suffices h : linear_independent K (T.to_linear_map ∘ projectivization.rep ∘ f) ↔ linear_independent K (projectivization.rep ∘ f), by
    {rw ← h  at hi,
    exact linear_independent.units_smul hi g},

  have ht : linear_independent K (T.to_linear_map ∘ projectivization.rep ∘ f) ↔ linear_independent K (projectivization.rep ∘ f), from linear_map.linear_independent_iff T.to_linear_map (linear_equiv.ker T),
  exact ht  },
have g : ι → Kˣ, by
  {intro i,
  have ht, from map_mk_eq_mk' (T.to_linear_map) (T.injective) (projectivization.rep (f i)) (rep_nonzero (f i)),
  rw eq_iff _ _ at ht,



  },

end -/

/- Independence of points is preserved by linear equivalences-/
lemma independent_comp_iso_independent {ι : Type*} (f : ι → ℙ K V) (hi : independent _ f) :
  independent _ ((map T.to_linear_map T.injective) ∘ f) :=
begin
unfold independent at hi,
have hli, from linear_independent.map' hi T.to_linear_map (linear_equiv.ker T),
have hli', from independent'.mk (by {simp, intro i, exact rep_nonzero (f i), }) hli,
rw independent_iff,
  split,
  {sorry},
  {sorry},

end


/- Points are independent iff they are independent under the map induced by a linear equivalence-/
lemma independent_iff_iso_independent {ι : Type*} (f : ι → ℙ K V) :
  independent _ f ↔ independent _ ((map T.to_linear_map T.injective) ∘ f) :=
begin
split,
  { intro h,
    exact independent_comp_iso_independent _ f h},
  {intro h,
  have hT, from independent_comp_iso_independent T.symm ((map T.to_linear_map T.injective) ∘ f) h,
  rw [← function.comp.assoc, ← map_comp] at hT,
  suffices hid : map (T.symm.to_linear_map.comp T.to_linear_map) _ = map linear_map.id _, by
    {rw [hid, map_id] at hT,
    simp at hT,
    exact hT,},
  ext,
  unfold map,
  simp,},
end

/-Points are dependent iff they are dependent under the map induced by a linear equivalence-/
lemma dependent_iff_iso_dependent {ι : Type*} (f : ι → ℙ K V) :
  dependent _ f ↔ dependent _ ((map T.to_linear_map T.injective) ∘ f) :=
begin
rw [dependent_iff_not_independent, dependent_iff_not_independent, not_iff_not],
exact independent_iff_iso_independent _ _,
end


lemma independent_iff_independent₂ (u v : ℙ K V) : independent _ ![u, v] ↔
  independent _ ![map T.to_linear_map T.injective u, map T.to_linear_map T.injective v] :=
begin
rw ← fin_comp_commutes₂,
exact independent_iff_iso_independent _ _,
end

lemma independent_iff_independent₃ (u v w: ℙ K V) : independent _ ![u, v, w] ↔
  independent _ ![map T.to_linear_map T.injective u, map T.to_linear_map T.injective v,
  map T.to_linear_map T.injective w] :=
begin
rw ← fin_comp_commutes₃,
exact independent_iff_iso_independent _ _,
end

lemma dependent_iff_dependent₂ (u v : ℙ K V) : dependent _ ![u, v] ↔
  dependent _ ![map T.to_linear_map T.injective u, map T.to_linear_map T.injective v] :=
begin
rw ← fin_comp_commutes₂,
exact dependent_iff_iso_dependent _ _,
end

lemma dependent_iff_dependent₃ (u v w: ℙ K V) : dependent _ ![u, v, w] ↔
  dependent _ ![map T.to_linear_map T.injective u, map T.to_linear_map T.injective v,
  map T.to_linear_map T.injective w] :=
begin
rw ← fin_comp_commutes₃,
exact dependent_iff_iso_dependent _ _,
end
