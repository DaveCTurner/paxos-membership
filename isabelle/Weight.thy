theory Weight
  imports Main
begin

fun weight :: "('acc \<Rightarrow> nat) \<Rightarrow> 'acc set \<Rightarrow> nat"
  where "weight f S = sum f { a \<in> S. f a \<noteq> 0 }"

fun isWeightedMajority :: "('acc \<Rightarrow> nat) \<Rightarrow> 'acc set \<Rightarrow> bool"
  where "isWeightedMajority f S = (finite { a. f a \<noteq> 0 } \<and> finite S \<and> weight f UNIV < 2 * weight f S)"

lemma weight_insert:
  assumes a: "a \<notin> S" and fin: "finite {a. f a \<noteq> 0}"
  shows "weight f (insert a S) = f a + weight f S"
proof (cases "f a = 0")
  case True
  hence "{a' \<in> insert a S. f a' \<noteq> 0} = {a' \<in> S. f a' \<noteq> 0}" by auto
  with True show ?thesis by auto
next
  case False
  hence p: "{a' \<in> insert a S. f a' \<noteq> 0} = insert a {a' \<in> S. f a' \<noteq> 0}" by auto
  hence "weight f (insert a S) = sum f (insert a {a' \<in> S. f a' \<noteq> 0})" by simp
  also from fin a have "... = f a + sum f {a' \<in> S. f a' \<noteq> 0}"
    by (intro sum.insert, auto)
  also have "... = f a + weight f S" by simp
  finally show ?thesis .
qed

lemma weight_diff:
  assumes a: "a \<in> S" and fin: "finite {a. f a \<noteq> 0}"
  shows "weight f (S - {a}) = weight f S - f a"
proof -
  from a have a': "insert a (S - {a}) = S" by auto
  have "a \<notin> S - {a}" by simp
  from weight_insert [OF this fin]
  show ?thesis by (simp only: a')
qed

lemma weight_mul:
  shows "weight (%a. k * f a) S = k * weight f S"
proof (cases "k = 0")
  case True
  thus ?thesis by auto
next
  case False
  hence nz_eq: "{a \<in> S. f a \<noteq> 0} = {a \<in> S. k * f a \<noteq> 0}" by auto

  show ?thesis
  proof (cases "finite { a \<in> S. f a \<noteq> 0 }")
    case False
    hence p: "weight f S = 0" by auto
    from False nz_eq
    have "\<not> finite { a \<in> S. k * f a \<noteq> 0 }" by simp
    hence q: "weight (%a. k * f a) S = 0" by simp
    with p show ?thesis by simp
  next
    case True
    with nz_eq have True': "finite { a \<in> S. k * f a \<noteq> 0 }" by simp
    from nz_eq
    have "weight (\<lambda>a. k * f a) S = sum ((%a. k * a) o f) { a \<in> S. f a \<noteq> 0 }" by simp
    also have "... = k * sum f { a \<in> S. f a \<noteq> 0 }"
      by  (intro sum_comp_morphism, simp_all add: distrib_left)
    also have "... = k * weight f S" by simp
    finally show ?thesis .
  qed
qed

lemma weight_mono:
  assumes fin1: "finite {a. f1 a \<noteq> 0}"
  assumes fin2: "finite {a. f2 a \<noteq> 0}"
  assumes le: "\<And>a. a \<in> S \<Longrightarrow> f1 a \<le> f2 a"
  shows "weight f1 S \<le> weight f2 S"
proof -
  have "weight f1 S = sum f1 { a \<in> S. f1 a \<noteq> 0}" by simp
  also from fin1 fin2 have "... \<le> sum f1 { a \<in> S. f1 a \<noteq> 0 \<or> f2 a \<noteq> 0 }"
    by (intro sum_mono2, auto)
  also have "... \<le> sum f2 { a \<in> S. f1 a \<noteq> 0 \<or> f2 a \<noteq> 0 }"
    by (intro sum_mono le, auto)
  also have "... = sum f2 ({ a \<in> S. f2 a \<noteq> 0 } \<union> { a \<in> S. f2 a = 0 \<and> f1 a \<noteq> 0})"
    by (intro cong [OF refl, where f = "sum f2"], auto)
  also from fin1 fin2 have "... = sum f2 { a \<in> S. f2 a \<noteq> 0 } + sum f2 { a \<in> S. f2 a = 0 \<and> f1 a \<noteq> 0}"
    by (intro sum.union_disjoint, auto)
  also have "... = weight f2 S" by simp
  finally show ?thesis .
qed

lemma
  assumes S1: "isWeightedMajority f1 S1"
  assumes S2: "isWeightedMajority f2 S2"
  assumes d1: "d \<le> 1"
  assumes fa0: "k2 * f2 a0 = k1 * f1 a0 + d"
  assumes f: "\<And>a. a \<noteq> a0 \<Longrightarrow> k1 * f1 a = k2 * f2 a"
  assumes k1: "k1 \<noteq> 0" and k2: "k2 \<noteq> 0"
  shows weighted_majority_intersects_asym: "S1 \<inter> S2 \<noteq> ({} :: 'acc set)"
proof -

  define kf1 where "kf1 == %a. k1 * f1 a"
  define kf2 where "kf2 == %a. k2 * f2 a"

  have weight_kf1: "\<And>S. weight kf1 S = k1 * weight f1 S" by (unfold kf1_def, intro weight_mul)
  have weight_kf2: "\<And>S. weight kf2 S = k2 * weight f2 S" by (unfold kf2_def, intro weight_mul)
  from fa0 have kfa0: "kf2 a0 = kf1 a0 + d" by (simp add: kf1_def kf2_def)
  from f   have kf: "\<And>a. a \<noteq> a0 \<Longrightarrow> kf1 a = kf2 a" by (simp add: kf1_def kf2_def)

  from S1 k1 have kS1: "isWeightedMajority kf1 S1"
    by (unfold isWeightedMajority.simps weight_kf1, intro conjI, auto simp add: kf1_def)

  from S2 k2 have kS2: "isWeightedMajority kf2 S2"
    by (unfold isWeightedMajority.simps weight_kf2, intro conjI, auto simp add: kf2_def)

  from kS1 have kS1_le: "weight kf1 UNIV + 1 \<le> 2 * weight kf1 S1" by auto
  from kS2 have kS2_le: "weight kf2 UNIV + 1 \<le> 2 * weight kf2 S2" by auto

  have nat_le_ge: "\<And>n m::nat. n \<le> m \<Longrightarrow> m \<le> n \<Longrightarrow> m = n" by auto

  have kf_le: "\<And>a. kf1 a \<le> kf2 a"
  proof -
    fix a from kfa0 kf show "?thesis a" by (cases "a = a0", auto)
  qed

  from kf_le kS1 kS2 have weight_12: "\<And>S. weight kf1 S \<le> weight kf2 S"
    by (intro weight_mono, auto)

  from kf kS1 kS2 have weight_eq: "\<And>S. a0 \<notin> S \<Longrightarrow> weight kf2 S = weight kf1 S"
  proof (intro nat_le_ge [OF weight_12 weight_mono])
    fix a S assume "a0 \<notin> S" and "a \<in> S" hence "a \<noteq> a0" by auto
    with kf show "kf2 a \<le> kf1 a" by simp
  qed auto

  have weight_eq_mem: "\<And>S. a0 \<in> S \<Longrightarrow> weight kf2 S = weight kf1 S + d"
  proof -
    fix S assume a0: "a0 \<in> S"
    hence "weight kf2 S = weight kf2 (insert a0 (S - {a0}))"
      by (intro cong [OF refl, where f = "weight kf2"], auto)
    also from kS2 have "... = kf2 a0 + weight kf2 (S - {a0})"
      by (intro weight_insert, auto)
    also have "... = kf2 a0 + weight kf1 (S - {a0})"
      by (intro cong [OF refl, where f = "%n. kf2 a0 + n"] weight_eq, simp)
    also have "... = (kf1 a0 + d) + weight kf1 (S - {a0})" by (simp add: kfa0)
    also have "... = (kf1 a0 + weight kf1 (S - {a0})) + d" by simp
    also from kS1 have "... = weight kf1 (insert a0 (S - {a0})) + d"
      by (intro cong [OF refl, where f = "%n. n + d"] sym [OF weight_insert], auto)
    also from a0 have "... = weight kf1 S + d"
      by (intro cong [OF refl, where f = "%n. n + d"] cong [OF refl, where f = "weight kf1"], auto)
    finally show "?thesis S" .
  qed

  define d' where "d' == if a0 \<in> S2 then d else 0"

  have weight_UNIV: "weight kf2 UNIV = weight kf1 UNIV + d"
    by (intro weight_eq_mem, simp)

  have weight_S2: "weight kf2 S2 = weight kf1 S2 + d'"
  proof (cases "a0 \<in> S2")
    case True
    have "weight kf2 S2 = weight kf1 S2 + d"
      by (intro weight_eq_mem True)
    thus ?thesis by (simp add: d'_def True)
  next
    case False
    hence "weight kf2 S2 = weight kf1 S2" by (intro weight_eq)
    thus ?thesis by (simp add: d'_def False)
  qed

  have union_inter_eq:
    "{ a \<in> S1 \<union> S2. kf1 a \<noteq> 0 } = { a \<in> S1. kf1 a \<noteq> 0 } \<union> { a \<in> S2. kf1 a \<noteq> 0 }"
    "{ a \<in> S1 \<inter> S2. kf1 a \<noteq> 0 } = { a \<in> S1. kf1 a \<noteq> 0 } \<inter> { a \<in> S2. kf1 a \<noteq> 0 }"
    by auto

  have le_plus_eq: "\<And>a b c :: nat. a \<le> b \<Longrightarrow> 2 * a + c \<le> 2 * b + c" by auto

  from S1 S2
  have in_ex: "weight kf1 S1 + weight kf1 S2 = weight kf1 (S1 \<union> S2) + weight kf1 (S1 \<inter> S2)"
    by (unfold weight.simps union_inter_eq, intro sym [OF sum.union_inter], auto)

  have "2 * weight kf1 UNIV + d + 2 = (weight kf1 UNIV + 1) + ((weight kf1 UNIV + d) + 1)" by simp
  also from weight_UNIV have "... = (weight kf1 UNIV + 1) + (weight kf2 UNIV + 1)" by simp
  also from kS1_le kS2_le have "... \<le> 2 * weight kf1 S1 + 2 * weight kf2 S2" by simp
  also from weight_S2 have "... = 2 * weight kf1 S1 + 2 * (weight kf1 S2 + d')" by simp
  also have "... = 2 * (weight kf1 S1 + weight kf1 S2) + 2 * d'" by simp
  also have "... = 2 * (weight kf1 (S1 \<union> S2) + weight kf1 (S1 \<inter> S2)) + 2 * d'" by (simp only: in_ex)
  also have "... = 2 * weight kf1 (S1 \<union> S2) + (2 * weight kf1 (S1 \<inter> S2) + 2 * d')" by simp
  also from kS1 have "... \<le> 2 * weight kf1 UNIV + (2 * weight kf1 (S1 \<inter> S2) + 2 * d')"
    by (intro le_plus_eq, simp, intro sum_mono2, auto)
  finally have p: "d + 2 \<le> 2 * weight kf1 (S1 \<inter> S2) + 2 * d'" by simp

  from d1 have "0 < d + 2 - 2 * d'" by (auto simp add: d'_def)
  also from p have "... \<le> 2 * weight kf1 (S1 \<inter> S2)" by auto
  finally show "S1 \<inter> S2 \<noteq> {}" by (intro notI, auto)
qed

fun abs_diff :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where "abs_diff m n = (if m < n then n - m else m - n)"

lemma
  assumes S1: "isWeightedMajority f1 S1"
  assumes S2: "isWeightedMajority f2 S2"
  assumes k1: "k1 \<noteq> 0" and k2: "k2 \<noteq> 0"
  assumes similar: "weight (%a. abs_diff (k1 * f1 a) (k2 * f2 a)) UNIV \<le> 1"
  shows weighted_majority_intersects: "S1 \<inter> S2 \<noteq> ({} :: 'acc set)"
proof -
  define kf1 where "kf1 == %a. k1 * f1 a"
  define kf2 where "kf2 == %a. k2 * f2 a"

  from k1 have kf1z: "\<And>a. (kf1 a = 0) = (f1 a = 0)" by (simp add: kf1_def)
  from k2 have kf2z: "\<And>a. (kf2 a = 0) = (f2 a = 0)" by (simp add: kf2_def)

  from similar have ksim: "weight (%a. abs_diff (kf1 a) (kf2 a)) UNIV \<le> 1"
    by (simp add: kf1_def kf2_def)

  obtain a0
    where kfa0: "abs_diff (kf1 a0) (kf2 a0) \<le> 1"
      and kf_eq: "\<And>a. a \<noteq> a0 \<Longrightarrow> kf1 a = kf2 a"
  proof -
    define df where "df == %a. abs_diff (kf1 a) (kf2 a)"
    define deviations where "deviations == {a. df a \<noteq> 0}"

    have deviations_subset: "deviations \<subseteq> {a . kf1 a \<noteq> 0} \<union> {a. kf2 a \<noteq> 0}"
    proof (intro subsetI)
      fix a assume a: "a \<in> deviations"
      hence "abs_diff (kf1 a) (kf2 a) \<noteq> 0" by (simp add: deviations_def df_def)
      hence "kf1 a \<noteq> 0 \<or> kf2 a \<noteq> 0" by auto
      thus "a \<in> {a . kf1 a \<noteq> 0} \<union> {a. kf2 a \<noteq> 0}" by simp
    qed
    from S1 S2 have finite_deviations: "finite deviations"
      by (intro finite_subset [OF deviations_subset], unfold finite_Un kf1z kf2z, simp)

    have "card deviations \<le> sum df deviations"
      by (unfold card_eq_sum, intro sum_mono, simp add: deviations_def)
    also have "weight df UNIV = sum df deviations"
      by (simp add: deviations_def)
    with ksim have df_max: "sum df deviations \<le> 1" by (simp add: df_def)
    finally have "card deviations \<le> 1" .
    hence "card deviations = 0 \<or> card deviations = 1" by auto
    thus thesis
    proof (elim disjE)
      assume "card deviations = 0"
      with finite_deviations have no_deviations: "deviations = {}" by simp

      fix a
      show thesis
      proof (intro that)
        from no_deviations show "abs_diff (kf1 a) (kf2 a) \<le> 1"
          by (simp add: deviations_def df_def)
        fix a'
        from no_deviations show "kf1 a' = kf2 a'"
          apply (simp add: deviations_def df_def)
          by (metis less_not_refl linorder_cases zero_less_diff)
      qed
    next
      assume c1: "card deviations = 1"
      then obtain a where a: "a \<in> deviations" by (cases "deviations = {}", auto)
      have deviations: "deviations = {a}"
        by (intro sym [OF card_seteq] finite_deviations, auto simp add: c1 a)

      show thesis
      proof (intro that)
        from ksim deviations
        show "abs_diff (kf1 a) (kf2 a) \<le> 1"
          by (auto simp add: deviations_def df_def)

        fix a'
        assume "a' \<noteq> a"
        hence "a' \<notin> deviations" by (simp add: deviations)
        thus "kf1 a' = kf2 a'"
          apply (simp add: deviations_def df_def)
          by (metis less_not_refl linorder_cases zero_less_diff)
      qed
    qed
  qed

  from kf_eq have f_eq: "\<And>a. a \<noteq> a0 \<Longrightarrow> k1 * f1 a = k2 * f2 a"
    by (simp add: kf1_def kf2_def)

  from kfa0 have fa0: "abs_diff (k1 * f1 a0) (k2 * f2 a0) \<le> 1"
    by (simp add: kf1_def kf2_def)

  show ?thesis
  proof (cases "k1 * f1 a0 < k2 * f2 a0")
    case True
    show ?thesis
    proof (intro weighted_majority_intersects_asym [OF S1 S2 _ _ f_eq k1 k2])
      from True show "k2 * f2 a0 = k1 * f1 a0 + (k2 * f2 a0 - k1 * f1 a0)" by simp
      from True fa0 show "k2 * f2 a0 - k1 * f1 a0 \<le> 1" by auto
    qed
  next
    case False
    have "S2 \<inter> S1 \<noteq> {}"
    proof (intro weighted_majority_intersects_asym [OF S2 S1 _ _ sym [OF f_eq] k2 k1])
      from False show "k1 * f1 a0 = k2 * f2 a0 + (k1 * f1 a0 - k2 * f2 a0)" by simp
      from False fa0 show "k1 * f1 a0 - k2 * f2 a0 \<le> 1" by auto
    qed
    thus ?thesis by auto
  qed
qed

lemma
  assumes eq: "\<And>a :: 'aid. f1 a * d1 = f2 a * d2"
  assumes d1: "0 < d1" and d2: "0 < d2"
  shows weighted_majority_mul: "isWeightedMajority f1 = isWeightedMajority f2"
proof (intro ext iffI)
  have p: "\<And>f1 f2 d1 d2 S. isWeightedMajority f1 S \<Longrightarrow> 0 < d1 \<Longrightarrow> 0 < (d2 :: nat) \<Longrightarrow> (\<And>a :: 'aid. f1 a * d1 = f2 a * d2) \<Longrightarrow> isWeightedMajority f2 S"
  proof -
    fix f1 f2 d1 d2 S
    assume eq: "\<And>a :: 'aid. f1 a * d1 = f2 a * (d2 :: nat)"
      and d1: "0 < d1" and d2: "0 < d2"

    hence s0: "\<And> T. {a \<in> T. f2 a \<noteq> 0} = {a \<in> T. f1 a \<noteq> 0}"
      by (metis le0 mult_is_0 not_le)

    hence s1: "{a. f2 a \<noteq> 0} = {a. f1 a \<noteq> 0}" by auto

    have d2I: "\<And>n m. d2 * n < d2 * (2 * m) \<Longrightarrow> n < 2 * m"
      by (metis nat_mult_less_cancel_disj)

    have d21: "\<And>T. d2 * sum f2 T = d1 * sum f1 T"
    proof -
      fix T
      have "d2 * sum f2 T = sum (%n. d2 * f2 n) T" by (simp add: sum_distrib_left)
      also have "... = sum (%n. d1 * f1 n) T"
      proof (intro sum.cong refl)
        fix a
        have "d1 * f1 a = f1 a * d1" by simp
        also note eq
        also have "f2 a * d2 = d2 * f2 a" by simp
        finally show "d2 * f2 a = d1 * f1 a" ..
      qed
      also have "... = d1 * sum f1 T" by (simp add: sum_distrib_left)
      finally show "?thesis T" .
    qed

    assume w1: "isWeightedMajority f1 S"
    show "isWeightedMajority f2 S"
    proof (unfold isWeightedMajority.simps weight.simps s0 s1, intro conjI d2I)
      from w1 show "finite {a. f1 a \<noteq> 0}" and "finite S" by auto
      have "d2 * sum f2 {a \<in> UNIV. f1 a \<noteq> 0} = d1 * sum f1 {a \<in> UNIV. f1 a \<noteq> 0}"
        by (simp add: d21)
      also from w1 d1 have "... < d1 * (2 * sum f1 {a \<in> S. f1 a \<noteq> 0})"
        by simp
      also have "... = 2 * (d1 * sum f1 {a \<in> S. f1 a \<noteq> 0})" by simp
      also from d21 have "... = 2 * (d2 * sum f2 {a \<in> S. f1 a \<noteq> 0})" by simp
      also have "... = d2 * (2 * sum f2 {a \<in> S. f1 a \<noteq> 0})" by simp
      finally show "d2 * sum f2 {a \<in> UNIV. f1 a \<noteq> 0} < ..." .
    qed
  qed

  fix S
  {
    assume "isWeightedMajority f1 S"
    from p [OF this d1 d2 eq]
    show "isWeightedMajority f2 S".
  next
    assume "isWeightedMajority f2 S"
    from p [OF this d2 d1 sym [OF eq]]
    show "isWeightedMajority f1 S".
  }
qed

end
