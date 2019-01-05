theory PropNo
  imports Main
begin

locale propNoL =
  fixes lt :: "'pid \<Rightarrow> 'pid \<Rightarrow> bool" (infixl "\<prec>" 50)
  assumes trans: "trans {(p,q). p \<prec> q}"
  assumes wf: "wf {(p,q). p \<prec> q}"
  assumes total: "p \<prec> q \<or> p = q \<or> q \<prec> p"

lemma (in propNoL) irreflexive [simp]: "\<And>p. \<not> p \<prec> p"
  by (meson CollectI case_prodI local.wf wf_asym)

definition (in propNoL)
  le :: "'pid \<Rightarrow> 'pid \<Rightarrow> bool" (infixl "\<preceq>" 50)
  where le_lt_eq [simp]: "\<And>p q. p \<preceq> q = (p \<prec> q \<or> p = q)"

definition (in propNoL) "max_of S == THE p. p \<in> S \<and> (\<forall> p'. p' \<in> S \<longrightarrow> p' \<preceq> p)"

lemma (in propNoL) propNo_cases:
  assumes lt: "p1 \<prec> p2  \<Longrightarrow> P"
    and eq: "p1 = p2  \<Longrightarrow> P"
    and gt: "p2 \<prec> p1  \<Longrightarrow> P"
  shows P
  using assms total by auto

lemma (in propNoL) propNo_leE [elim]:
  assumes le1: "p1 \<preceq> p2"
    and lt: "p1 \<prec> p2 \<Longrightarrow> P"
    and eq: "p1 = p2 \<Longrightarrow> P"
  shows P
  using assms local.le_lt_eq by auto

lemma (in propNoL) propNo_trans_lt_lt [trans]:
  "p1 \<prec> p2 \<Longrightarrow> p2 \<prec> p3 \<Longrightarrow> p1 \<prec> p3"
  using trans by (elim transE, auto)

lemma (in propNoL) propNo_lt_not_ge_E [elim]:
  assumes lt: "p1 \<prec> p2"
    and not_gt: "\<lbrakk> p1 \<noteq> p2; \<not>(p2 \<prec> p1) \<rbrakk>  \<Longrightarrow> P"
  shows P
  by (metis lt not_gt irreflexive propNo_trans_lt_lt)

lemma (in propNoL) propNo_trans_lt_le [trans]:
  "p1 \<prec> p2 \<Longrightarrow> p2 \<preceq> p3 \<Longrightarrow> p1 \<prec> p3"
  by (metis le_lt_eq propNo_trans_lt_lt)

lemma (in propNoL) propNo_trans_le_lt [trans]:
  "p1 \<preceq> p2 \<Longrightarrow> p2 \<prec> p3 \<Longrightarrow> p1 \<prec> p3"
  by (metis le_lt_eq propNo_trans_lt_lt)

lemma (in propNoL) propNo_trans_le_le [trans]:
  assumes p12: "p1 \<preceq> p2" and p23: "p2 \<preceq> p3"
  shows "p1 \<preceq> p3"
  by (metis le_lt_eq p12 p23 propNo_trans_lt_le)

lemma (in propNoL)
  assumes finite: "finite S" and nonempty: "S \<noteq> {}"
  shows max_of_mem: "max_of S \<in> S"
    and max_of_max_nonempty: "\<And>p. p \<in> S \<Longrightarrow> p \<preceq> max_of S"
proof -
  from finite nonempty
  have "\<exists> p_max \<in> S. \<forall> p \<in> S. p \<preceq> p_max"
  proof (induct)
    case (insert p S)
    show ?case
    proof (cases "S = {}")
      case True thus ?thesis by auto
    next
      case False
      with insert
      obtain p_max where p_max_S: "p_max \<in> S" and p_max_max: "\<And>p. p \<in> S \<Longrightarrow> p \<preceq> p_max" by auto
      show ?thesis
      proof (cases "p \<preceq> p_max")
        case True
        with p_max_S p_max_max
        show ?thesis
          by (intro bexI [where x = p_max], auto)
      next
        case False
        hence lt: "p_max \<prec> p" using propNo_cases by auto
        with p_max_max show ?thesis using propNo_trans_le_lt by auto
      qed
    qed
  qed simp
  then obtain p_max where mem: "p_max \<in> S" and max: "\<And>p. p \<in> S \<Longrightarrow> p \<preceq> p_max" by auto
  have "max_of S = p_max"
  proof (unfold max_of_def, intro the_equality conjI mem allI impI max)
    fix p
    assume "p \<in> S \<and> (\<forall>p'. p' \<in> S \<longrightarrow> p' \<preceq> p)"
    with mem max show "p = p_max" by (metis le_lt_eq propNo_lt_not_ge_E)
  qed
  with mem max show "max_of S \<in> S" " \<And>p. p \<in> S \<Longrightarrow> p \<preceq> max_of S" by auto
qed

lemma (in propNoL)
  assumes finite: "finite S" and pS: "p \<in> S"
  shows max_of_max: "p \<preceq> max_of S"
  using pS
  by (intro max_of_max_nonempty finite pS, auto)

lemma (in propNoL)
  assumes nonempty: "S1 \<noteq> {}" and finite: "finite S2" and subset: "S1 \<subseteq> S2"
  shows max_of_mono: "max_of S1 \<preceq> max_of S2"
  by (intro max_of_max set_mp [OF subset] max_of_mem finite_subset [OF subset] finite nonempty)

lemma (in propNoL)
  assumes nonempty: "S1 \<noteq> {}" and finite1: "finite S1" and finite2: "finite S2"
  assumes dominates: "\<forall> p1 \<in> S1. \<exists> p2 \<in> S2. p1 \<preceq> p2"
  shows max_of_dominated: "max_of S1 \<preceq> max_of S2"
proof -
  have "max_of S1 \<in> S1" by (intro max_of_mem finite1 nonempty)
  with dominates obtain p2 where p2S: "p2 \<in> S2" and p12: "max_of S1 \<preceq> p2" by auto
  note p12
  also note max_of_max [OF finite2 p2S] 
  finally show ?thesis .
qed

lemma (in propNoL) max_of_singleton[simp]: "max_of {p} = p"
proof -
  have "max_of {p} \<in> {p}" by (intro max_of_mem, auto)
  thus ?thesis by simp
qed

end