theory Synod
  imports PropNo
begin

locale synodL
  = propNoL lt
  for lt :: "'pid \<Rightarrow> 'pid \<Rightarrow> bool" (infixl "\<prec>" 50) 
  +

  fixes quorum_proposer :: "'pid \<Rightarrow> 'aid set \<Rightarrow> bool"
  fixes quorum_learner  :: "'pid \<Rightarrow> 'aid set \<Rightarrow> bool"
  fixes promised_free :: "'aid \<Rightarrow> 'pid \<Rightarrow> bool"
  fixes promised_prev :: "'aid \<Rightarrow> 'pid \<Rightarrow> 'pid \<Rightarrow> bool"
  fixes proposed :: "'pid \<Rightarrow> bool"
  fixes accepted :: "'aid \<Rightarrow> 'pid \<Rightarrow> bool"
  fixes chosen :: "'pid \<Rightarrow> bool"
  fixes value_proposed :: "'pid \<Rightarrow> 'value"

  fixes promised :: "'aid \<Rightarrow> 'pid \<Rightarrow> bool"
  defines "promised a p == promised_free a p \<or> (\<exists> p1. promised_prev a p p1)"

  fixes forced :: "'pid \<Rightarrow> 'aid set \<Rightarrow> 'pid set"
  defines "forced p S == { p1. \<exists> a \<in> S. promised_prev a p p1 }"

  assumes quorum_inter:
   "\<lbrakk> quorum_proposer p1 SP; quorum_learner p0 SL; chosen p0; proposed p1; p0 \<prec> p1 \<rbrakk>
    \<Longrightarrow> SP \<inter> SL \<noteq> {}"

  assumes quorum_nonempty: "quorum_learner p SL \<Longrightarrow> SL \<noteq> {}"

  assumes proposed_quorum:
    "proposed p \<Longrightarrow> EX S. quorum_proposer p S
      \<and> (\<forall> a \<in> S. promised a p)
      \<and> (forced p S = {} \<or> value_proposed p = value_proposed (max_of (forced p S)))"

  assumes proposed_finite: "finite {p. proposed p}"

  assumes promised_free:
    "\<lbrakk> promised_free a p0; accepted a p1 \<rbrakk> \<Longrightarrow> p0 \<preceq> p1"

  assumes promised_prev_accepted:
    "promised_prev a p0 p1 \<Longrightarrow> accepted a p1"
  assumes promised_prev_prev:
    "promised_prev a p0 p1 \<Longrightarrow> p1 \<prec> p0"
  assumes promised_prev_max:
    "\<lbrakk> promised_prev a p0 p1; accepted a p2; p2 \<prec> p0 \<rbrakk> \<Longrightarrow> p2 \<preceq> p1"

  assumes accepts_proposed:
    "accepted a p \<Longrightarrow> proposed p"

  assumes chosen_quorum:
    "chosen p \<Longrightarrow> EX S. quorum_learner p S \<and> (ALL a:S. accepted a p)"

lemma (in synodL) promised_some_none:
  assumes "promised_prev a p0 p1" "promised_free a p0"
  shows P
proof -
  have "promised_prev a p0 p1 \<longrightarrow> \<not> promised_free a p0"
    by (metis promised_free promised_prev_accepted promised_prev_prev propNo_leE propNo_lt_not_ge_E)
  with assms show P by simp
qed

lemma (in synodL) promised_prev_fun:
  assumes "promised_prev a p0 p1" "promised_prev a p0 p2"
  shows "p1 = p2"
  by (metis assms irreflexive promised_prev_accepted promised_prev_max promised_prev_prev propNo_leE propNo_trans_lt_le)

lemma (in synodL) forced_proposed: "forced p S \<subseteq> {p. proposed p}"
  by (auto simp add: forced_def intro: accepts_proposed promised_prev_accepted)

lemma (in synodL) finite_forced: "finite (forced p S)"
  by (intro finite_subset [OF _ proposed_finite] forced_proposed)

lemma (in synodL) p2b:
  assumes chosen: "chosen p0" and proposed_p1: "proposed p1" and p01: "p0 \<prec> p1"
  shows "value_proposed p0 = value_proposed p1"
using wf proposed_p1 p01
proof (induct p1)
  case (less p2)
  hence p02: "p0 \<prec> p2" and proposed_p2: "proposed p2"
    and props_eq: "\<And>p. \<lbrakk> p0 \<preceq> p; p \<prec> p2; proposed p \<rbrakk> \<Longrightarrow> value_proposed p = value_proposed p0" by auto

  from proposed_quorum [OF proposed_p2] obtain SP where SP_quorum: "quorum_proposer p2 SP"
    and SP_promised: "\<And>a. a \<in> SP \<Longrightarrow> promised a p2"
    and free_or_forced: "forced p2 SP = {} \<or> value_proposed p2 = value_proposed (max_of (forced p2 SP))" by auto

  from chosen_quorum [OF chosen] obtain SL
    where SC_quorum: "quorum_learner p0 SL"
    and SC_accepts: "\<And>a. \<lbrakk> a \<in> SL \<rbrakk> \<Longrightarrow> accepted a p0" by auto

  from SP_quorum SC_quorum quorum_inter chosen proposed_p2 p02
  obtain a where aSP: "a \<in> SP" and aSL: "a \<in> SL"
    by (metis disjoint_iff_not_equal)

  from SP_promised [OF aSP]
  show ?case
  proof (unfold promised_def, elim disjE exE)
    assume "promised_free a p2"
    from promised_free [OF this SC_accepts [OF aSL]] p02 show ?thesis by auto
  next
    fix p3
    define p4 where "p4 == max_of (forced p2 SP)"

    assume pp: "promised_prev a p2 p3"
    with aSP have forced: "forced p2 SP \<noteq> {}" by (auto simp add: forced_def promised_def)
    with free_or_forced
    have "value_proposed p2 = value_proposed p4" by (simp add: p4_def)

    also have "... = value_proposed p0"
    proof (intro props_eq)
      from promised_prev_max [OF pp SC_accepts [OF aSL] p02] have p03: "p0 \<preceq> p3" .
      also from aSP pp have "p3 \<preceq> p4"
        by (unfold p4_def, intro max_of_max finite_forced, auto simp add: forced_def)
      finally show "p0 \<preceq> ...".

      have "p4 \<in> forced p2 SP"
        by (unfold p4_def, intro max_of_mem finite_forced forced)

      then obtain a4 where a4SP: "a4 \<in> SP" and a4p: "promised_prev a4 p2 p4"
        by (auto simp add: forced_def)

      from promised_prev_prev [OF a4p] show "p4 \<prec> p2" .
      from a4p show "proposed p4" by (intro accepts_proposed promised_prev_accepted)
    qed

    finally show ?thesis by simp
  qed
qed

lemma (in synodL)
  assumes "chosen p0" and "accepted a1 p1" and "p0 \<prec> p1"
  shows p2a: "value_proposed p0 = value_proposed p1"
  using assms by (intro p2b accepts_proposed)

lemma (in synodL)
  assumes chosen0: "chosen p0"
  assumes chosen1: "chosen p1"
  assumes p01: "p0 \<prec> p1"
  shows p2: "value_proposed p0 = value_proposed p1"
proof -
  from chosen_quorum [OF chosen1]
  obtain S where QL: "quorum_learner p1 S" and acc: "\<And>a. a \<in> S \<Longrightarrow> accepted a p1" by auto
  from quorum_nonempty [OF QL] obtain a where aS: "a \<in> S" by auto
  show ?thesis by (metis p2a chosen0 p01 acc aS)
qed

theorem (in synodL)
  assumes "chosen p0" "chosen p1"
  shows synod_consistent: "value_proposed p0 = value_proposed p1"
  by (metis assms le_lt_eq p2 propNo_cases)

lemma (in synodL)
  assumes "quorum_learner p0 S"
  assumes "\<And>a. a \<in> S \<Longrightarrow> accepted a p0"
  assumes p0_quorum_inter: "\<And> SP SL p1.
    \<lbrakk> quorum_proposer p1 SP; quorum_learner p0 SL; proposed p1; p0 \<prec> p1 \<rbrakk>
    \<Longrightarrow> SP \<inter> SL \<noteq> {}"
  shows synod_add_chosen: "synodL lt quorum_proposer quorum_learner promised_free promised_prev
  proposed accepted (%p. p = p0 \<or> chosen p) value_proposed"
using accepts_proposed chosen_quorum promised_free
  promised_prev_accepted promised_prev_max promised_prev_prev 
  proposed_quorum proposed_finite quorum_inter 
  quorum_nonempty assms
apply unfold_locales
apply (fold promised_def forced_def max_of_def)
proof -
  fix SP SL p0a p1
  assume "quorum_proposer p1 SP" "quorum_learner p0a SL" "proposed p1" "p0a \<prec> p1" "p0a = p0 \<or> chosen p0a"
  thus "SP \<inter> SL \<noteq> {}" by (metis p0_quorum_inter quorum_inter)
qed auto

end
