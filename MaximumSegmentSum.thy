theory MaximumSegmentSum
  imports Main
begin

fun mss_rec_naive_aux :: "int list \<Rightarrow> int" where
  "mss_rec_naive_aux [] = 0"
| "mss_rec_naive_aux (x#xs) = max 0 (x + mss_rec_naive_aux xs)"

fun mss_rec_naive :: "int list \<Rightarrow> int" where
  "mss_rec_naive [] = 0"
| "mss_rec_naive (x#xs) = max (mss_rec_naive_aux (x#xs)) (mss_rec_naive xs)"

definition fronts :: "int list \<Rightarrow> int list set" where
  "fronts xs = {as. \<exists>bs. xs = as @ bs}"

definition "front_sums xs \<equiv> sum_list ` fronts xs"

lemma fronts_cons: "fronts (x#xs) = ((#) x) ` fronts xs \<union> {[]}" (is "?l = ?r")
proof
  show "?l \<subseteq> ?r"
  proof
    fix as assume "as \<in> ?l"
    then show "as \<in> ?r" by (cases as) (auto simp: fronts_def)
  qed
  show "?r \<subseteq> ?l" unfolding fronts_def by auto
qed

lemma front_sums_cons: "front_sums (x#xs) = (+) x ` front_sums xs \<union> {0}"
proof -
  have "sum_list ` ((#) x) ` fronts xs = (+) x ` front_sums xs" unfolding front_sums_def by force
  then show ?thesis by (simp add: front_sums_def fronts_cons)
qed

lemma finite_fronts: "finite (fronts xs)"
  by (induction xs) (simp add: fronts_def, simp add: fronts_cons)

lemma finite_front_sums: "finite (front_sums xs)"
  using front_sums_def finite_fronts by simp

lemma front_sums_not_empty: "front_sums xs \<noteq> {}"
  unfolding front_sums_def fronts_def using image_iff by fastforce

lemma max_front_sum: "Max (front_sums (x#xs)) = max 0 (x + Max (front_sums xs))"
  using finite_front_sums front_sums_not_empty by (auto simp add: front_sums_cons hom_Max_commute)

lemma mss_rec_naive_aux_front_sums: "mss_rec_naive_aux xs = Max (front_sums xs)"
  by (induction xs) (simp add: front_sums_def fronts_def, auto simp: max_front_sum)

lemma front_sums: "front_sums xs = {s. \<exists>as bs. xs = as @ bs \<and> s = sum_list as}"
  unfolding front_sums_def fronts_def by auto

lemma mss_rec_naive_aux: "mss_rec_naive_aux xs = Max {s. \<exists>as bs. xs = as @ bs \<and> s = sum_list as}"
  using front_sums mss_rec_naive_aux_front_sums by simp
  


definition mids :: "int list \<Rightarrow> int list set" where
  "mids xs \<equiv> {bs. \<exists>as cs. xs = as @ bs @ cs}"

definition "mid_sums xs \<equiv> sum_list ` mids xs"

lemma fronts_mids: "bs \<in> fronts xs \<Longrightarrow> bs \<in> mids xs"
  unfolding fronts_def mids_def by auto

lemma mids_mids_cons: "bs \<in> mids xs \<Longrightarrow> bs \<in> mids (x#xs)"
proof-
  fix bs assume "bs \<in> mids xs"
  then obtain as cs where "xs = as @ bs @ cs" unfolding mids_def by blast
  then have "x # xs = (x#as) @ bs @ cs" by simp
  then show "bs \<in> mids (x#xs)" unfolding mids_def by blast
qed

lemma mids_cons: "mids (x#xs) = fronts (x#xs) \<union> mids xs" (is "?l = ?r")
proof
  show "?l \<subseteq> ?r"
  proof
    fix bs assume "bs \<in> ?l"
    then obtain as cs where as_bs_cs: "(x#xs) = as @ bs @ cs" unfolding mids_def by blast
    then show "bs \<in> ?r"
    proof (cases as)
      case Nil
      then have "bs \<in> fronts (x#xs)" by (simp add: fronts_def as_bs_cs)
      then show ?thesis by simp
    next
      case (Cons a as')
      then have "xs = as' @ bs @ cs" using as_bs_cs by simp
      then show ?thesis unfolding mids_def by auto
    qed
  qed
  show "?r \<subseteq> ?l" using fronts_mids mids_mids_cons by auto
qed

lemma mid_sums_cons: "mid_sums (x#xs) = front_sums (x#xs) \<union> mid_sums xs"
  unfolding mid_sums_def by (auto simp: mids_cons front_sums_def)

lemma finite_mids: "finite (mids xs)"
  by (induction xs) (simp add: mids_def, simp add: mids_cons finite_fronts)

lemma finite_mid_sums: "finite (mid_sums xs)"
  by (simp add: mid_sums_def finite_mids)

lemma mid_sums_not_empty: "mid_sums xs \<noteq> {}"
  unfolding mid_sums_def mids_def by blast

lemma max_mid_sums_cons: "Max (mid_sums (x#xs)) = max (Max (front_sums (x#xs))) (Max (mid_sums xs))"
  by (auto simp: mid_sums_cons Max_Un finite_front_sums finite_mid_sums front_sums_not_empty mid_sums_not_empty)

lemma mss_rec_naive_max_mid_sum: "mss_rec_naive xs = Max (mid_sums xs)"
  by (induction xs) (simp add: mid_sums_def mids_def, auto simp: max_mid_sums_cons mss_rec_naive_aux front_sums)

lemma mid_sums: "mid_sums xs = {s. \<exists>as bs cs. xs = as @ bs @ cs \<and> s = sum_list bs}"
  by (auto simp: mid_sums_def mids_def)

theorem mss_rec_naive: "mss_rec_naive xs = Max {s. \<exists>as bs cs. xs = as @ bs @ cs \<and> s = sum_list bs}"
  unfolding mss_rec_naive_max_mid_sum mid_sums by simp


fun kadane :: "int list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "kadane [] cur m = max cur m"
| "kadane (x#xs) cur m =
    (let cur' = max x (cur + x) in
      kadane xs cur' (max m cur'))"

end