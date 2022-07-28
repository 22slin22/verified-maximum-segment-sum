theory MaximumSegmentSum
  imports Main
begin

fun mas_index_naive_aux :: "int list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int" where
  "mas_index_naive_aux xs 0 h = sum ((!) xs) {0..<h}"
| "mas_index_naive_aux xs (Suc l) h = max (sum ((!) xs) {(Suc l)..<h}) (mas_index_naive_aux xs l h)"

fun mas_index_naive :: "int list \<Rightarrow> nat \<Rightarrow> int" where
  "mas_index_naive xs 0 = 0"
| "mas_index_naive xs (Suc h) = max (mas_index_naive xs h) (mas_index_naive_aux xs (Suc h) (Suc h))"



fun mss_rec_naive_aux :: "int list \<Rightarrow> int" where
  "mss_rec_naive_aux [] = 0"
| "mss_rec_naive_aux (x#xs) = max 0 (x + mss_rec_naive_aux xs)"

fun mss_rec_naive :: "int list \<Rightarrow> int" where
  "mss_rec_naive [] = 0"
| "mss_rec_naive (x#xs) = max (mss_rec_naive_aux (x#xs)) (mss_rec_naive xs)"

value "mss_rec_naive [-1, 2, -1, 2]"

lemma mss_rec_naive_aux_pos: "mss_rec_naive_aux xs \<ge> 0"
  by (induction xs) auto

lemma mss_rec_naive_aux_append: "mss_rec_naive_aux (xs @ ys) \<ge> mss_rec_naive_aux xs"
  by (induction xs) (auto simp: mss_rec_naive_aux_pos)

definition fronts :: "int list \<Rightarrow> int list set" where
  "fronts xs = {as. \<exists>bs. xs = as @ bs}"

definition "front_sums xs \<equiv> sum_list ` fronts xs"

lemma fronts_cons: "fronts (x#xs) = ((#) x) ` fronts xs \<union> {[]}" (is "?l = ?r")
proof
  show "?l \<subseteq> ?r"
  proof
    fix as
    assume as_in_l: "as \<in> ?l"
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

lemma mss_rec_naive_aux: "mss_rec_naive_aux xs = Max (front_sums xs)"
  by (induction xs) (simp add: front_sums_def fronts_def, auto simp: max_front_sum)


definition mids :: "int list \<Rightarrow> int list set" where
  "mids xs \<equiv> {bs. \<exists>as cs. xs = as @ bs @ cs}"

definition "mid_sums xs \<equiv> sum_list ` mids xs"

lemma mids_cons: "mids (x#xs) = ((#) x) ` fronts xs \<union> {[]}" (is "?l = ?r")
proof
  show "?l \<subseteq> ?r"
  proof
    fix as
    assume as_in_l: "as \<in> ?l"
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

lemma mss_rec_naive_aux: "mss_rec_naive_aux xs = Max (front_sums xs)"
  by (induction xs) (simp add: front_sums_def fronts_def, auto simp: max_front_sum)


end