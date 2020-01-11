theory Checkmate
imports Main
begin


theorem eqIntro:
  "(A \<longrightarrow> B)
    \<longrightarrow> (B \<longrightarrow> A)
      \<longrightarrow> (A = B)"
  apply auto
  done

theorem bad:
  "((\<forall>n.(F n \<longrightarrow> A n)) \<longrightarrow> (\<forall>n. F n))
    \<longrightarrow> (\<forall>k. F k) = (\<forall>k. A k)
      \<longrightarrow> A 0 \<and> A 1 \<and> A 2 \<and> A 3 \<and> A 4 \<and> A 5
        \<longrightarrow> F 0 \<and> F 1 \<and> F 2 \<and> F 3 \<and> F 4 \<and> F 5
          \<longrightarrow> (\<forall>n. F n)"
  (* sledgehammer *)
  apply auto
  oops

theorem good:
  "((\<forall>n.(F n \<longrightarrow> A n)) \<longrightarrow> (\<forall>n. F n))
    \<longrightarrow> F = A
       \<longrightarrow> (\<forall>n. F n)"
  (* sledgehammer *)
  apply auto
  done


end



