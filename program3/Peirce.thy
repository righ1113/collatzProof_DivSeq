theory Peirce
imports Main
begin


theorem peirce []:
  "\<forall>x. (\<forall>z. \<not>(P z \<longrightarrow> Q z)) \<longrightarrow> (\<forall>n. (\<forall>z. (P z \<longrightarrow> Q z)) \<longrightarrow> P n) \<longrightarrow> P x"
  (* sledgehammer *)
  apply auto
  done


end
