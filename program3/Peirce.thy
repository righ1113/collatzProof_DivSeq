theory Peirce
imports Main
begin


theorem peirce []:
  "\<forall>x::nat. \<not>(\<forall>z::nat. (P z \<longrightarrow> Q z))
     \<longrightarrow> (\<forall>z::nat. (P z \<longrightarrow> Q z) \<longrightarrow> (\<forall>n::nat. P n))
       \<longrightarrow> P x"
  (* sledgehammer *)
  apply auto
  done


end
