theory Peirce
imports Main
begin


theorem peirce []:
  "x \<longrightarrow> \<not>(z \<longrightarrow> (P z \<longrightarrow> Q z)) \<longrightarrow> (n \<longrightarrow> (z \<longrightarrow> (P z \<longrightarrow> Q z)) \<longrightarrow> P n) \<longrightarrow> P x"
  (* sledgehammer *)
  apply auto
  done


end
