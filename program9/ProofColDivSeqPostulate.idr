module ProofColDivSeqPostulate

%default total
%access export


--            from ProofColDivSeqBase
-- ########################################
postulate JusticeWormHole     : Type
postulate BaseCaseFlg         : Type
postulate NotStraddleSign     : Type
postulate trueBaseCaseFlg     : BaseCaseFlg
postulate trueNotStraddleSign : NotStraddleSign
postulate prop : (BaseCaseFlg, NotStraddleSign) -> JusticeWormHole
-- ########################################



--            from ProofColDivSeqMain
-- ########################################
-- ########################################



--            from sub0xxxxx
-- ########################################
-- ########################################



