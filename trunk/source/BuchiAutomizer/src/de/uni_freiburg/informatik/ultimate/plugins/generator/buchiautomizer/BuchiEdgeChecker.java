package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer;

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.EdgeChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;

/**
 * EdgeChecker that is aware of the special rankDecrease predicates (e.g., the
 * Honda Predicate). If one of these Predicates occurs on the left-hand side of
 * an Hoare triple check (i.e., is Precondition or HierPred) we have to replace
 * it by the corresponding rankEqual predicate.
 * 
 * E.g., f(x)<oldrk /\ oldrk>=0 is replaced by f(x)<=oldrk.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class BuchiEdgeChecker extends EdgeChecker {

	private final Map<IPredicate,IPredicate> m_RankDecrease2RankEquality = 
			new HashMap<IPredicate,IPredicate>();

	public BuchiEdgeChecker(SmtManager smtManager, 
			BuchiModGlobalVarManager buchiModGlobalVarManager) {
		super(smtManager, buchiModGlobalVarManager);
	}
	
	public void putDecreaseEqualPair(IPredicate rankDecreaseAndBound, IPredicate rankEquality) {
		m_RankDecrease2RankEquality.put(rankDecreaseAndBound, rankEquality);
	}

	
	private IPredicate replaceIfRankDecreasePredicate(IPredicate p) {
		IPredicate rankEq = m_RankDecrease2RankEquality.get(p);
		if (rankEq == null) {
			return p;
		} else {
			return rankEq;
		}
	}
	
	
	@Override
	public LBool assertPrecondition(IPredicate p) {
		p = replaceIfRankDecreasePredicate(p);
		return super.assertPrecondition(p);
	}




	@Override
	public LBool assertHierPred(IPredicate p) {
		p = replaceIfRankDecreasePredicate(p);
		return super.assertHierPred(p);
	}




	@Override
	public LBool sdecInternalSelfloop(IPredicate p, CodeBlock cb) {
		return null; 
	}
	@Override
	public LBool sdecCallSelfloop(IPredicate p, CodeBlock cb) {
		return null;	}
	@Override
	public LBool sdecReturnSelfloopPre(IPredicate p, Return ret) {
		return null;	}
	@Override
	public LBool sdecReturnSelfloopHier(IPredicate p, Return ret) {
		return null;
	}
	@Override
	public LBool sdecInternalToFalse(IPredicate pre, CodeBlock cb) {
		return null;
	}
	@Override
	public LBool sdecInteral(IPredicate pre, CodeBlock cb, IPredicate post) {
		return null;
	}
	@Override
	public LBool sdLazyEcInteral(IPredicate pre, CodeBlock cb, IPredicate post) {
		return null;
	}
	@Override
	public LBool sdecCall(IPredicate pre, CodeBlock cb, IPredicate post) {
		return null;
	}
	@Override
	public LBool sdLazyEcCall(IPredicate pre, Call cb, IPredicate post) {
		return null;
	}
	@Override
	public LBool sdecReturn(IPredicate pre, IPredicate hier, CodeBlock cb,
			IPredicate post) {
		return null;
	}
	@Override
	public LBool sdLazyEcReturn(IPredicate pre, IPredicate hier, Return cb,
			IPredicate post) {
		return null;
	}

	

}
