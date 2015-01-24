package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer;

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.EdgeChecker.EdgeCheckerBenchmarkGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IHoareTripleChecker;

/**
 * HoareTripleChecker that is aware of the special rankDecrease predicates 
 * (e.g., the Honda Predicate). If one of these Predicates occurs on the 
 * left-hand side of a Hoare triple check (i.e., is Precondition or HierPred) 
 * we have to replace it by the corresponding rankEqual predicate.
 * 
 * E.g., f(x)<oldrk /\ oldrk>=0 is replaced by f(x)<=oldrk.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class BuchiHoareTripleChecker implements IHoareTripleChecker {

	private final Map<IPredicate,IPredicate> m_RankDecrease2RankEquality = 
			new HashMap<IPredicate,IPredicate>();
	private final IHoareTripleChecker m_IHoareTripleChecker;

	
	public BuchiHoareTripleChecker(IHoareTripleChecker iHoareTripleChecker) {
		super();
		m_IHoareTripleChecker = iHoareTripleChecker;
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
	public Validity checkInternal(IPredicate pre, CodeBlock cb, IPredicate succ) {
		pre = replaceIfRankDecreasePredicate(pre);
		return m_IHoareTripleChecker.checkInternal(pre, cb, succ);
	}

	@Override
	public Validity checkCall(IPredicate pre, CodeBlock cb, IPredicate succ) {
		pre = replaceIfRankDecreasePredicate(pre);
		return m_IHoareTripleChecker.checkCall(pre, cb, succ);
	}

	@Override
	public Validity checkReturn(IPredicate preLin, IPredicate preHier,
			CodeBlock cb, IPredicate succ) {
		preLin = replaceIfRankDecreasePredicate(preLin);
		preHier = replaceIfRankDecreasePredicate(preHier);
		return m_IHoareTripleChecker.checkReturn(preLin, preHier, cb, succ);
	}


	public EdgeCheckerBenchmarkGenerator getEdgeCheckerBenchmark() {
		return m_IHoareTripleChecker.getEdgeCheckerBenchmark();
	}

	

}
