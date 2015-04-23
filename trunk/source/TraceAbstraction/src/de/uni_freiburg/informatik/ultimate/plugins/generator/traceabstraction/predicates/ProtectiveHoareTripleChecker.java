package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;

/**
 * IHoareTripleChecker that "protects" another IHoareTripleChecker from
 * intricate predicates.
 * The m_PredicateUnifer defines what an intricate predicates is.
 * If the Hoare triple that should be checked contains an intricate predicate
 * we return Validity.NOT_CHECKED. Otherwise we ask the "protected" 
 * IHoareTripleChecker.
 * @author Matthias Heizmann
 *
 */
public class ProtectiveHoareTripleChecker implements IHoareTripleChecker {
	
	private final IHoareTripleChecker m_ProtectedHoareTripleChecker;
	private final PredicateUnifier m_PredicateUnifer;
	
	public ProtectiveHoareTripleChecker(
			IHoareTripleChecker protectedHoareTripleChecker,
			PredicateUnifier predicateUnifer) {
		super();
		m_ProtectedHoareTripleChecker = protectedHoareTripleChecker;
		m_PredicateUnifer = predicateUnifer;
	}

	@Override
	public Validity checkInternal(IPredicate pre, CodeBlock cb, IPredicate succ) {
		if (m_PredicateUnifer.isIntricatePredicate(pre) || 
				m_PredicateUnifer.isIntricatePredicate(succ)) {
			return Validity.NOT_CHECKED;
		} else {
			return m_ProtectedHoareTripleChecker.checkInternal(pre, cb, succ);
		}
	}

	@Override
	public Validity checkCall(IPredicate pre, CodeBlock cb, IPredicate succ) {
		if (m_PredicateUnifer.isIntricatePredicate(pre) || 
				m_PredicateUnifer.isIntricatePredicate(succ)) {
			return Validity.NOT_CHECKED;
		} else {
			return m_ProtectedHoareTripleChecker.checkCall(pre, cb, succ);
		}
	}

	@Override
	public Validity checkReturn(IPredicate preLin, IPredicate preHier,
			CodeBlock cb, IPredicate succ) {
		if (m_PredicateUnifer.isIntricatePredicate(preLin) || 
				m_PredicateUnifer.isIntricatePredicate(preHier) || m_PredicateUnifer.isIntricatePredicate(succ)) {
			return Validity.NOT_CHECKED;
		} else {
			return m_ProtectedHoareTripleChecker.checkReturn(preLin, preHier, cb, succ);
		}
	}
	
	

	@Override
	public HoareTripleCheckerBenchmarkGenerator getEdgeCheckerBenchmark() {
		return m_ProtectedHoareTripleChecker.getEdgeCheckerBenchmark();
	}

	public IHoareTripleChecker getProtectedHoareTripleChecker() {
		return m_ProtectedHoareTripleChecker;
	}

	@Override
	public void releaseLock() {
		m_ProtectedHoareTripleChecker.releaseLock();
	}
	
	

}
