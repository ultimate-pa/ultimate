package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.EdgeChecker.EdgeCheckerBenchmarkGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;

public class EfficientHoareTripleChecker implements IHoareTripleChecker {
	private static final boolean m_ReviewSmtResultsIfAssertionsEnabled = true;
	private static final boolean m_ReviewSdResultsIfAssertionsEnabled = true;
	
	private final IHoareTripleChecker m_SmtBasedHoareTripleChecker;
	private final SimpleDataflowHoareTripleChecker m_SdHoareTripleChecker;
	private final IHoareTripleChecker m_hoareTripleCheckerForReview;
	
	

	public EfficientHoareTripleChecker(
			IHoareTripleChecker smtBasedHoareTripleChecker, 
			ModifiableGlobalVariableManager modGlobVarManager, 
			PredicateUnifier predicateUnifier, 
			SmtManager smtManager) {
		super();
		m_SmtBasedHoareTripleChecker = smtBasedHoareTripleChecker;
		m_SdHoareTripleChecker = new SimpleDataflowHoareTripleChecker(modGlobVarManager, predicateUnifier);
		m_hoareTripleCheckerForReview = new MonolithicHoareTripleChecker(smtManager);
	}

	@Override
	public Validity checkInternal(IPredicate pre, CodeBlock cb, IPredicate succ) {
		final Validity sdResult = m_SdHoareTripleChecker.checkInternal(pre, cb, succ);
		if (sdResult != Validity.UNKNOWN) {
			if (m_ReviewSdResultsIfAssertionsEnabled) {
				Validity reviewResult = m_hoareTripleCheckerForReview.checkInternal(pre, cb, succ);
				assert resultCompatible(sdResult, reviewResult);
			}
			return sdResult;
		} else {
			Validity result = m_SmtBasedHoareTripleChecker.checkInternal(pre, cb, succ);
			if (m_ReviewSmtResultsIfAssertionsEnabled) {
				Validity reviewResult = m_hoareTripleCheckerForReview.checkInternal(pre, cb, succ);
				assert resultCompatible(sdResult, reviewResult);
			}
			return result;
		}
	}

	@Override
	public Validity checkCall(IPredicate pre, CodeBlock cb, IPredicate succ) {
		final Validity sdResult = m_SdHoareTripleChecker.checkCall(pre, cb, succ);
		if (sdResult != Validity.UNKNOWN) {
			if (m_ReviewSdResultsIfAssertionsEnabled) {
				Validity reviewResult = m_hoareTripleCheckerForReview.checkCall(pre, cb, succ);
				assert resultCompatible(sdResult, reviewResult);
			}
			return sdResult;
		} else {
			Validity result = m_SmtBasedHoareTripleChecker.checkCall(pre, cb, succ);
			if (m_ReviewSmtResultsIfAssertionsEnabled) {
				Validity reviewResult = m_hoareTripleCheckerForReview.checkCall(pre, cb, succ);
				assert resultCompatible(sdResult, reviewResult);
			}
			return result;
		}
	}

	@Override
	public Validity checkReturn(IPredicate preLin, IPredicate preHier,
			CodeBlock cb, IPredicate succ) {
		final Validity sdResult = m_SdHoareTripleChecker.checkReturn(preLin, preHier, cb, succ);
		if (sdResult != Validity.UNKNOWN) {
			if (m_ReviewSdResultsIfAssertionsEnabled) {
				Validity reviewResult = m_hoareTripleCheckerForReview.checkReturn(preLin, preHier, cb, succ);
				assert resultCompatible(sdResult, reviewResult);
			}
			return sdResult;
		} else {
			Validity result = m_SmtBasedHoareTripleChecker.checkReturn(preLin, preHier, cb, succ);
			if (m_ReviewSmtResultsIfAssertionsEnabled) {
				Validity reviewResult = m_hoareTripleCheckerForReview.checkReturn(preLin, preHier, cb, succ);
				assert resultCompatible(sdResult, reviewResult);
			}
			return result;
		}
	}

	@Override
	public EdgeCheckerBenchmarkGenerator getEdgeCheckerBenchmark() {
		return m_SmtBasedHoareTripleChecker.getEdgeCheckerBenchmark();
	}
	
	
	private boolean resultCompatible(Validity result, Validity reviewResult) {
		if (resultCompatibleHelper(result, reviewResult)) {
			return true;
		} else {
			throw new AssertionError("Result: " + result 
					+ "  Review result: " + reviewResult);
		}
	}
	
	/**
	 * Return true if results are compatible or one is UNKNOWN
	 */
	private boolean resultCompatibleHelper(Validity validity1, Validity validity2) {
		switch (validity1) {
		case VALID:
			return (validity2 == Validity.VALID || validity2 == Validity.UNKNOWN);
		case INVALID:
			return (validity2 == Validity.INVALID || validity2 == Validity.UNKNOWN);
		case UNKNOWN:
			return true;
		default:
			throw new UnsupportedOperationException();
		}
	}

}
