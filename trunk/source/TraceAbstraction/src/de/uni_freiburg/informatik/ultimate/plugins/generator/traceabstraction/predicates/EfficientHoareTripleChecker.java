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
	private final SdHoareTripleChecker m_SdHoareTripleChecker;
	private final IHoareTripleChecker m_hoareTripleCheckerForReview;
	
	

	public EfficientHoareTripleChecker(
			IHoareTripleChecker smtBasedHoareTripleChecker, 
			ModifiableGlobalVariableManager modGlobVarManager, 
			PredicateUnifier predicateUnifier, 
			SmtManager smtManager) {
		super();
		m_SmtBasedHoareTripleChecker = smtBasedHoareTripleChecker;
		m_SdHoareTripleChecker = new SdHoareTripleChecker(modGlobVarManager, predicateUnifier);
		m_hoareTripleCheckerForReview = new MonolithicHoareTripleChecker(smtManager);
	}

	@Override
	public Validity checkInternal(IPredicate pre, CodeBlock cb, IPredicate succ) {
		final Validity sdResult = m_SdHoareTripleChecker.checkInternal(pre, cb, succ);
		if (sdResult != Validity.UNKNOWN) {
			if (m_ReviewSdResultsIfAssertionsEnabled) {
				assert reviewInductiveInternal(pre, cb, succ, sdResult);
			}
			return sdResult;
		} else {
			Validity result = m_SmtBasedHoareTripleChecker.checkInternal(pre, cb, succ);
			if (m_ReviewSmtResultsIfAssertionsEnabled) {
				assert reviewInductiveInternal(pre, cb, succ, result);
			}
			return result;
		}
	}

	@Override
	public Validity checkCall(IPredicate pre, CodeBlock cb, IPredicate succ) {
		final Validity sdResult = m_SdHoareTripleChecker.checkCall(pre, cb, succ);
		if (sdResult != Validity.UNKNOWN) {
			if (m_ReviewSdResultsIfAssertionsEnabled) {
				assert reviewInductiveCall(pre, cb, succ, sdResult);
			}
			return sdResult;
		} else {
			Validity result = m_SmtBasedHoareTripleChecker.checkCall(pre, cb, succ);
			if (m_ReviewSmtResultsIfAssertionsEnabled) {
				assert reviewInductiveCall(pre, cb, succ, result);
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
				assert reviewInductiveReturn(preLin, preHier, cb, succ, sdResult);
			}
			return sdResult;
		} else {
			Validity result = m_SmtBasedHoareTripleChecker.checkReturn(preLin, preHier, cb, succ);
			if (m_ReviewSmtResultsIfAssertionsEnabled) {
				assert reviewInductiveReturn(preLin, preHier, cb, succ, result);
			}
			return result;
		}
	}

	@Override
	public EdgeCheckerBenchmarkGenerator getEdgeCheckerBenchmark() {
		return m_SmtBasedHoareTripleChecker.getEdgeCheckerBenchmark();
	}
	
	
	private boolean reviewInductiveInternal(IPredicate state, CodeBlock cb, IPredicate succ, Validity result) {
		unlockSmtSolverWorkaround();
		Validity reviewResult = m_hoareTripleCheckerForReview.checkInternal(state, cb, succ);
		if (resultCompatibleHelper(result, reviewResult)) {
			return true;
		} else {
			throw new AssertionError("Result: " + result 
					+ "  Review result: " + reviewResult);
		}
	}
	
	private boolean reviewInductiveCall(IPredicate state, CodeBlock cb, IPredicate succ, Validity result) {
		unlockSmtSolverWorkaround();
		Validity reviewResult = m_hoareTripleCheckerForReview.checkCall(state, cb, succ);
		if (resultCompatibleHelper(result, reviewResult)) {
			return true;
		} else {
			throw new AssertionError("Result: " + result 
					+ "  Review result: " + reviewResult);
		}

	}
	
	private boolean reviewInductiveReturn(IPredicate state, IPredicate hier, CodeBlock cb, IPredicate succ, Validity result) {
		unlockSmtSolverWorkaround();
		Validity reviewResult = m_hoareTripleCheckerForReview.checkReturn(state, hier, cb, succ);
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
	
	/**
	 * Ask m_SmtBasedHoareTripleChecker to release its lock if it is an
	 * IncrementalHoareTripleChecker.
	 */
	public void unlockSmtSolverWorkaround() {
		if (m_SmtBasedHoareTripleChecker instanceof IncrementalHoareTripleChecker) {
			((IncrementalHoareTripleChecker) m_SmtBasedHoareTripleChecker).releaseLock();
		}
	}

}
