package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.EdgeChecker.EdgeCheckerBenchmarkGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.IPredicateCoverageChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;

/**
 * Hoare triple checker that uses only simple dataflow analysis to check 
 * triples. If this simple analysis is not able to determine the result
 * UNKNOWN is returned.
 * @author Matthias Heizmann
 *
 */
public class SimpleDataflowHoareTripleChecker implements IHoareTripleChecker {
	
	private final SdHoareTripleChecker m_SdHoareTripleChecker;
	private final IPredicateCoverageChecker m_PredicateCoverageChecker;
	private final IPredicate m_TruePredicate;
	private final IPredicate m_FalsePredicate;
	private final static boolean m_LazyChecks = false;
	private final InternalCheckHelper m_InternalCheckHelper = new InternalCheckHelper();
	private final CallCheckHelper m_CallCheckHelper = new CallCheckHelper();
	private final ReturnCheckHelper m_ReturnCheckHelper = new ReturnCheckHelper();

	
	public SimpleDataflowHoareTripleChecker(ModifiableGlobalVariableManager modGlobVarManager, 
			PredicateUnifier predicateUnifier) {
		m_PredicateCoverageChecker = predicateUnifier.getCoverageRelation();
		m_TruePredicate = predicateUnifier.getTruePredicate();
		m_FalsePredicate = predicateUnifier.getFalsePredicate();
		m_SdHoareTripleChecker = new SdHoareTripleChecker(modGlobVarManager, m_PredicateCoverageChecker);
		
	}
	
	
	@Override
	public Validity checkInternal(IPredicate pre, CodeBlock cb, IPredicate succ) {
		return m_InternalCheckHelper.check(pre, null, cb, succ);

	}

	@Override
	public Validity checkCall(IPredicate pre, CodeBlock cb, IPredicate succ) {
		return m_CallCheckHelper.check(pre, null, cb, succ);
	}

	@Override
	public Validity checkReturn(IPredicate preLin, IPredicate preHier, CodeBlock cb, IPredicate succ) {
		return m_ReturnCheckHelper.check(preLin, preHier, cb, succ);
	}

	@Override
	public EdgeCheckerBenchmarkGenerator getEdgeCheckerBenchmark() {
		return m_SdHoareTripleChecker.getEdgeCheckerBenchmark();
	}
	
	
	
	
	/**
	 * Abstract class for data-flow based Hoare triple checks.
	 * Subclasses are checks for internal, call, and return. 
	 * Because we can only override methods with the same signature (in Java) 
	 * we use the 3-parameter-signature for return (with hierarchical state) 
	 * and use null as hierarchical state for call and internal.
	 */
	public abstract class CheckHelper {

		public Validity check(IPredicate preLin, IPredicate preHier, CodeBlock cb, IPredicate succ) {
			switch (cb.getTransitionFormula().isInfeasible()) {
			case INFEASIBLE:
				return Validity.VALID;
			case NOT_DETERMINED:
			case UNPROVEABLE:
				break;
			default:
				throw new AssertionError("unknown case");
			}
			
			boolean unknownCoverage = false;
			// check if preLin is equivalent to true
			switch (m_PredicateCoverageChecker.isCovered(preLin, m_FalsePredicate)) {
			case INVALID:
				break;
			case NOT_CHECKED:
				throw new AssertionError("unchecked predicate");
			case UNKNOWN:
				unknownCoverage = true;
			case VALID:
				return Validity.VALID;
			default:
				throw new AssertionError("unknown case");
			}
			
			// check if preHier is equivalent to true
			if (preHier != null) {
				switch (m_PredicateCoverageChecker.isCovered(preHier, m_FalsePredicate)) {
				case INVALID:
					break;
				case NOT_CHECKED:
					throw new AssertionError("unchecked predicate");
				case UNKNOWN:
					unknownCoverage = true;
				case VALID:
					return Validity.VALID;
				default:
					throw new AssertionError("unknown case");
				}
			}
			
			// check if succ is equivalent to true
			switch (m_PredicateCoverageChecker.isCovered(m_TruePredicate, succ)) {
			case INVALID:
				break;
			case NOT_CHECKED:
				throw new AssertionError("unchecked predicate");
			case UNKNOWN:
				unknownCoverage = true;
			case VALID:
				return Validity.VALID;
			default:
				throw new AssertionError("unknown case");
			}
			if (unknownCoverage) {
				return Validity.UNKNOWN;
			}
			boolean isInductiveSelfloop = this.isInductiveSefloop(preLin, preHier, cb, succ);
			if (isInductiveSelfloop) {
				return Validity.VALID;
			}
			if (SmtUtils.isFalse(succ.getFormula())) {
				Validity toFalse = this.sdecToFalse(preLin, preHier, cb);
				if (toFalse == Validity.INVALID) {
					return Validity.INVALID;
				}
			}
			final Validity general;
			if (m_LazyChecks) {
				general = sdLazyEc(preLin, preHier, cb, succ);
			} else {			
				general = sdec(preLin, preHier, cb, succ);
			}
			if (general == Validity.INVALID) {
				return Validity.INVALID;
			}
			return Validity.UNKNOWN;
		}

		public abstract Validity sdecToFalse(IPredicate preLin, IPredicate preHier, CodeBlock cb);

		public abstract boolean isInductiveSefloop(IPredicate preLin, IPredicate preHier, CodeBlock cb,
				IPredicate succ);

		public abstract Validity sdec(IPredicate preLin, IPredicate preHier, CodeBlock cb, IPredicate succ);

		public abstract Validity sdLazyEc(IPredicate preLin, IPredicate preHier, CodeBlock cb, IPredicate succ);

	}

	protected class InternalCheckHelper extends CheckHelper {

		@Override
		public Validity sdecToFalse(IPredicate preLin, IPredicate preHier, CodeBlock cb) {
			assert preHier == null;
			return m_SdHoareTripleChecker.sdecInternalToFalse(preLin, cb);
		}

		@Override
		public boolean isInductiveSefloop(IPredicate preLin, IPredicate preHier, CodeBlock cb, IPredicate succ) {
			assert preHier == null;
			if ((preLin == succ) && (m_SdHoareTripleChecker.sdecInternalSelfloop(preLin, cb) == Validity.VALID)) {
				return true;
			} else {
				return false;
			}
		}

		@Override
		public Validity sdec(IPredicate preLin, IPredicate preHier, CodeBlock cb, IPredicate succ) {
			assert preHier == null;
			return m_SdHoareTripleChecker.sdecInteral(preLin, cb, succ);
		}

		@Override
		public Validity sdLazyEc(IPredicate preLin, IPredicate preHier, CodeBlock cb, IPredicate succ) {
			assert preHier == null;
			return m_SdHoareTripleChecker.sdLazyEcInteral(preLin, cb, succ);
		}
	}

	protected class CallCheckHelper extends CheckHelper {

		@Override
		public Validity sdecToFalse(IPredicate preLin, IPredicate preHier, CodeBlock cb) {
			assert preHier == null;
			return m_SdHoareTripleChecker.sdecCallToFalse(preLin, cb);
		}

		@Override
		public boolean isInductiveSefloop(IPredicate preLin, IPredicate preHier, CodeBlock cb, IPredicate succ) {
			assert preHier == null;
			if ((preLin == succ) && (m_SdHoareTripleChecker.sdecCallSelfloop(preLin, cb) == Validity.VALID)) {
				return true;
			} else {
				return false;
			}
		}

		@Override
		public Validity sdec(IPredicate preLin, IPredicate preHier, CodeBlock cb, IPredicate succ) {
			assert preHier == null;
			return m_SdHoareTripleChecker.sdecCall(preLin, cb, succ);
		}

		@Override
		public Validity sdLazyEc(IPredicate preLin, IPredicate preHier, CodeBlock cb, IPredicate succ) {
			assert preHier == null;
			return m_SdHoareTripleChecker.sdLazyEcCall(preLin, (Call) cb, succ);
		}

	}

	public class ReturnCheckHelper extends CheckHelper {

		@Override
		public Validity sdecToFalse(IPredicate preLin, IPredicate preHier, CodeBlock cb) {
			// sat if (not only if!) preLin and preHier are independent,
			// hence we can use the "normal" sdec method
			return m_SdHoareTripleChecker.sdecReturn(preLin, preHier, cb, m_FalsePredicate);
		}

		@Override
		public boolean isInductiveSefloop(IPredicate preLin, IPredicate preHier, CodeBlock cb, IPredicate succ) {
			if ((preLin == succ) && (m_SdHoareTripleChecker.sdecReturnSelfloopPre(preLin, (Return) cb) == Validity.VALID)) {
				return true;
			} else if ((preHier == succ)
					&& (m_SdHoareTripleChecker.sdecReturnSelfloopHier(preHier, (Return) cb) == Validity.VALID)) {
				return true;
			} else {
				return false;
			}
		}

		@Override
		public Validity sdec(IPredicate preLin, IPredicate preHier, CodeBlock cb, IPredicate succ) {
			return m_SdHoareTripleChecker.sdecReturn(preLin, preHier, cb, succ);
		}

		@Override
		public Validity sdLazyEc(IPredicate preLin, IPredicate preHier, CodeBlock cb, IPredicate succ) {
			return m_SdHoareTripleChecker.sdLazyEcReturn(preLin, preHier, (Return) cb, succ);
		}

	}

}
