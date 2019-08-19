/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.HoareTripleCheckerStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.SdHoareTripleCheckerHelper;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateCoverageChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;

/**
 * Hoare triple checker that uses only simple dataflow analysis to check triples. If this simple analysis is not able to
 * determine the result UNKNOWN is returned.
 *
 * @author Matthias Heizmann
 */
public class SdHoareTripleChecker implements IHoareTripleChecker {
	private final SdHoareTripleCheckerHelper mSdHoareTripleChecker;
	private final IPredicateCoverageChecker mPredicateCoverageChecker;
	private final IPredicate mTruePredicate;
	private final IPredicate mFalsePredicate;
	private static final boolean mLazyChecks = false;
	private final InternalCheckHelper mInternalCheckHelper = new InternalCheckHelper();
	private final CallCheckHelper mCallCheckHelper = new CallCheckHelper();
	private final ReturnCheckHelper mReturnCheckHelper = new ReturnCheckHelper();

	public SdHoareTripleChecker(final CfgSmtToolkit csToolkit, final IPredicateUnifier predicateUnifier,
			final HoareTripleCheckerStatisticsGenerator edgeCheckerBenchmarkGenerator) {
		mPredicateCoverageChecker = predicateUnifier.getCoverageRelation();
		mTruePredicate = predicateUnifier.getTruePredicate();
		mFalsePredicate = predicateUnifier.getFalsePredicate();
		mSdHoareTripleChecker =
				new SdHoareTripleCheckerHelper(csToolkit, mPredicateCoverageChecker, edgeCheckerBenchmarkGenerator);
	}

	@Override
	public Validity checkInternal(final IPredicate pre, final IInternalAction act, final IPredicate succ) {
		return mInternalCheckHelper.check(pre, null, act, succ);
	}

	@Override
	public Validity checkCall(final IPredicate pre, final ICallAction act, final IPredicate succ) {
		return mCallCheckHelper.check(pre, null, act, succ);
	}

	@Override
	public Validity checkReturn(final IPredicate preLin, final IPredicate preHier, final IReturnAction act,
			final IPredicate succ) {
		return mReturnCheckHelper.check(preLin, preHier, act, succ);
	}

	@Override
	public HoareTripleCheckerStatisticsGenerator getEdgeCheckerBenchmark() {
		return mSdHoareTripleChecker.getEdgeCheckerBenchmark();
	}

	protected SdHoareTripleCheckerHelper getSdHoareTripleChecker() {
		return mSdHoareTripleChecker;
	}

	protected IPredicateCoverageChecker getPredicateCoverageChecker() {
		return mPredicateCoverageChecker;
	}

	protected IPredicate getFalsePredicate() {
		return mFalsePredicate;
	}

	protected IPredicate getTruePredicate() {
		return mTruePredicate;
	}

	/**
	 * Abstract class for data-flow based Hoare triple checks. Subclasses are checks for internal, call, and return.
	 * Because we can only override methods with the same signature (in Java) we use the 3-parameter-signature for
	 * return (with hierarchical state) and use null as hierarchical state for call and internal.
	 */
	public abstract class CheckHelper {
		public Validity check(final IPredicate preLin, final IPredicate preHier, final IAction act,
				final IPredicate succ) {
			if (act instanceof IInternalAction) {
				if (((IInternalAction) act).getTransformula().isInfeasible() == Infeasibility.INFEASIBLE) {
					return Validity.VALID;
				}
			}

			boolean unknownCoverage = false;
			// check if preLin is equivalent to false
			switch (getPredicateCoverageChecker().isCovered(preLin, getFalsePredicate())) {
			case INVALID:
				break;
			case NOT_CHECKED:
				throw new AssertionError("unchecked predicate");
			case UNKNOWN:
				unknownCoverage = true;
				break;
			case VALID:
				return Validity.VALID;
			default:
				throw new AssertionError("unknown case");
			}

			// check if preHier is equivalent to false
			if (preHier != null) {
				switch (getPredicateCoverageChecker().isCovered(preHier, getFalsePredicate())) {
				case INVALID:
					break;
				case NOT_CHECKED:
					throw new AssertionError("unchecked predicate");
				case UNKNOWN:
					unknownCoverage = true;
					break;
				case VALID:
					return Validity.VALID;
				default:
					throw new AssertionError("unknown case");
				}
			}

			// check if succ is equivalent to true
			switch (getPredicateCoverageChecker().isCovered(getTruePredicate(), succ)) {
			case INVALID:
				break;
			case NOT_CHECKED:
				throw new AssertionError("unchecked predicate");
			case UNKNOWN:
				unknownCoverage = true;
				break;
			case VALID:
				return Validity.VALID;
			default:
				throw new AssertionError("unknown case");
			}
			if (unknownCoverage) {
				return Validity.UNKNOWN;
			}
			final boolean isInductiveSelfloop = isInductiveSefloop(preLin, preHier, act, succ);
			if (isInductiveSelfloop) {
				return Validity.VALID;
			}
			if (SmtUtils.isFalseLiteral(succ.getFormula())) {
				final Validity toFalse = sdecToFalse(preLin, preHier, act);
				if (toFalse == null) {
					// we are unable to determine validity with SD checks
					assert sdec(preLin, preHier, act, succ) == null : "inconsistent check results";
					return Validity.UNKNOWN;
				}
				switch (toFalse) {
				case INVALID:
					return Validity.INVALID;
				case NOT_CHECKED:
					throw new AssertionError("unchecked predicate");
				case UNKNOWN:
					throw new AssertionError("this case should have been filtered out before");
				case VALID:
					throw new AssertionError("this case should have been filtered out before");
				default:
					throw new AssertionError("unknown case");
				}
			}
			final Validity general;
			if (mLazyChecks) {
				general = sdLazyEc(preLin, preHier, act, succ);
			} else {
				general = sdec(preLin, preHier, act, succ);
			}
			if (general != null) {
				switch (general) {
				case INVALID:
					return Validity.INVALID;
				case NOT_CHECKED:
					throw new AssertionError("unchecked predicate");
				case UNKNOWN:
					throw new AssertionError("this case should have been filtered out before");
				case VALID:
					return Validity.VALID;
				default:
					throw new AssertionError("unknown case");
				}
			}
			return Validity.UNKNOWN;
		}

		public abstract Validity sdecToFalse(IPredicate preLin, IPredicate preHier, IAction act);

		public abstract boolean isInductiveSefloop(IPredicate preLin, IPredicate preHier, IAction act, IPredicate succ);

		public abstract Validity sdec(IPredicate preLin, IPredicate preHier, IAction act, IPredicate succ);

		public abstract Validity sdLazyEc(IPredicate preLin, IPredicate preHier, IAction act, IPredicate succ);

	}

	protected class InternalCheckHelper extends CheckHelper {
		@Override
		public Validity sdecToFalse(final IPredicate preLin, final IPredicate preHier, final IAction act) {
			assert preHier == null;
			return getSdHoareTripleChecker().sdecInternalToFalse(preLin, (IInternalAction) act);
		}

		@Override
		public boolean isInductiveSefloop(final IPredicate preLin, final IPredicate preHier, final IAction act,
				final IPredicate succ) {
			assert preHier == null;
			return preLin == succ
					&& getSdHoareTripleChecker().sdecInternalSelfloop(preLin, (IInternalAction) act) == Validity.VALID;
		}

		@Override
		public Validity sdec(final IPredicate preLin, final IPredicate preHier, final IAction act,
				final IPredicate succ) {
			assert preHier == null;
			return getSdHoareTripleChecker().sdecInteral(preLin, (IInternalAction) act, succ);
		}

		@Override
		public Validity sdLazyEc(final IPredicate preLin, final IPredicate preHier, final IAction act,
				final IPredicate succ) {
			assert preHier == null;
			return getSdHoareTripleChecker().sdLazyEcInteral(preLin, (IInternalAction) act, succ);
		}
	}

	protected class CallCheckHelper extends CheckHelper {
		@Override
		public Validity sdecToFalse(final IPredicate preLin, final IPredicate preHier, final IAction act) {
			assert preHier == null;
			return getSdHoareTripleChecker().sdecCallToFalse(preLin, (ICallAction) act);
		}

		@Override
		public boolean isInductiveSefloop(final IPredicate preLin, final IPredicate preHier, final IAction act,
				final IPredicate succ) {
			assert preHier == null;
			return preLin == succ
					&& getSdHoareTripleChecker().sdecCallSelfloop(preLin, (ICallAction) act) == Validity.VALID;
		}

		@Override
		public Validity sdec(final IPredicate preLin, final IPredicate preHier, final IAction act,
				final IPredicate succ) {
			assert preHier == null;
			return getSdHoareTripleChecker().sdecCall(preLin, (ICallAction) act, succ);
		}

		@Override
		public Validity sdLazyEc(final IPredicate preLin, final IPredicate preHier, final IAction act,
				final IPredicate succ) {
			assert preHier == null;
			return getSdHoareTripleChecker().sdLazyEcCall(preLin, (ICallAction) act, succ);
		}

	}

	public class ReturnCheckHelper extends CheckHelper {
		@Override
		public Validity sdecToFalse(final IPredicate preLin, final IPredicate preHier, final IAction act) {
			return getSdHoareTripleChecker().sdecReturnToFalse(preLin, preHier, (IReturnAction) act);
		}

		@Override
		public boolean isInductiveSefloop(final IPredicate preLin, final IPredicate preHier, final IAction act,
				final IPredicate succ) {
			if (preLin == succ
					&& getSdHoareTripleChecker().sdecReturnSelfloopPre(preLin, (IReturnAction) act) == Validity.VALID) {
				return true;
			}
			return preHier == succ
					&& getSdHoareTripleChecker().sdecReturnSelfloopHier(preHier, (IReturnAction) act) == Validity.VALID;
		}

		@Override
		public Validity sdec(final IPredicate preLin, final IPredicate preHier, final IAction act,
				final IPredicate succ) {
			return getSdHoareTripleChecker().sdecReturn(preLin, preHier, (IReturnAction) act, succ);
		}

		@Override
		public Validity sdLazyEc(final IPredicate preLin, final IPredicate preHier, final IAction act,
				final IPredicate succ) {
			return getSdHoareTripleChecker().sdLazyEcReturn(preLin, preHier, (IReturnAction) act, succ);
		}

	}

	@Override
	public void releaseLock() {
		// do nothing, since objects of this class do not lock the solver
	}
}
