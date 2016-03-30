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

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.ICallAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IInternalAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IReturnAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.HoareTripleCheckerStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
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
		m_SmtBasedHoareTripleChecker = new ProtectiveHoareTripleChecker(smtBasedHoareTripleChecker, predicateUnifier);
		m_SdHoareTripleChecker = new SdHoareTripleChecker(modGlobVarManager, 
				predicateUnifier, m_SmtBasedHoareTripleChecker.getEdgeCheckerBenchmark());
		m_hoareTripleCheckerForReview = new MonolithicHoareTripleChecker(smtManager);
	}

	@Override
	public Validity checkInternal(IPredicate pre, IInternalAction act, IPredicate succ) {
		final Validity sdResult = m_SdHoareTripleChecker.checkInternal(pre, act, succ);
		if (sdResult != Validity.UNKNOWN) {
			if (m_ReviewSdResultsIfAssertionsEnabled) {
				assert reviewInductiveInternal(pre, act, succ, sdResult);
			}
			return sdResult;
		} else {
			Validity result = m_SmtBasedHoareTripleChecker.checkInternal(pre, act, succ);
			if (m_ReviewSmtResultsIfAssertionsEnabled) {
				assert reviewInductiveInternal(pre, act, succ, result);
			}
			return result;
		}
	}

	@Override
	public Validity checkCall(IPredicate pre, ICallAction act, IPredicate succ) {
		final Validity sdResult = m_SdHoareTripleChecker.checkCall(pre, act, succ);
		if (sdResult != Validity.UNKNOWN) {
			if (m_ReviewSdResultsIfAssertionsEnabled) {
				assert reviewInductiveCall(pre, act, succ, sdResult);
			}
			return sdResult;
		} else {
			Validity result = m_SmtBasedHoareTripleChecker.checkCall(pre, act, succ);
			if (m_ReviewSmtResultsIfAssertionsEnabled) {
				assert reviewInductiveCall(pre, act, succ, result);
			}
			return result;
		}
	}

	@Override
	public Validity checkReturn(IPredicate preLin, IPredicate preHier,
			IReturnAction act, IPredicate succ) {
		final Validity sdResult = m_SdHoareTripleChecker.checkReturn(preLin, preHier, act, succ);
		if (sdResult != Validity.UNKNOWN) {
			if (m_ReviewSdResultsIfAssertionsEnabled) {
				assert reviewInductiveReturn(preLin, preHier, act, succ, sdResult);
			}
			return sdResult;
		} else {
			Validity result = m_SmtBasedHoareTripleChecker.checkReturn(preLin, preHier, act, succ);
			if (m_ReviewSmtResultsIfAssertionsEnabled) {
				assert reviewInductiveReturn(preLin, preHier, act, succ, result);
			}
			return result;
		}
	}

	@Override
	public HoareTripleCheckerStatisticsGenerator getEdgeCheckerBenchmark() {
		return m_SmtBasedHoareTripleChecker.getEdgeCheckerBenchmark();
	}
	
	
	private boolean reviewInductiveInternal(IPredicate state, IInternalAction act, IPredicate succ, Validity result) {
		releaseLock();
		Validity reviewResult = m_hoareTripleCheckerForReview.checkInternal(state, act, succ);
		if (resultCompatibleHelper(result, reviewResult)) {
			return true;
		} else {
			throw new AssertionError("Result: " + result 
					+ "  Review result: " + reviewResult);
		}
	}
	
	private boolean reviewInductiveCall(IPredicate state, ICallAction act, IPredicate succ, Validity result) {
		releaseLock();
		Validity reviewResult = m_hoareTripleCheckerForReview.checkCall(state, act, succ);
		if (resultCompatibleHelper(result, reviewResult)) {
			return true;
		} else {
			throw new AssertionError("Result: " + result 
					+ "  Review result: " + reviewResult);
		}

	}
	
	private boolean reviewInductiveReturn(IPredicate state, IPredicate hier, IReturnAction act, IPredicate succ, Validity result) {
		releaseLock();
		Validity reviewResult = m_hoareTripleCheckerForReview.checkReturn(state, hier, act, succ);
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
		case NOT_CHECKED:
			return true;
		default:
			throw new UnsupportedOperationException();
		}
	}
	
	@Override
	public void releaseLock() {
		m_SmtBasedHoareTripleChecker.releaseLock();
	}

}
