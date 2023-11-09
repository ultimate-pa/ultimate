/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.predicates;

import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IncrementalHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;

/**
 * Check if each edge of automaton is inductive (resp. if inductivity can be refuted if <i>antiInductivity</i> is set).
 *
 * @param <L>
 *            The type of letters (i.e., actions) in the automaton
 */
public class InductivityCheck<L extends IAction> {

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;

	private final IHoareTripleChecker mHoareTripleChecker;
	private final boolean mAntiInductivity;
	private final boolean mAssertInductivity;

	private int mInductiveEdges;
	private int mNonInductiveEdges;
	private int mUnknownEdges;
	private final boolean mResult;

	/**
	 * @param services
	 * @param nwa
	 * @param antiInductivity
	 *            if false, we check if each edge is inductive, if true we check if inductivity of each edge can be
	 *            refuted.
	 * @param assertInductivity
	 *            if true, assert statements require inductivity (resp. anti-inductivity)
	 * @param hoareTripleChecker
	 */
	public InductivityCheck(final IUltimateServiceProvider services, final INestedWordAutomaton<L, IPredicate> nwa,
			final boolean antiInductivity, final boolean assertInductivity,
			final IHoareTripleChecker hoareTripleChecker) {
		super();
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		mHoareTripleChecker = hoareTripleChecker;
		mAntiInductivity = antiInductivity;
		mAssertInductivity = assertInductivity;
		mResult = checkInductivity(nwa);
	}

	public boolean getResult() {
		return mResult;
	}

	private boolean checkInductivity(final INestedWordAutomaton<L, IPredicate> nwa) {
		if (mAntiInductivity) {
			mLogger.info("Starting anti-inductivity check of a Floyd-Hoare automaton with " + nwa.sizeInformation());
		} else {
			mLogger.info("Starting inductivity check of a Floyd-Hoare automaton with " + nwa.sizeInformation());
		}

		boolean result = true;

		for (final IPredicate state : nwa.getStates()) {
			for (final OutgoingInternalTransition<L, IPredicate> outTrans : nwa.internalSuccessors(state)) {
				final Validity inductivity = mHoareTripleChecker.checkInternal(state,
						(IInternalAction) outTrans.getLetter(), outTrans.getSucc());
				final boolean newResult = evaluateResult(inductivity, state, outTrans);
				result = result && newResult;
			}
			for (final OutgoingCallTransition<L, IPredicate> outTrans : nwa.callSuccessors(state)) {
				final Validity inductivity =
						mHoareTripleChecker.checkCall(state, (ICallAction) outTrans.getLetter(), outTrans.getSucc());
				final boolean newResult = evaluateResult(inductivity, state, outTrans);
				result = result && newResult;
			}
			for (final OutgoingReturnTransition<L, IPredicate> outTrans : nwa.returnSuccessors(state)) {
				final Validity inductivity = mHoareTripleChecker.checkReturn(state, outTrans.getHierPred(),
						(IReturnAction) outTrans.getLetter(), outTrans.getSucc());
				final boolean newResult = evaluateResult(inductivity, state, outTrans);
				result = result && newResult;
			}
		}
		if (mHoareTripleChecker instanceof IncrementalHoareTripleChecker) {
			((IncrementalHoareTripleChecker) mHoareTripleChecker).clearAssertionStack();
		}
		mLogger.info("Floyd-Hoare automaton has " + (mInductiveEdges + mNonInductiveEdges + mUnknownEdges) + " edges. "
				+ mInductiveEdges + " inductive. " + mNonInductiveEdges + " not inductive. " + mUnknownEdges
				+ " times theorem prover too weak to decide inductivity. ");
		return result;
	}

	private boolean evaluateResult(final Validity inductivity, final IPredicate state, final Object trans) {
		boolean result = true;
		switch (inductivity) {
		case VALID: {
			mInductiveEdges++;
			if (mAntiInductivity) {
				mLogger.warn("Transition " + state + " " + trans + " not anti inductive");
				result = false;
				assert !mAssertInductivity || result : "anti inductivity failed";
			}
			break;
		}
		case INVALID: {
			mNonInductiveEdges++;
			if (!mAntiInductivity) {
				mLogger.warn("Transition " + state + " " + trans + " not inductive");
				result = false;
				assert !mAssertInductivity || result : "inductivity failed";
			}
			break;
		}
		case UNKNOWN: {
			mUnknownEdges++;
			break;
		}
		default:
			throw new IllegalArgumentException();
		}
		return result;
	}
}
