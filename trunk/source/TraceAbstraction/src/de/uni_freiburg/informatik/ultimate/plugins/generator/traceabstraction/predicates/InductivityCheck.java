/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;

/**
 * Check if each edge of automaton is inductive (resp. if inductivity can be refuted if <i>antiInductivity</i> is set).
 *
 * @param antiInductivity
 *            if false, we check if each edge is inductive, if true we check if inductivity of each edge can be refuted.
 * @param assertInductivity
 *            if true, assert statements require inductivity (resp. anti-inductivity)
 */
public class InductivityCheck<LETTER extends IAction> {

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;

	private final IHoareTripleChecker mHoareTripleChecker;
	private final boolean mAntiInductivity;
	private final boolean mAssertInductivity;
	private final int[] mYield;
	private final boolean mResult;

	public InductivityCheck(final IUltimateServiceProvider services, final INestedWordAutomaton<LETTER, IPredicate> nwa,
			final boolean antiInductivity, final boolean assertInductivity,
			final IHoareTripleChecker hoareTripleChecker) {
		super();
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		mHoareTripleChecker = hoareTripleChecker;
		mYield = new int[3];
		mAntiInductivity = antiInductivity;
		mAssertInductivity = assertInductivity;
		mResult = checkInductivity(nwa);
	}

	public boolean getResult() {
		return mResult;
	}

	private boolean checkInductivity(final INestedWordAutomaton<LETTER, IPredicate> nwa) {
		if (mAntiInductivity) {
			mLogger.info("Starting anti-indutivity check of a Floyd-Hoare automaton with " + nwa.sizeInformation());
		} else {
			mLogger.info("Starting indutivity check of a Floyd-Hoare automaton with " + nwa.sizeInformation());
		}

		final boolean result = true;
		// yield[0] is the number of edges whose inductiveness could be
		// proven
		// yield[1] is the number of edges whose inductiveness could be
		// refuted
		// yield[2] is the number of edges whose inductiveness could be
		// neither proven nor refuted because theorem prover too weak
		// yield[3] is the number of edges whose inductiveness could be
		// neither proven nor refuted because there were no interpolants

		for (final IPredicate state : nwa.getStates()) {
			for (final OutgoingInternalTransition<LETTER, IPredicate> outTrans : nwa.internalSuccessors(state)) {
				final Validity inductivity = mHoareTripleChecker.checkInternal(state,
						(IInternalAction) outTrans.getLetter(), outTrans.getSucc());
				evaluateResult(inductivity, state, outTrans);
			}
			for (final OutgoingCallTransition<LETTER, IPredicate> outTrans : nwa.callSuccessors(state)) {
				final Validity inductivity = mHoareTripleChecker.checkCall(state, (ICallAction) outTrans.getLetter(),
						outTrans.getSucc());
				evaluateResult(inductivity, state, outTrans);
			}
			for (final OutgoingReturnTransition<LETTER, IPredicate> outTrans : nwa.returnSuccessors(state)) {
				final Validity inductivity = mHoareTripleChecker.checkReturn(state, outTrans.getHierPred(),
						(IReturnAction) outTrans.getLetter(), outTrans.getSucc());
				evaluateResult(inductivity, state, outTrans);
			}
		}
		if (mHoareTripleChecker instanceof IncrementalHoareTripleChecker) {
			((IncrementalHoareTripleChecker) mHoareTripleChecker).clearAssertionStack();
		}
		mLogger.info("Floyd-Hoare automaton has " + (mYield[0] + mYield[1] + mYield[2]) + " edges. " + mYield[0]
				+ " inductive. " + mYield[1] + " not inductive. " + mYield[2] + " times theorem prover too"
				+ " weak to decide inductivity. ");
		return result;
	}

	private boolean evaluateResult(final Validity inductivity, final IPredicate state, final Object trans) {
		boolean result = true;
		switch (inductivity) {
		case VALID: {
			mYield[0]++;
			if (mAntiInductivity) {
				mLogger.warn("Transition " + state + " " + trans + " not anti inductive");
				result = false;
				assert !mAssertInductivity || result : "anti inductivity failed";
			}
			break;
		}
		case INVALID: {
			mYield[1]++;
			if (!mAntiInductivity) {
				mLogger.warn("Transition " + state + " " + trans + " not inductive");
				result = false;
				assert !mAssertInductivity || result : "inductivity failed";
			}
			break;
		}
		case UNKNOWN: {
			mYield[2]++;
			break;
		}
		default:
			throw new IllegalArgumentException();
		}
		return result;
	}
}
