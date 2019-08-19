/*
 * Copyright (C) 2011-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IStateDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.DeterminizedState;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IDeterminizeStateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.MonolithicHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;

/**
 * Tradeoff between PowersetDeterminizer and BestApproximationDeterminizer. Idea: Make a selfloop if inductive. If not
 * inductive use PowersetDeterminizer
 * 
 * @author heizmann@informatik.uni-freiburg.de
 * 
 *         TODO: For Call and Return this does not make much sense. Use there generally the PowersetDeterminizer or the
 *         BestApproximationDeterminizer.
 */
public class SelfloopDeterminizer implements IStateDeterminizer<IIcfgTransition<?>, IPredicate> {

	IHoareTripleChecker mHoareTriplechecker;
	PowersetDeterminizer<IIcfgTransition<?>, IPredicate> mPowersetDeterminizer;

	INestedWordAutomaton<IIcfgTransition<?>, IPredicate> mInterpolantAutomaton;
	private final IDeterminizeStateFactory<IPredicate> mStateFactory;
	IPredicate mInterpolantAutomatonFinalState;

	DeterminizedState<IIcfgTransition<?>, IPredicate> mResultFinalState;

	public int mInternalSelfloop = 0;
	public int mInternalNonSelfloop = 0;

	public int mCallSelfloop = 0;
	public int mCallNonSelfloop = 0;

	public int mReturnSelfloop = 0;
	public int mReturnNonSelfloop = 0;

	public SelfloopDeterminizer(final CfgSmtToolkit mCsToolkit, final TAPreferences taPreferences,
			final INestedWordAutomaton<IIcfgTransition<?>, IPredicate> interpolantAutom,
			final IDeterminizeStateFactory<IPredicate> stateFactory) {
		super();
		mHoareTriplechecker = new MonolithicHoareTripleChecker(mCsToolkit);
		mInterpolantAutomaton = interpolantAutom;
		mStateFactory = stateFactory;
		mPowersetDeterminizer = new PowersetDeterminizer<>(mInterpolantAutomaton, true, mStateFactory);
		for (final IPredicate state : mInterpolantAutomaton.getStates()) {
			if (mInterpolantAutomatonFinalState == null) {
				if (mInterpolantAutomaton.isFinal(state)) {
					mInterpolantAutomatonFinalState = state;
				}
			} else {
				throw new IllegalArgumentException("Interpolant Automaton" + " must have one final state");
			}
		}
		mResultFinalState = new DeterminizedState<>(mInterpolantAutomaton);
		mResultFinalState.addPair(mInterpolantAutomaton.getEmptyStackState(), mInterpolantAutomatonFinalState,
				mInterpolantAutomaton);
	}

	@Override
	public DeterminizedState<IIcfgTransition<?>, IPredicate> initialState() {
		return mPowersetDeterminizer.initialState();
	}

	@Override
	public DeterminizedState<IIcfgTransition<?>, IPredicate> internalSuccessor(
			final DeterminizedState<IIcfgTransition<?>, IPredicate> detState, final IIcfgTransition<?> symbol) {
		if (detState == mResultFinalState) {
			mInternalSelfloop++;
			return mResultFinalState;
		}
		final DeterminizedState<IIcfgTransition<?>, IPredicate> powersetSucc =
				mPowersetDeterminizer.internalSuccessor(detState, symbol);
		if (containsFinal(powersetSucc)) {
			mInternalNonSelfloop++;
			return mResultFinalState;
		}
		if (powersetSucc.isSubsetOf(detState)) {
			final IPredicate detStateContent = getState(detState);
			final Validity isInductive =
					mHoareTriplechecker.checkInternal(detStateContent, (IInternalAction) symbol, detStateContent);
			if (isInductive == Validity.VALID) {
				mInternalSelfloop++;
				return detState;
			}
		}
		mInternalNonSelfloop++;
		return powersetSucc;
	}

	@Override
	public DeterminizedState<IIcfgTransition<?>, IPredicate> callSuccessor(
			final DeterminizedState<IIcfgTransition<?>, IPredicate> detState, final IIcfgTransition<?> symbol) {
		if (detState == mResultFinalState) {
			mCallSelfloop++;
			return mResultFinalState;
		}
		final DeterminizedState<IIcfgTransition<?>, IPredicate> powersetSucc =
				mPowersetDeterminizer.callSuccessor(detState, symbol);
		if (containsFinal(powersetSucc)) {
			mCallNonSelfloop++;
			return mResultFinalState;
		}
		if (powersetSucc.isSubsetOf(detState)) {
			final IPredicate detStateContent = getState(detState);
			final Validity isInductive =
					mHoareTriplechecker.checkCall(detStateContent, (IIcfgCallTransition<?>) symbol, detStateContent);
			if (isInductive == Validity.VALID) {
				mCallSelfloop++;
				return detState;
			}
		}
		mCallNonSelfloop++;
		return powersetSucc;
	}

	@Override
	public DeterminizedState<IIcfgTransition<?>, IPredicate> returnSuccessor(
			final DeterminizedState<IIcfgTransition<?>, IPredicate> detState,
			final DeterminizedState<IIcfgTransition<?>, IPredicate> derHier, final IIcfgTransition<?> symbol) {
		if (detState == mResultFinalState) {
			mReturnSelfloop++;
			return mResultFinalState;
		}
		if (derHier == mResultFinalState) {
			throw new AssertionError("I guess this never happens");
		}
		final DeterminizedState<IIcfgTransition<?>, IPredicate> powersetSucc =
				mPowersetDeterminizer.returnSuccessor(detState, derHier, symbol);
		if (containsFinal(powersetSucc)) {
			mReturnNonSelfloop++;
			return mResultFinalState;
		}
		if (powersetSucc.isSubsetOf(detState)) {
			final IPredicate detStateContent = getState(detState);
			final IPredicate detHierContent = getState(derHier);
			final Validity isInductive = mHoareTriplechecker.checkReturn(detStateContent, detHierContent,
					(IIcfgReturnTransition<?, ?>) symbol, detStateContent);
			if (isInductive == Validity.VALID) {
				mReturnSelfloop++;
				return detState;
			}
		}
		mReturnNonSelfloop++;
		return powersetSucc;
	}

	private boolean containsFinal(final DeterminizedState<IIcfgTransition<?>, IPredicate> detState) {
		for (final IPredicate down : detState.getDownStates()) {
			for (final IPredicate up : detState.getUpStates(down)) {
				if (up == mInterpolantAutomatonFinalState) {
					return true;
				}
			}
		}
		return false;
	}

	@Override
	public int getMaxDegreeOfNondeterminism() {
		// TODO Auto-generated method stub
		return 0;
	}

	@Override
	public boolean useDoubleDeckers() {
		return true;
	}

	@Override
	public IPredicate getState(final DeterminizedState<IIcfgTransition<?>, IPredicate> determinizedState) {
		return determinizedState.getContent(mStateFactory);
	}

}
