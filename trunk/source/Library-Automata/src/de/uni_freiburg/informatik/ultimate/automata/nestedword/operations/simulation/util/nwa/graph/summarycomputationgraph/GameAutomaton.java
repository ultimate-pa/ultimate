/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 * 
 * This file is part of the ULTIMATE Automata Library.
 * 
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.summarycomputationgraph;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomatonOnDemandStateAndLetter;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.ETransitionType;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.DuplicatorNwaVertex;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.DuplicatorWinningSink;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.IWinningSink;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.SpoilerNwaVertex;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.SpoilerWinningSink;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.game.GameSpoilerNwaVertex;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.game.IGameLetter;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.game.IGameState;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IOutgoingTransitionlet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap3;

/**
 * Construct game automaton given the input automaton (not a game graph) and
 * the initial partition.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 * @param <LETTER>
 * @param <STATE>
 */
public abstract class GameAutomaton<LETTER, STATE> extends NestedWordAutomatonOnDemandStateAndLetter<IGameLetter<LETTER, STATE>, IGameState> {
	
	private final boolean mOmitSymmetricPairs = true;
	
	private final Collection<Set<STATE>> mPossibleEquivalentClasses;
	private final IDoubleDeckerAutomaton<LETTER, STATE> mOperand;
	
	private final ISimulationInfoProvider<LETTER, STATE> mSimulationInfoProvider;
	
	private final GameStateFactory mGameStateFactory;
	private final GameLetterFactory mGameLetterFactory;

	private final SpoilerWinningSink<LETTER, STATE> mSpoilerWinningSink;
	private final DuplicatorWinningSink<LETTER, STATE> mDuplicatorWinningSink;
	
	
	
	public GameAutomaton(final AutomataLibraryServices services, final IStateFactory<IGameState> stateFactory,
			final Collection<Set<STATE>> possibleEquivalentClasses, final IDoubleDeckerAutomaton<LETTER, STATE> operand,
			final ISimulationInfoProvider<LETTER, STATE> simulationInfoProvider) {
		super(services, stateFactory);
		mPossibleEquivalentClasses = possibleEquivalentClasses;
		mOperand = operand;
		mSimulationInfoProvider = simulationInfoProvider;
		mGameLetterFactory = new GameLetterFactory();
		mGameStateFactory = new GameStateFactory();
		mSpoilerWinningSink = new SpoilerWinningSink<>(null);
		mDuplicatorWinningSink = new DuplicatorWinningSink<>(null);
	}
	@Override
	protected void constructInitialStates() {
		for (final Set<STATE> eqClass : mPossibleEquivalentClasses) {
			for (final STATE q0 : eqClass) {
				for (final STATE q1 : eqClass) {
					if (mOmitSymmetricPairs && q0.equals(q1)) {
						// omit pair
					} else {
						constructInitialVertex(q0, q1);
					}
				}
			}
		}
	}

	private IGameState constructInitialVertex(final STATE spoilerState, final STATE duplicatorState) {
		final boolean isSpoilerAccepting = mOperand.isFinal(spoilerState);
		final boolean isDuplicatorAccepting = mOperand.isFinal(duplicatorState);
		final boolean delayedbit = mSimulationInfoProvider.computeBitForInitialVertex(isSpoilerAccepting, isDuplicatorAccepting);
		final int priority = mSimulationInfoProvider.computePriority(delayedbit, isSpoilerAccepting, isDuplicatorAccepting);
		final IGameState result = mGameStateFactory.getOrConstructGameState(spoilerState, duplicatorState, delayedbit , priority, false);
		return result;
	}
	
	
	@Override
	protected void constructInternalSuccessors(final IGameState state) {
		if (isSpoilerSink(state) || isDuplicatorSink(state)) {
			// do nothing
		} else {
			final SpoilerNwaVertex<LETTER, STATE> vertex = unwrapSpoilerNwaVertex(state);
			final HashRelation<IGameLetter<LETTER, STATE>, IGameState> succTrans = 
					constructSuccessors(vertex, new InternalLetterAndSuccessorProvider(), 
							ETransitionType.INTERNAL, false);
			addInternalTransitionsToAutomaton(state, succTrans);
		}
	}
	
	@Override
	protected void constructCallSuccessors(final IGameState state) {
		if (isSpoilerSink(state) || isDuplicatorSink(state)) {
			// do nothing
		} else {
			final SpoilerNwaVertex<LETTER, STATE> vertex = unwrapSpoilerNwaVertex(state);
			final HashRelation<IGameLetter<LETTER, STATE>, IGameState> succTrans = 
					constructSuccessors(vertex, new CallLetterAndSuccessorProvider(), 
							ETransitionType.CALL, false);
			addCallTransitionsToAutomaton(state, succTrans);
		}
		
	}
	@Override
	protected void constructReturnSuccessors(final IGameState lin, final IGameState hier) {
		if (isSpoilerSink(lin) || isDuplicatorSink(lin)) {
			// do nothing
		} else {
			final SpoilerNwaVertex<LETTER, STATE> vertex = unwrapSpoilerNwaVertex(lin);
			final HashRelation<IGameLetter<LETTER, STATE>, IGameState> succTrans = 
					constructSuccessors(vertex, new ReturnLetterAndSuccessorProvider(unwrapSpoilerNwaVertex(hier)), 
							ETransitionType.RETURN, true);
			addReturnTransitionsToAutomaton(lin, hier, succTrans);
		}
	}
	
	private SpoilerNwaVertex<LETTER, STATE> unwrapSpoilerNwaVertex(final IGameState state) {
		final GameSpoilerNwaVertex<LETTER, STATE> wrapper = (GameSpoilerNwaVertex<LETTER, STATE>) state;
		final SpoilerNwaVertex<LETTER, STATE> vertex = wrapper.getSpoilerNwaVertex();
		return vertex;
	}
	
	private HashRelation<IGameLetter<LETTER, STATE>, IGameState> constructSuccessors(
			final SpoilerNwaVertex<LETTER, STATE> vertex,
			final LetterAndSuccessorProvider<LETTER, STATE, ? extends IOutgoingTransitionlet<LETTER, STATE>> lasp, 
			final ETransitionType transitionType, final boolean spoilerStateNeededInSucc) {
		final STATE spoilerState = vertex.getQ0();
		final STATE duplicatorState = vertex.getQ1();
		final HashRelation<IGameLetter<LETTER, STATE>, IGameState> succTrans = new HashRelation<>();
		for (final LETTER letter : lasp.getLettersForSpoiler(spoilerState)) {
			final Iterable<? extends IOutgoingTransitionlet<LETTER, STATE>> spoilerSuccIt = lasp.getOutgoingTransitionsForSpoiler(spoilerState, letter);
			final Set<STATE> spoilerSuccs = NestedWordAutomataUtils.constructSuccessorSet(spoilerSuccIt);
			final Iterable<? extends IOutgoingTransitionlet<LETTER, STATE>> duplicatorSuccIt = lasp.getOutgoingTransitionsForSpoiler(duplicatorState, letter);
			final Set<STATE> duplicatorSuccs = NestedWordAutomataUtils.constructSuccessorSet(duplicatorSuccIt);
			final HashRelation<IGameLetter<LETTER, STATE>, IGameState> succTransForLetter = 
					computerSuccessorTransitions(vertex, letter, transitionType, spoilerSuccs, duplicatorSuccs, spoilerStateNeededInSucc);
			succTrans.addAll(succTransForLetter);
		}
		return succTrans;
	}
	
	private void addInternalTransitionsToAutomaton(final IGameState state, final HashRelation<IGameLetter<LETTER, STATE>, IGameState> succTrans) {
		for (final IGameLetter<LETTER, STATE> gameLetter : succTrans.getDomain()) {
			mCache.addInternalTransitions(state, gameLetter, succTrans.getImage(gameLetter));
		}
	}
	
	private void addCallTransitionsToAutomaton(final IGameState state, final HashRelation<IGameLetter<LETTER, STATE>, IGameState> succTrans) {
		for (final IGameLetter<LETTER, STATE> gameLetter : succTrans.getDomain()) {
			mCache.addCallTransitions(state, gameLetter, succTrans.getImage(gameLetter));
		}
	}
	
	private void addReturnTransitionsToAutomaton(final IGameState lin, final IGameState hier, final HashRelation<IGameLetter<LETTER, STATE>, IGameState> succTrans) {
		for (final IGameLetter<LETTER, STATE> gameLetter : succTrans.getDomain()) {
			mCache.addReturnTransitions(lin, hier, gameLetter, succTrans.getImage(gameLetter));
		}
	}
	
	
	
	private HashRelation<IGameLetter<LETTER, STATE>, IGameState> computerSuccessorTransitions(
			final SpoilerNwaVertex<LETTER, STATE> vertex, final LETTER letter, final ETransitionType transitionType, final Set<STATE> spoilerSuccs,
			final Set<STATE> duplicatorSuccs, final boolean spoilerStateNeededInSucc) {
		final HashRelation<IGameLetter<LETTER, STATE>, IGameState> result = new HashRelation<>();
		for (final STATE spoilerSucc : spoilerSuccs) {
			final IGameLetter<LETTER, STATE> gameLetter = getOrConstuctSuccessorGameLetter(vertex, letter, transitionType, spoilerSucc);
			if (duplicatorSuccs.isEmpty()) {
				final IGameState wrapper = getOrConstructSuccessorSpoilerWinningSinkVertex(vertex, letter, spoilerSucc);
				result.addPair(gameLetter, wrapper);
			} else {
				final DuplicatorNwaVertex<LETTER, STATE> dnv = (DuplicatorNwaVertex<LETTER, STATE>) gameLetter;
				for (final STATE duplicatorSucc : duplicatorSuccs) {
					final IGameState wrapper = getOrConstructSuccessorVertex(dnv.isB(), letter, spoilerSucc, duplicatorSucc, spoilerStateNeededInSucc);
					result.addPair(gameLetter, wrapper);
				}
			}
		}
		return result;
	}
	private IGameState getOrConstructSuccessorSpoilerWinningSinkVertex(final SpoilerNwaVertex<LETTER, STATE> predVertex, final LETTER letter,
			final STATE spoilerSucc) {
		final boolean isDuplicatorAccepting = mOperand.isFinal(predVertex.getQ1());
		final boolean delayedbit = mSimulationInfoProvider.computeBitForDuplicatorVertex(predVertex.isB(), isDuplicatorAccepting);
		// only auxiliary step to sink, use "neutral" priority
		final int priority = 2;
		final IGameState result = mGameStateFactory.getOrConstructGameState(spoilerSucc, null, delayedbit , priority, false);
		return result;
	}
	private IGameState getOrConstructSuccessorVertex(final boolean predBit, final LETTER letter, final STATE spoilerSucc,
			final STATE duplicatorSucc, final boolean spoilerStateNeededInSucc) {
		final boolean isSpoilerAccepting = mOperand.isFinal(spoilerSucc);
		final boolean isDuplicatorAccepting = mOperand.isFinal(duplicatorSucc);
		final boolean isImmediatelyWinningForSpoiler = mSimulationInfoProvider.isImmediatelyWinningForSpoiler(isSpoilerAccepting, isDuplicatorAccepting);
		if (isImmediatelyWinningForSpoiler && !spoilerStateNeededInSucc) {
			//TODO: Optimization for unique sink
			return null;
		} else {
			final boolean delayedbit = mSimulationInfoProvider.computeBitForSpoilerVertex(predBit, isSpoilerAccepting);
			final int priority = mSimulationInfoProvider.computePriority(delayedbit, isSpoilerAccepting, isDuplicatorAccepting);
			final IGameState result = mGameStateFactory.getOrConstructGameState(spoilerSucc, duplicatorSucc, delayedbit , priority, isImmediatelyWinningForSpoiler);
			return result;
		}
	}
	private IGameLetter<LETTER, STATE> getOrConstuctSuccessorGameLetter(final SpoilerNwaVertex<LETTER, STATE> predVertex, final LETTER letter,
			final ETransitionType transitionType, final STATE spoilerSucc) {
		final boolean isDuplicatorAccepting = mOperand.isFinal(predVertex.getQ1());
		final boolean delayedbit = mSimulationInfoProvider.computeBitForDuplicatorVertex(predVertex.isB(), isDuplicatorAccepting);
		final IGameLetter<LETTER, STATE> result = mGameLetterFactory.getOrConstructGameLetter(spoilerSucc, predVertex.getQ1(), letter, delayedbit, transitionType);
		return result;
	}
	
	private boolean isDuplicatorSink(final IGameState state) {
		return unwrapSpoilerNwaVertex(state).getSink().equals(mDuplicatorWinningSink);
	}
	private boolean isSpoilerSink(final IGameState state) {
		return unwrapSpoilerNwaVertex(state).getSink().equals(mSpoilerWinningSink);	}

	

	
	private class GameStateFactory {
		private final NestedMap2<STATE, STATE, IGameState> mSpoiler2duplicator2vertexForFalse = new NestedMap2<>();
		private final NestedMap2<STATE, STATE, IGameState> mSpoiler2duplicator2vertexForTrue = new NestedMap2<>();
		private final IWinningSink<LETTER, STATE> mSpoilerWinningSink = null;
		
		private IGameState getGameState(final STATE spoilerState, final STATE duplicatorState, final boolean delayedbit) {
			if (delayedbit) {
				return mSpoiler2duplicator2vertexForTrue.get(spoilerState, duplicatorState);
			} else {
				return mSpoiler2duplicator2vertexForFalse.get(spoilerState, duplicatorState);
			}
		}
		
		public IGameState getOrConstructGameState(final STATE spoilerState, final STATE duplicatorState, 
				final boolean delayedbit, final int priority, final boolean isSpoilerWinningSink){
			IGameState result = getGameState(spoilerState, duplicatorState, delayedbit);
			if (result == null) {
				result = constructGameState(spoilerState, duplicatorState, delayedbit, priority, isSpoilerWinningSink);
			} else {
				assert priority == unwrapSpoilerNwaVertex(result).getPriority() : "inconsistent priority";
			}
			return result;
		}

		private IGameState constructGameState(final STATE spoilerState, final STATE duplicatorState, 
				final boolean delayedbit, final int priority, final boolean isSpoilerWinningSink) {
			final SpoilerNwaVertex<LETTER, STATE> spoilerNwaVertex;
			if (isSpoilerWinningSink) {
				spoilerNwaVertex = new SpoilerNwaVertex<LETTER, STATE>(priority, delayedbit, spoilerState, duplicatorState, mSpoilerWinningSink);
			} else {
				spoilerNwaVertex = new SpoilerNwaVertex<LETTER, STATE>(priority, delayedbit, spoilerState, duplicatorState);
			}
			final IGameState result = new GameSpoilerNwaVertex<LETTER, STATE>(spoilerNwaVertex);
			if (delayedbit) {
				mSpoiler2duplicator2vertexForTrue.put(spoilerState, duplicatorState, result);
			} else {
				mSpoiler2duplicator2vertexForFalse.put(spoilerState, duplicatorState, result);
			}
			mCache.addState(true, true, result);
			return result;
		}
	}
	
	private class GameLetterFactory {
		private final NestedMap3<STATE, STATE, LETTER, IGameLetter<LETTER, STATE>> mSpoi2Dupl2letter2GameLetter_ForFalse_ForInternal = new NestedMap3<>();
		private final NestedMap3<STATE, STATE, LETTER, IGameLetter<LETTER, STATE>> mSpoi2Dupl2letter2GameLetter_ForTrue_ForInternal = new NestedMap3<>();
		
		private final NestedMap3<STATE, STATE, LETTER, IGameLetter<LETTER, STATE>> mSpoi2Dupl2letter2GameLetter_ForFalse_ForCall = new NestedMap3<>();
		private final NestedMap3<STATE, STATE, LETTER, IGameLetter<LETTER, STATE>> mSpoi2Dupl2letter2GameLetter_ForTrue_ForCall = new NestedMap3<>();

		private final NestedMap3<STATE, STATE, LETTER, IGameLetter<LETTER, STATE>> mSpoi2Dupl2letter2GameLetter_ForFalse_ForReturn = new NestedMap3<>();
		private final NestedMap3<STATE, STATE, LETTER, IGameLetter<LETTER, STATE>> mSpoi2Dupl2letter2GameLetter_ForTrue_ForReturn = new NestedMap3<>();

		private IGameLetter<LETTER, STATE> getGameLetter(final STATE spoilerState, final STATE duplicatorState, final LETTER letter, final boolean delayedbit, final ETransitionType transitionType) {
			switch (transitionType) {
			case CALL:
				if (delayedbit) {
					return mSpoi2Dupl2letter2GameLetter_ForTrue_ForCall.get(spoilerState, duplicatorState, letter);
				} else {
					return mSpoi2Dupl2letter2GameLetter_ForFalse_ForCall.get(spoilerState, duplicatorState, letter);
				}
			case INTERNAL:
				if (delayedbit) {
					return mSpoi2Dupl2letter2GameLetter_ForTrue_ForInternal.get(spoilerState, duplicatorState, letter);
				} else {
					return mSpoi2Dupl2letter2GameLetter_ForFalse_ForInternal.get(spoilerState, duplicatorState, letter);
				}
			case RETURN:
				if (delayedbit) {
					return mSpoi2Dupl2letter2GameLetter_ForTrue_ForReturn.get(spoilerState, duplicatorState, letter);
				} else {
					return mSpoi2Dupl2letter2GameLetter_ForFalse_ForReturn.get(spoilerState, duplicatorState, letter);
				}
			case SINK:
			case SUMMARIZE_ENTRY:
			case SUMMARIZE_EXIT:
			default:
				throw new AssertionError("illegal transition type");
			}
		}
		
		public IGameLetter<LETTER, STATE> getOrConstructGameLetter(final STATE spoilerState, final STATE duplicatorState, final LETTER letter, 
				final boolean delayedbit, final ETransitionType transitionType){
			IGameLetter<LETTER, STATE> result = getGameLetter(spoilerState, duplicatorState, letter, delayedbit, transitionType);
			if (result == null) {
				result = constructGameLetter(spoilerState, duplicatorState, letter, delayedbit, transitionType);
			}
			return result;
		}
		
		private IGameLetter<LETTER, STATE> constructGameLetter(final STATE spoilerState, final STATE duplicatorState, 
				final LETTER letter, final boolean delayedbit, final ETransitionType transitionType) {
			final IGameLetter<LETTER, STATE> result = new DuplicatorNwaVertex<>(2, delayedbit, spoilerState, duplicatorState, letter, transitionType);
			switch (transitionType) {
			case CALL:
				if (delayedbit) {
					mSpoi2Dupl2letter2GameLetter_ForTrue_ForCall.put(spoilerState, duplicatorState, letter, result);
				} else {
					mSpoi2Dupl2letter2GameLetter_ForFalse_ForCall.put(spoilerState, duplicatorState, letter, result);
				}
				mCallAlphabet.add(result);
				break;
			case INTERNAL:
				if (delayedbit) {
					mSpoi2Dupl2letter2GameLetter_ForTrue_ForInternal.put(spoilerState, duplicatorState, letter, result);
				} else {
					mSpoi2Dupl2letter2GameLetter_ForFalse_ForInternal.put(spoilerState, duplicatorState, letter, result);
				}
				mInternalAlphabet.add(result);
				break;
			case RETURN:
				if (delayedbit) {
					mSpoi2Dupl2letter2GameLetter_ForTrue_ForReturn.put(spoilerState, duplicatorState, letter, result);
				} else {
					mSpoi2Dupl2letter2GameLetter_ForFalse_ForReturn.put(spoilerState, duplicatorState, letter, result);
				}
				mReturnAlphabet.add(result);
				break;
			case SINK:
			case SUMMARIZE_ENTRY:
			case SUMMARIZE_EXIT:
			default:
				throw new AssertionError("illegal transition type");
			}
			return result;
		}
	}
	
	private interface LetterAndSuccessorProvider<LETTER, STATE, T extends IOutgoingTransitionlet<LETTER, STATE>> {
		Set<LETTER> getLettersForSpoiler(STATE spoilerState);
		Iterable<T> getOutgoingTransitionsForSpoiler(STATE spoilerState, LETTER letter);
		Iterable<T> getOutgoingTransitionsForDuplicator(STATE duplicatorState, LETTER letter);
	}
	
	private class InternalLetterAndSuccessorProvider implements LetterAndSuccessorProvider<LETTER, STATE, OutgoingInternalTransition<LETTER, STATE>> {

		@Override
		public Set<LETTER> getLettersForSpoiler(final STATE state) {
			return mOperand.lettersInternal(state);
		}

		@Override
		public Iterable<OutgoingInternalTransition<LETTER, STATE>> getOutgoingTransitionsForSpoiler(final STATE state, final LETTER letter) {
			return mOperand.internalSuccessors(state, letter);
		}
		
		@Override
		public Iterable<OutgoingInternalTransition<LETTER, STATE>> getOutgoingTransitionsForDuplicator(final STATE state, final LETTER letter) {
			return mOperand.internalSuccessors(state, letter);
		}
	}
	
	private class CallLetterAndSuccessorProvider implements LetterAndSuccessorProvider<LETTER, STATE, OutgoingCallTransition<LETTER, STATE>> {

		@Override
		public Set<LETTER> getLettersForSpoiler(final STATE state) {
			return mOperand.lettersCall(state);
		}

		@Override
		public Iterable<OutgoingCallTransition<LETTER, STATE>> getOutgoingTransitionsForSpoiler(final STATE state, final LETTER letter) {
			return mOperand.callSuccessors(state, letter);
		}
		
		@Override
		public Iterable<OutgoingCallTransition<LETTER, STATE>> getOutgoingTransitionsForDuplicator(final STATE state, final LETTER letter) {
			return mOperand.callSuccessors(state, letter);
		}
	}
	
	
	private class ReturnLetterAndSuccessorProvider implements LetterAndSuccessorProvider<LETTER, STATE, OutgoingReturnTransition<LETTER, STATE>> {

		private final SpoilerNwaVertex<LETTER, STATE> mHier;
		
		public ReturnLetterAndSuccessorProvider(final SpoilerNwaVertex<LETTER, STATE> hier) {
			super();
			mHier = hier;
		}

		@Override
		public Set<LETTER> getLettersForSpoiler(final STATE lin) {
			final Set<LETTER> result = new HashSet<>();
			for (final OutgoingReturnTransition<LETTER, STATE> trans : mOperand.returnSuccessors(lin)) {
				if (trans.getHierPred().equals(mHier)) {
					result.add(trans.getLetter());
				}
			}
			return result;
		}

		@Override
		public Iterable<OutgoingReturnTransition<LETTER, STATE>> getOutgoingTransitionsForSpoiler(final STATE lin, final LETTER letter) {
			return mOperand.returnSuccessors(lin, mHier.getQ0(), letter);
		}
		
		@Override
		public Iterable<OutgoingReturnTransition<LETTER, STATE>> getOutgoingTransitionsForDuplicator(final STATE lin, final LETTER letter) {
			return mOperand.returnSuccessors(lin, mHier.getQ1(), letter);
		}

	}
	
	
}
