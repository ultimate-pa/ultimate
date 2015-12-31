/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.DoubleDecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomatonCache;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.util.PowersetIterator;

	

/**
 * Buchi Complementation based on the algorithm proposed by Frantisek Blahoudek
 * and Jan Stejcek. This complementation is only sound for a special class of
 * automata whose working title is TABA (termination analysis Büchi automata).
 * @author heizmann@informatik.uni-freiburg.de
 */
public class BuchiComplementNCSBNwa<LETTER,STATE> implements INestedWordAutomatonSimple<LETTER,STATE> {
	
	private final IUltimateServiceProvider m_Services;
	private final Logger m_Logger;
	
	private final INestedWordAutomatonSimple<LETTER,STATE> m_Operand;
	
	private final NestedWordAutomatonCache<LETTER, STATE> m_Cache;
	
	private final StateFactory<STATE> m_StateFactory;
	
	private final StateWithRankInfo<STATE> m_EmptyStackStateWRI;
	
	/**
	 * Maps BlaStState to its representative in the resulting automaton.
	 */
	private final Map<LevelRankingState<LETTER,STATE>,STATE> m_det2res =
		new HashMap<LevelRankingState<LETTER,STATE>, STATE>();
	
	/**
	 * Maps a state in resulting automaton to the BlaStState for which it
	 * was created.
	 */
	private final Map<STATE, LevelRankingState<LETTER,STATE>> m_res2det =
		new HashMap<STATE, LevelRankingState<LETTER,STATE>>();
	private final boolean m_OmitNonAcceptingSink = true;
	
	
	public BuchiComplementNCSBNwa(IUltimateServiceProvider services,
			INestedWordAutomatonSimple<LETTER,STATE> operand,
			StateFactory<STATE> stateFactory) throws OperationCanceledException {
		m_Services = services;
		m_Logger = m_Services.getLoggingService().getLogger(LibraryIdentifiers.s_LibraryID);
		m_Operand = operand;
		m_StateFactory = stateFactory;
		m_Cache = new NestedWordAutomatonCache<LETTER, STATE>(
				m_Services,
				operand.getInternalAlphabet(), operand.getCallAlphabet(), 
				operand.getReturnAlphabet(), m_StateFactory);
		m_EmptyStackStateWRI = new StateWithRankInfo<STATE>(getEmptyStackState());
		constructInitialState();
	}
	
	
	private void constructInitialState() {
		LevelRankingState<LETTER,STATE> lvlrk = new LevelRankingState<LETTER,STATE>(m_Operand);
		for (STATE state : m_Operand.getInitialStates()) {
			if (m_Operand.isFinal(state)) {
				lvlrk.addRank(m_EmptyStackStateWRI, state, 2, false);
			} else {
				lvlrk.addRank(m_EmptyStackStateWRI, state, 3, false);
			}
		}
		getOrAdd(true, lvlrk);
	}
	
	/**
	 * Return state of result automaton that represents detState. If no such
	 * state was constructed yet, construct it.
	 */
	private STATE getOrAdd(boolean isInitial, 
			LevelRankingState<LETTER,STATE> lvlrk) {
		STATE resState = m_det2res.get(lvlrk);
		if (resState == null) {
			resState = m_StateFactory.buchiComplementNCSB(lvlrk);
			m_det2res.put(lvlrk, resState);
			m_res2det.put(resState, lvlrk);
			boolean isFinal = !lvlrk.isNonAcceptingSink() && lvlrk.isOempty();
			m_Cache.addState(isInitial, isFinal, resState);
		} else {
			assert !isInitial;
		}
		return resState;
	}
	
	@Override
	public Iterable<STATE> getInitialStates() {
		return m_Cache.getInitialStates();
	}


	@Override
	public Set<LETTER> getInternalAlphabet() {
		return m_Operand.getInternalAlphabet();
	}

	@Override
	public Set<LETTER> getCallAlphabet() {
		return m_Operand.getCallAlphabet();
	}

	@Override
	public Set<LETTER> getReturnAlphabet() {
		return m_Operand.getReturnAlphabet();
	}

	@Override
	public StateFactory<STATE> getStateFactory() {
		return m_StateFactory;
	}
	
	@Override
	public boolean isInitial(STATE state) {
		return m_Cache.isInitial(state);
	}

	@Override
	public boolean isFinal(STATE state) {
		return m_Cache.isFinal(state);
	}

	@Override
	public STATE getEmptyStackState() {
		return m_Cache.getEmptyStackState();
	}

	@Override
	public Set<LETTER> lettersInternal(STATE state) {
		return m_Operand.getInternalAlphabet();
	}

	@Override
	public Set<LETTER> lettersCall(STATE state) {
		return m_Operand.getCallAlphabet();
	}

	@Override
	public Set<LETTER> lettersReturn(STATE state) {
		return m_Operand.getReturnAlphabet();
	}
	
	private LevelRankingConstraintDrdCheck<LETTER, STATE> computeSuccLevelRankingConstraints_Internal(
			STATE state, LETTER letter) {
		LevelRankingState<LETTER,STATE> lvlrkState = m_res2det.get(state);
		if (lvlrkState.isNonAcceptingSink()) {
			return new LevelRankingConstraintDrdCheck<LETTER, STATE>();
		}
		LevelRankingConstraintDrdCheck<LETTER, STATE> lrcwh = new LevelRankingConstraintDrdCheck(m_Operand, lvlrkState.isOempty(), 7777, true);
		for (StateWithRankInfo<STATE> down : lvlrkState.getDownStates()) {
			for (StateWithRankInfo<STATE> up : lvlrkState.getUpStates(down)) {
				boolean hasSuccessor = false;
				for (OutgoingInternalTransition<LETTER, STATE> trans : 
								m_Operand.internalSuccessors(up.getState(), letter)) {
					hasSuccessor = true;
					lrcwh.addConstaint(down, trans.getSucc(), up.getRank(), up.isInO(), m_Operand.isFinal(up.getState()));
				}
				if (transitionWouldAnnihilateEvenRank(down, up, hasSuccessor)) {
					return new LevelRankingConstraintDrdCheck<LETTER, STATE>();
				}
			}
		}
		return lrcwh;
	}
	
	private boolean transitionWouldAnnihilateEvenRank(
			StateWithRankInfo<STATE> down, StateWithRankInfo<STATE> up,
			boolean hasSuccessor) {
		return !hasSuccessor && !m_Operand.isFinal(up.getState()) && LevelRankingConstraint.isEven(up.getRank());
	}


	private LevelRankingConstraintDrdCheck<LETTER, STATE> computeSuccLevelRankingConstraints_Call(
			STATE state, LETTER letter) {
		LevelRankingState<LETTER,STATE> lvlrkState = m_res2det.get(state);
		if (lvlrkState.isNonAcceptingSink()) {
			return new LevelRankingConstraintDrdCheck<LETTER, STATE>();
		}
		LevelRankingConstraintDrdCheck<LETTER, STATE> lrcwh = new LevelRankingConstraintDrdCheck(m_Operand, lvlrkState.isOempty(), 7777, true);
		for (StateWithRankInfo<STATE> down : lvlrkState.getDownStates()) {
			for (StateWithRankInfo<STATE> up : lvlrkState.getUpStates(down)) {
				boolean hasSuccessor = false;
				for (OutgoingCallTransition<LETTER, STATE> trans : 
								m_Operand.callSuccessors(up.getState(), letter)) {
					hasSuccessor = true;
					lrcwh.addConstaint(up, trans.getSucc(), up.getRank(), up.isInO(), m_Operand.isFinal(up.getState()));
				}
				if (transitionWouldAnnihilateEvenRank(down, up, hasSuccessor)) {
					return new LevelRankingConstraintDrdCheck<LETTER, STATE>();
				}
			}
		}
		return lrcwh;
	}
	
	private LevelRankingConstraintDrdCheck<LETTER, STATE> computeSuccLevelRankingConstraints_Return(
			STATE state, STATE hier, LETTER letter) {
		LevelRankingState<LETTER,STATE> lvlrkState = m_res2det.get(state);
		LevelRankingState<LETTER,STATE> lvlrkHier = m_res2det.get(hier);
		if (lvlrkState.isNonAcceptingSink()) {
			return new LevelRankingConstraintDrdCheck<LETTER, STATE>();
		}
		LevelRankingConstraintDrdCheck<LETTER, STATE> lrcwh = new LevelRankingConstraintDrdCheck(m_Operand, lvlrkState.isOempty(), 7777, true);
		for (StateWithRankInfo<STATE> downHier : lvlrkHier.getDownStates()) {
			for (StateWithRankInfo<STATE> upHier : lvlrkHier.getUpStates(downHier)) {
				if (!lvlrkState.getDownStates().contains(upHier)) {
					continue;
				}
				for (StateWithRankInfo<STATE> up : lvlrkState.getUpStates(upHier)) {
					boolean hasSuccessor = false;
					for (OutgoingReturnTransition<LETTER, STATE> trans : 
						m_Operand.returnSucccessors(up.getState(), upHier.getState(), letter)) {
						hasSuccessor = true;
						lrcwh.addConstaint(downHier, trans.getSucc(), up.getRank(), up.isInO(), m_Operand.isFinal(up.getState()));
					}
					if (transitionWouldAnnihilateEvenRank(downHier, up, hasSuccessor)) {
						return new LevelRankingConstraintDrdCheck<LETTER, STATE>();
					}
				}
			}
		}
		return lrcwh;
	}


	private List<LevelRankingState<LETTER, STATE>> computeSuccLevelRankingStates(
			LevelRankingConstraintDrdCheck<LETTER, STATE> lrcwh) {
		if (lrcwh.isNonAcceptingSink()) {
			if (m_OmitNonAcceptingSink ) {
				return Collections.emptyList();
			} else {
				return Collections.singletonList(new LevelRankingState<LETTER, STATE>());
			}
		}
//		if (lrcwh.aroseFromDelayedRankDecrease()) {
		if (lrcwh.isTargetOfDelayedRankDecrease(3)) {
			// in this case we do not want to have successor states
			return Collections.emptyList();
		}
		List<LevelRankingState<LETTER, STATE>> succLvls = new ArrayList<LevelRankingState<LETTER,STATE>>();
		Set<DoubleDecker<StateWithRankInfo<STATE>>> allDoubleDeckersWithVoluntaryDecrease = 
				computeDoubleDeckersWithVoluntaryDecrease(lrcwh);
		Iterator<Set<DoubleDecker<StateWithRankInfo<STATE>>>> it = 
				new PowersetIterator<DoubleDecker<StateWithRankInfo<STATE>>>(allDoubleDeckersWithVoluntaryDecrease);
		while(it.hasNext()) {
			Set<DoubleDecker<StateWithRankInfo<STATE>>> subset = it.next();
			LevelRankingState<LETTER, STATE> succCandidate = computeLevelRanking(lrcwh, subset);
			if (succCandidate != null) {
				succLvls.add(succCandidate);
			}
		}
		return succLvls;
	}


	private Set<DoubleDecker<StateWithRankInfo<STATE>>> computeDoubleDeckersWithVoluntaryDecrease(
			LevelRankingConstraintDrdCheck<LETTER, STATE> lrcwh) {
		Set<DoubleDecker<StateWithRankInfo<STATE>>> doubleDeckersWithVoluntaryDecrease = new HashSet<DoubleDecker<StateWithRankInfo<STATE>>>();
		for (DoubleDecker<StateWithRankInfo<STATE>> predWasAccepting : lrcwh.getPredecessorWasAccepting()) {
			// we will decrease the rank if 
			// predecessor was final
			// state has even rank (resp. lowest rank constraint is even)
			// state is not final
			int rank = lrcwh.getRank(predWasAccepting.getDown(), predWasAccepting.getUp().getState());
			boolean isFinal = m_Operand.isFinal(predWasAccepting.getUp().getState()); 
			if (LevelRankingState.isEven(rank) && !isFinal) {
				doubleDeckersWithVoluntaryDecrease.add(predWasAccepting);
			}
		}
		return doubleDeckersWithVoluntaryDecrease;
	}


	private LevelRankingState<LETTER, STATE> computeLevelRanking(LevelRankingConstraintDrdCheck<LETTER, STATE> lrcwh,
			Set<DoubleDecker<StateWithRankInfo<STATE>>> doubleDeckersWithVoluntaryDecrease) {
		LevelRankingState<LETTER, STATE> result = new LevelRankingState<LETTER, STATE>(m_Operand);
		for (StateWithRankInfo<STATE> down : lrcwh.getDownStates()) {
			for (StateWithRankInfo<STATE> up : lrcwh.getUpStates(down)) {
				final boolean oCandidate = up.isInO();
				final boolean inO;
				int rank = up.getRank();
				switch (rank) {
				case 3:
					if (m_Operand.isFinal(up.getState())) {
						rank = 2;
						inO = oCandidate;
					} else {
						inO = false;
					}
					break;
				case 2:
					if (doubleDeckersWithVoluntaryDecrease.contains(new DoubleDecker<StateWithRankInfo<STATE>>(down, up))) {
						rank = 1;
						inO = false;
					} else {
						inO = oCandidate;
					}
					break;
				case 1:
					if (m_Operand.isFinal(up.getState())) {
						return null;
					} else {
						inO = false;
					}
					break;
				default:
					throw new AssertionError("no other ranks allowed");
				}
				result.addRank(down, up.getState(), rank, inO);
			}
		}
		return result;
	}


	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(
			STATE state, LETTER letter) {
		Collection<STATE> succs = m_Cache.succInternal(state, letter);
		if (succs == null) {
			LevelRankingConstraintDrdCheck<LETTER, STATE> lrcwh = computeSuccLevelRankingConstraints_Internal(
					state, letter);
			List<LevelRankingState<LETTER, STATE>> succLvls = computeSuccLevelRankingStates(lrcwh);
			List<STATE> computedSuccs = new ArrayList<>(); 
			for (LevelRankingState<LETTER, STATE> succLvl : succLvls) {
				STATE resSucc = getOrAdd(false, succLvl);
				computedSuccs.add(resSucc);
			}
			m_Cache.addInternalTransitions(state, letter, computedSuccs);
		}
		return m_Cache.internalSuccessors(state, letter);
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(
			STATE state) {
		for (LETTER letter : getInternalAlphabet()) {
			internalSuccessors(state, letter);
		}
		return m_Cache.internalSuccessors(state);
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(
			STATE state, LETTER letter) {
		Collection<STATE> succs = m_Cache.succCall(state, letter);
		if (succs == null) {
			LevelRankingConstraintDrdCheck<LETTER, STATE> lrcwh = computeSuccLevelRankingConstraints_Call(
					state, letter);
			List<LevelRankingState<LETTER, STATE>> succLvls = computeSuccLevelRankingStates(lrcwh);
			for (LevelRankingState<LETTER, STATE> succLvl : succLvls) {
				STATE resSucc = getOrAdd(false, succLvl);
				m_Cache.addCallTransition(state, letter, resSucc);
			}
		}
		return m_Cache.callSuccessors(state, letter);
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(
			STATE state) {
		for (LETTER letter : getCallAlphabet()) {
			callSuccessors(state, letter);
		}
		return m_Cache.callSuccessors(state);
	}



	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSucccessors(
			STATE state, STATE hier, LETTER letter) {
		Collection<STATE> succs = m_Cache.succReturn(state, hier, letter);
		if (succs == null) {
			LevelRankingConstraintDrdCheck<LETTER, STATE> lrcwh = computeSuccLevelRankingConstraints_Return(
					state, hier, letter);
			List<LevelRankingState<LETTER, STATE>> succLvls = computeSuccLevelRankingStates(lrcwh);
			for (LevelRankingState<LETTER, STATE> succLvl : succLvls) {
				STATE resSucc = getOrAdd(false, succLvl);
				m_Cache.addReturnTransition(state, hier, letter, resSucc);
			}
		}
		return m_Cache.returnSucccessors(state, hier, letter);
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessorsGivenHier(
			STATE state, STATE hier) {
		for (LETTER letter : getReturnAlphabet()) {
			returnSucccessors(state, hier, letter);
		}
		return m_Cache.returnSuccessorsGivenHier(state, hier);
	}

	@Override
	public int size() {
		return m_Cache.size();
	}

	@Override
	public Set<LETTER> getAlphabet() {
		throw new UnsupportedOperationException();	}

	@Override
	public String sizeInformation() {
		return "size Information not available";
	}
	
	
	
	
	



}
