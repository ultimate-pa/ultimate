/*
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomatonCache;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.MultiOptimizationLevelRankingGenerator.FkvOptimization;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.IStateDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.DeterminizedState;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;

	

/**
 * Buchi Complementation based on 
 * 2004ATVA - Friedgut,Kupferman,Vardi - Büchi Complementation Made Tighter
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class BuchiComplementFKVNwa<LETTER,STATE> implements INestedWordAutomatonSimple<LETTER,STATE> {
	
	private final IUltimateServiceProvider m_Services;
	private final Logger m_Logger;
	
	/**
	 * TODO Allow definition of a maximal rank for cases where you know that
	 * this is sound. E.g. if the automaton is reverse deterministic a maximal
	 * rank of 2 is sufficient, see paper of Seth Forgaty.
	 */
	private final int m_UserDefinedMaxRank;
	
	private final INestedWordAutomatonSimple<LETTER,STATE> m_Operand;
	
	private final NestedWordAutomatonCache<LETTER, STATE> m_Cache;
	
	StateFactory<STATE> m_StateFactory;
	
	/**
	 * Maps DeterminizedState to its representative in the resulting automaton.
	 */
	private final Map<DeterminizedState<LETTER,STATE>,STATE> m_det2res =
		new HashMap<DeterminizedState<LETTER,STATE>, STATE>();
	
	/**
	 * Maps a state in resulting automaton to the FkvSubsetComponentState for which it
	 * was created.
	 */
	private final Map<STATE,FkvSubsetComponentState<LETTER,STATE>> m_res2scs =
		new HashMap<STATE, FkvSubsetComponentState<LETTER,STATE>>();
	
	/**
	 * Maps a LevelRankingState to its representative in the resulting automaton.
	 */
	private final Map<LevelRankingState<LETTER,STATE>,STATE> m_lrk2res =
		new HashMap<LevelRankingState<LETTER,STATE>, STATE>();
	
	/**
	 * Maps a state in resulting automaton to the LevelRankingState for which it
	 * was created.
	 */
	private final Map<STATE,LevelRankingState<LETTER,STATE>> m_res2lrk =
		new HashMap<STATE, LevelRankingState<LETTER,STATE>>();
	
	private final IStateDeterminizer<LETTER,STATE> m_StateDeterminizer;
	
	/**
	 * Highest rank that occured during the construction. Used only for
	 *  statistics.
	 */
	int m_HighestRank = -1;	
	
	private final MultiOptimizationLevelRankingGenerator<LETTER, STATE, LevelRankingConstraint<LETTER, STATE>> m_LevelRankingGenerator;
	
	private final STATE m_SinkState;
	
	
	
	public BuchiComplementFKVNwa(IUltimateServiceProvider services,
			INestedWordAutomatonSimple<LETTER,STATE> operand,
			IStateDeterminizer<LETTER,STATE> stateDeterminizer,
			StateFactory<STATE> stateFactory, FkvOptimization optimization,
			int userDefinedMaxRank) throws OperationCanceledException {
		m_Services = services;
		m_Logger = m_Services.getLoggingService().getLogger(LibraryIdentifiers.s_LibraryID);
		m_Operand = operand;
		m_StateFactory = stateFactory;
		m_Cache = new NestedWordAutomatonCache<LETTER, STATE>(
				m_Services,
				operand.getInternalAlphabet(), operand.getCallAlphabet(), 
				operand.getReturnAlphabet(), m_StateFactory);
		m_StateDeterminizer = stateDeterminizer;
		m_UserDefinedMaxRank = userDefinedMaxRank;
		m_LevelRankingGenerator = new MultiOptimizationLevelRankingGenerator<>(
				m_Services, m_Operand, optimization, userDefinedMaxRank);
		m_SinkState = constructSinkState();
	}
	
	
	private void constructInitialState() {
		DeterminizedState<LETTER,STATE> detState = m_StateDeterminizer.initialState();
		getOrAdd(detState, true);	
	}
	
	private STATE constructSinkState() {
		DeterminizedState<LETTER, STATE> detSinkState = new DeterminizedState<>(m_Operand);
		STATE resSinkState = m_StateDeterminizer.getState(detSinkState);
		m_Cache.addState(false, true, resSinkState);
		m_det2res.put(detSinkState, resSinkState);
		m_res2scs.put(resSinkState, new FkvSubsetComponentState<>(detSinkState));
		return resSinkState;
	}
	

	/**
	 * Return state of result automaton that represents lrkState. If no such
	 * state was constructed yet, construct it.
	 */
	private STATE getOrAdd(LevelRankingState<LETTER, STATE> lrkState) {
		if (lrkState.isEmpty()) {
			return m_SinkState;
		} else {
			STATE resSucc = m_lrk2res.get(lrkState);
			if (resSucc == null) {
				resSucc = m_StateFactory.buchiComplementFKV(lrkState);
				assert resSucc != null;
				m_Cache.addState(false, lrkState.isOempty(), resSucc);
				m_lrk2res.put(lrkState, resSucc);
				m_res2lrk.put(resSucc, lrkState);
				if (this.m_HighestRank < lrkState.m_HighestRank) {
					this.m_HighestRank = lrkState.m_HighestRank;
				}
			}
			return resSucc;
		}
	}
	
	
	/**
	 * Return state of result automaton that represents detState. If no such
	 * state was constructed yet, construct it.
	 */
	private STATE getOrAdd(DeterminizedState<LETTER,STATE> detState, boolean isInitial) {
		if (detState.isEmpty()) {
			assert !isInitial : "sink cannot be initial";
			return m_SinkState;
		} else {
			STATE resSucc = m_det2res.get(detState);
			if (resSucc == null) {
				resSucc = m_StateDeterminizer.getState(detState);
				assert resSucc != null;
				m_Cache.addState(isInitial, false, resSucc);
				m_det2res.put(detState, resSucc);
				m_res2scs.put(resSucc, new FkvSubsetComponentState<>(detState));
			}
			return resSucc;
		}
	}
	
	public int getHighesRank() {
		return m_HighestRank;
	}

	public int getPowersetStates() {
		return m_res2scs.size();
	}

	public int getRankStates() {
		return m_res2lrk.size();
	}
	


	@Override
	public Iterable<STATE> getInitialStates() {
		constructInitialState();
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


	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(
			STATE state, LETTER letter) {
		Collection<STATE> succs = m_Cache.succInternal(state, letter);
		if (succs == null) {
			Collection<STATE> resSuccs = new ArrayList<STATE>();
			FkvSubsetComponentState<LETTER,STATE> detUp = m_res2scs.get(state);
			if (detUp != null) {
				{
					DeterminizedState<LETTER,STATE> detSucc = m_StateDeterminizer.internalSuccessor(
							detUp.getDeterminizedState(), letter);
					STATE resSucc = getOrAdd(detSucc, false);
					m_Cache.addInternalTransition(state, letter, resSucc);
					resSuccs.add(resSucc);
				}
				boolean oIsEmpty = true; // considering O empty for subset component will safe some states
				LevelRankingConstraint<LETTER,STATE> constraints = new LevelRankingConstraintDrdCheck<LETTER,STATE>(
						m_Operand, oIsEmpty, m_UserDefinedMaxRank, m_StateDeterminizer.useDoubleDeckers());
				constraints.internalSuccessorConstraints(detUp, letter);
				Collection<LevelRankingState<LETTER,STATE>> result = m_LevelRankingGenerator.
						generateLevelRankings(constraints, true);
				if (result.size() > 2) {
					m_Logger.warn("big" + result.size());
				}
				for (LevelRankingState<LETTER,STATE> complSucc : result) {
					STATE resSucc = getOrAdd(complSucc);
					m_Cache.addInternalTransition(state, letter, resSucc);
					resSuccs.add(resSucc);
				}
			}
			LevelRankingState<LETTER,STATE> complUp = m_res2lrk.get(state);
			if (complUp != null) {
				LevelRankingConstraint<LETTER,STATE> constraints = new LevelRankingConstraintDrdCheck<LETTER,STATE>(
						m_Operand, complUp.isOempty(), m_UserDefinedMaxRank, m_StateDeterminizer.useDoubleDeckers());
				constraints.internalSuccessorConstraints(complUp, letter);
				Collection<LevelRankingState<LETTER,STATE>> result = m_LevelRankingGenerator.
						generateLevelRankings(constraints, false);
				if (result.size() > 4) {
					m_Logger.warn("big" + result.size());
				}
				for (LevelRankingState<LETTER,STATE> complSucc : result) {
					STATE resSucc = getOrAdd(complSucc);
					m_Cache.addInternalTransition(state, letter, resSucc);
					resSuccs.add(resSucc);
				}
			}
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
			Collection<STATE> resSuccs = new ArrayList<STATE>();
			FkvSubsetComponentState<LETTER,STATE> detUp = m_res2scs.get(state);
			if (detUp != null) {
				{
					DeterminizedState<LETTER,STATE> detSucc = m_StateDeterminizer.callSuccessor(
							detUp.getDeterminizedState(), letter);
					STATE resSucc = getOrAdd(detSucc, false);
					m_Cache.addCallTransition(state, letter, resSucc);
					resSuccs.add(resSucc);
				}
				boolean oIsEmpty = true; // considering O empty for subset component will safe some states
				LevelRankingConstraint<LETTER, STATE> constraints = new LevelRankingConstraintDrdCheck<LETTER, STATE>(
						m_Operand, oIsEmpty, m_UserDefinedMaxRank, m_StateDeterminizer.useDoubleDeckers());
				constraints.callSuccessorConstraints(detUp, letter);
				Collection<LevelRankingState<LETTER, STATE>> result = m_LevelRankingGenerator.
						generateLevelRankings(constraints, true);
				for (LevelRankingState<LETTER, STATE> complSucc : result) {
					STATE resSucc = getOrAdd(complSucc);
					m_Cache.addCallTransition(state, letter, resSucc);
					resSuccs.add(resSucc);
				}
			}
			LevelRankingState<LETTER, STATE> complUp = m_res2lrk.get(state);
			if (complUp != null) {
				LevelRankingConstraint<LETTER, STATE> constraints = new LevelRankingConstraintDrdCheck<LETTER, STATE>(
						m_Operand, complUp.isOempty(), m_UserDefinedMaxRank, m_StateDeterminizer.useDoubleDeckers());
				constraints.callSuccessorConstraints(complUp, letter);
				Collection<LevelRankingState<LETTER, STATE>> result = m_LevelRankingGenerator.
						generateLevelRankings(constraints, false);
				for (LevelRankingState<LETTER, STATE> complSucc : result) {
					STATE resSucc = getOrAdd(complSucc);
					m_Cache.addCallTransition(state, letter, resSucc);
					resSuccs.add(resSucc);
				}
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
			Collection<STATE> resSuccs = new ArrayList<STATE>();
			FkvSubsetComponentState<LETTER,STATE> detUp = m_res2scs.get(state);
			FkvSubsetComponentState<LETTER,STATE> detDown = m_res2scs.get(hier);
			if (detUp != null) {
				{
					DeterminizedState<LETTER,STATE> detSucc = m_StateDeterminizer.returnSuccessor(
							detUp.getDeterminizedState(), detDown.getDeterminizedState(), letter);
					STATE resSucc = getOrAdd(detSucc, false);
					m_Cache.addReturnTransition(state, hier, letter, resSucc);
					resSuccs.add(resSucc);
				}
				boolean oIsEmpty = true; // considering O empty for subset component will safe some states
				LevelRankingConstraint<LETTER, STATE> constraints = new LevelRankingConstraintDrdCheck<LETTER, STATE>(
						m_Operand, oIsEmpty, m_UserDefinedMaxRank, m_StateDeterminizer.useDoubleDeckers());
				constraints.returnSuccessorConstraints(detUp, detDown, letter);
				Collection<LevelRankingState<LETTER, STATE>> result = m_LevelRankingGenerator.
						generateLevelRankings(constraints, true);
				for (LevelRankingState<LETTER, STATE> complSucc : result) {
					STATE resSucc = getOrAdd(complSucc);
					m_Cache.addReturnTransition(state, hier, letter, resSucc);
					resSuccs.add(resSucc);
				}
			}
			LevelRankingState<LETTER, STATE> complUp = m_res2lrk.get(state);
			IFkvState<LETTER, STATE> complDown;
			if (m_res2scs.containsKey(hier)) {
				complDown = m_res2scs.get(hier);
			} else {
				assert m_res2lrk.containsKey(hier);
				complDown = m_res2lrk.get(hier);
			}
			if (complUp != null) {
				LevelRankingConstraint<LETTER, STATE> constraints = new LevelRankingConstraintDrdCheck<LETTER, STATE>(
						m_Operand, complUp.isOempty(), m_UserDefinedMaxRank, m_StateDeterminizer.useDoubleDeckers());
				constraints.returnSuccessorConstraints(complUp, complDown, letter);
				Collection<LevelRankingState<LETTER, STATE>> result = m_LevelRankingGenerator.
						generateLevelRankings(constraints, false);
				for (LevelRankingState<LETTER, STATE> complSucc : result) {
					STATE resSucc = getOrAdd(complSucc);
					m_Cache.addReturnTransition(state, hier, letter, resSucc);
					resSuccs.add(resSucc);
				}
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
