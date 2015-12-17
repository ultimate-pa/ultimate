/*
 * Copyright (C) 2015-2016 Daniel Tischner
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.direct;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.AGameGraph;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.DuplicatorVertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.SpoilerVertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.Vertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.util.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.UnionFind;

/**
 * Game graph that realizes <b>direct simulation</b>.<br/>
 * In direct simulation each time <i>Spoiler</i> visits a final state
 * <i>Duplicator</i> must also visit one at his next turn.<br/>
 * <br/>
 * 
 * If its impossible for <i>Spoiler</i> to build a word such that
 * <i>Duplicator</i> can not fulfill its condition we say <b>q1 direct simulates
 * q0</b> where q0 was the starting state of <i>Spoiler</i> and q1 of
 * <i>Duplicator</i>.
 * 
 * @author Daniel Tischner
 *
 * @param <LETTER>
 *            Letter class of buechi automaton
 * @param <STATE>
 *            State class of buechi automaton
 */
public final class DirectGameGraph<LETTER, STATE> extends AGameGraph<LETTER, STATE> {

	/**
	 * The underlying buechi automaton from which the game graph gets generated.
	 */
	private final INestedWordAutomatonOldApi<LETTER, STATE> m_Buechi;
	/**
	 * The logger used by the Ultimate framework.
	 */
	private final Logger m_Logger;
	/**
	 * The state factory used for creating states.
	 */
	private final StateFactory<STATE> m_StateFactory;

	/**
	 * Creates a new direct game graph by using the given buechi automaton.
	 * 
	 * @param services
	 *            Service provider of Ultimate framework.
	 * @param buechi
	 *            The underlying buechi automaton from which the game graph gets
	 *            generated.
	 * @param stateFactory
	 *            The state factory used for creating states.
	 * @throws OperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	public DirectGameGraph(final IUltimateServiceProvider services,
			final INestedWordAutomatonOldApi<LETTER, STATE> buechi, final StateFactory<STATE> stateFactory)
					throws OperationCanceledException {
		super(services, stateFactory);
		m_Buechi = buechi;
		m_Logger = getServiceProvider().getLoggingService().getLogger(LibraryIdentifiers.s_LibraryID);
		m_StateFactory = stateFactory;
		generateGameGraphFromBuechi();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.
	 * buchiReduction.AGameGraph#generateBuchiAutomatonFromGraph()
	 */
	@Override
	protected NestedWordAutomaton<LETTER, STATE> generateBuchiAutomatonFromGraph() throws OperationCanceledException {
		// Determine which states to merge
		UnionFind<STATE> uf = new UnionFind<>();
		for (STATE state : m_Buechi.getStates()) {
			uf.makeEquivalenceClass(state);
		}
		HashRelation<STATE, STATE> similarStates = new HashRelation<>();
		for (SpoilerVertex<LETTER, STATE> v : getSpoilerVertices()) {
			// all the states we need are in V1...
			if (v.getPM(null, getGlobalInfinity()) < getGlobalInfinity()) {
				STATE state1 = v.getQ0();
				STATE state2 = v.getQ1();
				similarStates.addPair(state1, state2);

			}
		}
		// Merge states if they simulate each other
		for (STATE state1 : similarStates.getDomain()) {
			for (STATE state2 : similarStates.getImage(state1)) {
				// Only merge if simulation holds in both directions
				if (similarStates.containsPair(state2, state1)) {
					uf.union(state1, state2);
				}
			}
		}

		if (getServiceProvider().getProgressMonitorService() != null
				&& !getServiceProvider().getProgressMonitorService().continueProcessing()) {
			m_Logger.debug("Stopped in generateBuchiAutomatonFromGraph/table filled");
			throw new OperationCanceledException(this.getClass());
		}

		// Merge states
		NestedWordAutomaton<LETTER, STATE> result = new NestedWordAutomaton<>(getServiceProvider(),
				m_Buechi.getInternalAlphabet(), null, null, m_StateFactory);
		Set<STATE> representativesOfInitials = new HashSet<>();
		for (STATE initial : m_Buechi.getInitialStates()) {
			representativesOfInitials.add(uf.find(initial));
		}

		Map<STATE, STATE> input2result = new HashMap<>(m_Buechi.size());
		for (STATE representative : uf.getAllRepresentatives()) {
			boolean isInitial = representativesOfInitials.contains(representative);
			boolean isFinal = m_Buechi.isFinal(representative);
			Set<STATE> eqClass = uf.getEquivalenceClassMembers(representative);
			STATE resultState = m_StateFactory.minimize(eqClass);
			result.addState(isInitial, isFinal, resultState);
			for (STATE eqClassMember : eqClass) {
				input2result.put(eqClassMember, resultState);
			}
		}

		for (STATE state : uf.getAllRepresentatives()) {
			STATE pred = input2result.get(state);
			for (OutgoingInternalTransition<LETTER, STATE> outTrans : m_Buechi.internalSuccessors(state)) {
				STATE succ = input2result.get(outTrans.getSucc());
				result.addInternalTransition(pred, outTrans.getLetter(), succ);
			}
		}

		if (getServiceProvider().getProgressMonitorService() != null
				&& !getServiceProvider().getProgressMonitorService().continueProcessing()) {
			m_Logger.debug("Stopped in generateBuchiAutomatonFromGraph/states added to result BA");
			throw new OperationCanceledException(this.getClass());
		}
		return result;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.
	 * buchiReduction.AGameGraph#generateGameGraphFromBuechi()
	 */
	@Override
	protected void generateGameGraphFromBuechi() throws OperationCanceledException {
		// Calculate v1 [paper ref 10]
		for (STATE q0 : m_Buechi.getStates()) {
			for (STATE q1 : m_Buechi.getStates()) {
				SpoilerVertex<LETTER, STATE> v1e = new SpoilerVertex<>(0, false, q0, q1);
				addSpoilerVertex(v1e);
			}

			if (getServiceProvider().getProgressMonitorService() != null
					&& !getServiceProvider().getProgressMonitorService().continueProcessing()) {
				m_Logger.debug("Stopped in generateGameGraphFromBuechi/calculating v0 und v1");
				throw new OperationCanceledException(this.getClass());
			}
		}
		// Calculate v0 and edges [paper ref 10, 11, 12]
		for (STATE q0 : m_Buechi.getStates()) {
			for (STATE q1 : m_Buechi.getStates()) {
				Set<LETTER> relevantLetters = new HashSet<>();
				relevantLetters.addAll(m_Buechi.lettersInternalIncoming(q0));
				relevantLetters.addAll(m_Buechi.lettersInternal(q1));
				for (LETTER s : relevantLetters) {
					DuplicatorVertex<LETTER, STATE> v0e = new DuplicatorVertex<>(0, false, q0, q1, s);
					addDuplicatorVertex(v0e);
					// V1 -> V0 edges [paper ref 11]
					for (STATE pred0 : m_Buechi.predInternal(q0, s)) {
						// Only add edge if duplicator does not directly loose
						if (!m_Buechi.isFinal(pred0) || m_Buechi.isFinal(q1)) {
							addEdge(getSpoilerVertex(pred0, q1, false), v0e);
						}
					}
					// V0 -> V1 edges [paper ref 11]
					for (STATE succ1 : m_Buechi.succInternal(q1, s)) {
						// Only add edge if duplicator does not directly loose
						if (!m_Buechi.isFinal(q0) || m_Buechi.isFinal(succ1)) {
							addEdge(v0e, getSpoilerVertex(q0, succ1, false));
						}
					}
				}
			}

			if (getServiceProvider().getProgressMonitorService() != null
					&& !getServiceProvider().getProgressMonitorService().continueProcessing()) {
				m_Logger.debug("Stopped in generateGameGraphFromBuechi/calculating v0 und v1");
				throw new OperationCanceledException(this.getClass());
			}
		}
		// global infinity = (# of pr==1 nodes) + 1
		increaseGlobalInfinity();
		if (m_Logger.isDebugEnabled()) {
			m_Logger.debug("Infinity is " + getGlobalInfinity());
			m_Logger.debug("Number of vertices in game graph: "
					+ (getDuplicatorVertices().size() + getSpoilerVertices().size()));
			m_Logger.debug("Number of vertices in v0: " + getDuplicatorVertices().size());
			m_Logger.debug("Number of vertices in v1: " + getSpoilerVertices().size());
			int edges = 0;
			for (Set<Vertex<LETTER, STATE>> hs : getSuccessorGroups()) {
				edges += hs.size();
			}
			m_Logger.debug("Number of edges in game graph: " + edges);
		}
	}

}
