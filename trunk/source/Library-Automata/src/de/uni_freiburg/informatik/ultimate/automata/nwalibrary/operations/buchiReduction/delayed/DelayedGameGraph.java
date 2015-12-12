/*
 * Copyright (C) 2015-2016 Daniel Tischner
 * Copyright (C) 2012-2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Oleksii Saukh (saukho@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.delayed;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StringFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.AGameGraph;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.DuplicatorVertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.SpoilerVertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.Vertex;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;

/**
 * Game graph that realizes <b>delayed simulation</b>.<br/>
 * In delayed simulation each time <i>Spoiler</i> visits a final state
 * <i>Duplicator</i> must at least visit one in the future for coverage.<br/>
 * To reflect <i>Duplicator</i>s coverage the delayed game graph uses vertices
 * that have an extra bit.<br/>
 * <br/>
 * 
 * If its impossible for <i>Spoiler</i> to build a word such that
 * <i>Duplicator</i> can not fulfill its condition we say <b>q1 delayed
 * simulates q0</b> where q0 was the starting state of <i>Spoiler</i> and q1 of
 * <i>Duplicator</i>.
 * 
 * @author Daniel Tischner
 * @author Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * @author Oleksii Saukh (saukho@informatik.uni-freiburg.de)
 * 
 * @param <LETTER>
 *            Letter class of buechi automaton
 * @param <STATE>
 *            State class of buechi automaton
 */
public final class DelayedGameGraph<LETTER, STATE> extends AGameGraph<LETTER, STATE> {

	/**
	 * The underlying buechi automaton from which the game graph gets generated.
	 */
	private final INestedWordAutomatonOldApi<LETTER, STATE> m_Buechi;
	/**
	 * The logger used by the Ultimate framework.
	 */
	private final Logger m_Logger;

	/**
	 * Creates a new delayed game graph by using the given buechi automaton.
	 * 
	 * @param services
	 *            Service provider of Ultimate framework.
	 * @param buechi
	 *            The underlying buechi automaton from which the game graph gets
	 *            generated.
	 * @throws OperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	public DelayedGameGraph(final IUltimateServiceProvider services,
			final INestedWordAutomatonOldApi<LETTER, STATE> buechi) throws OperationCanceledException {
		super(services);
		m_Buechi = buechi;
		m_Logger = getServiceProvider().getLoggingService().getLogger(LibraryIdentifiers.s_LibraryID);
		generateGameGraphFromBuechi();
	}

	/**
	 * Gets the amount of {@link SpoilerVertex} objects that exist in the game
	 * graph with representation (q0, q1). Since there can be such vertices with
	 * the extra bit false and true the returned value is between zero and two.
	 * 
	 * @param q0
	 *            The state spoiler is at
	 * @param q1
	 *            The state duplicator is at
	 * @return The amount of {@link SpoilerVertex} objects that exist in the
	 *         game graph with representation (q0, q1). Since there can be such
	 *         vertices with the extra bit false and true the returned value is
	 *         between zero and two.
	 */
	private int getAmountOfBitsForSpoilerVertix(final STATE q0, final STATE q1) {
		int amount = 0;

		if (getSpoilerVertex(q0, q1, false) != null) {
			amount++;
		}

		if (getSpoilerVertex(q0, q1, true) != null) {
			amount++;
		}

		return amount;
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
		ArrayList<STATE> states = new ArrayList<>();
		states.addAll(m_Buechi.getStates());
		boolean[][] table = new boolean[states.size()][states.size()];
		for (SpoilerVertex<LETTER, STATE> v : getSpoilerVertices()) {
			// All the states we need are in spoiler vertices
			if ((m_Buechi.isFinal(v.getQ0()) && m_Buechi.isFinal(v.getQ1())) ^ v.isB() ^ m_Buechi.isFinal(v.getQ0())) {
				// Skip all elements that not fulfill:
				// Letting b=1 if q0 in F and q1 not in F, and b=0 else
				continue;
			}
			if (v.getPM(null, getGlobalInfinity()) < getGlobalInfinity()) {
				table[states.indexOf(v.getQ0())][states.indexOf(v.getQ1())] = true;
			}
		}

		if (getServiceProvider().getProgressMonitorService() != null
				&& !getServiceProvider().getProgressMonitorService().continueProcessing()) {
			m_Logger.debug("Stopped in generateBuchiAutomaton/table filled");
			throw new OperationCanceledException(this.getClass());
		}

		// Merge states
		boolean[] marker = new boolean[states.size()];
		Set<STATE> temp = new HashSet<>();
		HashMap<STATE, STATE> oldSNames2newSNames = new HashMap<>();
		@SuppressWarnings("unchecked")
		StateFactory<STATE> snf = (StateFactory<STATE>) new StringFactory();
		NestedWordAutomaton<LETTER, STATE> result = new NestedWordAutomaton<>(getServiceProvider(),
				m_Buechi.getInternalAlphabet(), null, null, snf);
		for (int i = 0; i < states.size(); i++) {
			if (marker[i])
				continue;
			temp.clear();
			temp.add(states.get(i));
			marker[i] = true;
			boolean isFinal = m_Buechi.isFinal(states.get(i));
			boolean isInitial = m_Buechi.isInitial(states.get(i));
			for (int j = i; j < states.size(); j++) {
				if (table[i][j] && table[j][i] && !marker[j]) {
					temp.add(states.get(j));
					marker[j] = true;
					if (m_Buechi.isFinal(states.get(j)))
						isFinal = true;
					if (m_Buechi.isInitial(states.get(j)))
						isInitial = true;
				}
			}
			STATE minimizedStateName = snf.minimize(temp);
			for (STATE c : temp)
				oldSNames2newSNames.put(c, minimizedStateName);
			result.addState(isInitial, isFinal, minimizedStateName);
			marker[i] = true;
		}

		if (getServiceProvider().getProgressMonitorService() != null
				&& !getServiceProvider().getProgressMonitorService().continueProcessing()) {
			m_Logger.debug("Stopped in generateBuchiAutomaton/states added to result BA");
			throw new OperationCanceledException(this.getClass());
		}

		// Add edges
		for (STATE c : m_Buechi.getStates())
			for (LETTER s : m_Buechi.getInternalAlphabet())
				for (STATE succ : m_Buechi.succInternal(c, s)) {
					STATE newPred = oldSNames2newSNames.get(c);
					STATE newSucc = oldSNames2newSNames.get(succ);
					result.addInternalTransition(newPred, s, newSucc);
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
				if (!m_Buechi.isFinal(q1)) {
					v1e = new SpoilerVertex<>(1, true, q0, q1);
					addSpoilerVertex(v1e);
					increaseGlobalInfinity();
				}
			}
			if (getServiceProvider().getProgressMonitorService() != null
					&& !getServiceProvider().getProgressMonitorService().continueProcessing()) {
				m_Logger.debug("Stopped in generateGameGraph/calculating v0 und v1");
				throw new OperationCanceledException(this.getClass());
			}
		}
		// Calculate v0 and edges [paper ref 10, 11, 12]
		for (STATE q0 : m_Buechi.getStates()) {
			for (STATE q1 : m_Buechi.getStates()) {
				for (LETTER s : m_Buechi.lettersInternalIncoming(q0)) {
					if (m_Buechi.predInternal(q0, s).iterator().hasNext()) {
						DuplicatorVertex<LETTER, STATE> v0e = new DuplicatorVertex<>(2, false, q0, q1, s);
						addDuplicatorVertex(v0e);
						// V0 -> V1 edges [paper ref 11]
						for (STATE q2 : m_Buechi.succInternal(q1, s))
							addEdge(v0e, getSpoilerVertex(q0, q2, false));
						// V1 -> V0 edges [paper ref 11]
						for (STATE q2 : m_Buechi.predInternal(q0, s))
							if (!m_Buechi.isFinal(q0))
								addEdge(getSpoilerVertex(q2, q1, false), v0e);
						v0e = new DuplicatorVertex<>(2, true, q0, q1, s);
						addDuplicatorVertex(v0e);
						// V0 -> V1 edges [paper ref 11]
						for (STATE q2 : m_Buechi.succInternal(q1, s)) {
							if (!m_Buechi.isFinal(q2) && getAmountOfBitsForSpoilerVertix(q0, q2) > 1) {
								addEdge(v0e, getSpoilerVertex(q0, q2, true));
							} else {
								addEdge(v0e, getSpoilerVertex(q0, q2, false));
							}
						}
						// V1 -> V0 edges [paper ref 11]
						for (STATE q2 : m_Buechi.predInternal(q0, s)) {
							if (getAmountOfBitsForSpoilerVertix(q2, q1) > 1)
								addEdge(getSpoilerVertex(q2, q1, true), v0e);
							if (m_Buechi.isFinal(q0))
								addEdge(getSpoilerVertex(q2, q1, false), v0e);
						}
					}
				}
			}
			if (getServiceProvider().getProgressMonitorService() != null
					&& !getServiceProvider().getProgressMonitorService().continueProcessing()) {
				m_Logger.debug("Stopped in generateGameGraph/calculating v0 und v1");
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
