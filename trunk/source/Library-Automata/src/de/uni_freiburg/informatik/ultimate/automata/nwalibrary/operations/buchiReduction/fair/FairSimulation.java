/*
 * Copyright (C) 2015-2016 Daniel Tischner
 * Copyright (C) 2009-2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.fair;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Random;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.Player0Vertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.Player1Vertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.Vertex;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.util.scc.DefaultStronglyConnectedComponentFactory;
import de.uni_freiburg.informatik.ultimate.util.scc.SccComputation;
import de.uni_freiburg.informatik.ultimate.util.scc.StronglyConnectedComponent;

/**
 * Doc comes later.
 * 
 * @author Daniel Tischner
 * @param <LETTER>
 * @param <STATE>
 *
 */
public final class FairSimulation<LETTER, STATE> {

	private INestedWordAutomatonOldApi<LETTER, STATE> m_Buechi;

	private final FairGameGraph<LETTER, STATE> m_Game;

	private int globalInfinity;

	private boolean m_UseSCCs;

	private ArrayList<Vertex<LETTER, STATE>> workingList;

	protected final Logger m_Logger;

	protected final IUltimateServiceProvider m_Services;

	protected final StateFactory<STATE> m_StateFactory;

	protected NestedWordAutomaton<LETTER, STATE> result;
	
	private int stepCounter;
	
	private SccComputation<Vertex<LETTER, STATE>,
		StronglyConnectedComponent<Vertex<LETTER, STATE>>> m_SccComp;
	
	private DefaultStronglyConnectedComponentFactory<Vertex<LETTER,STATE>> m_SccFactory;
	
	private GameGraphSuccessorProvider<LETTER, STATE> m_SuccessorProvider;
	
	private HashSet<Vertex<LETTER, STATE>> m_pokedFromNeighborSCC;

	public FairSimulation(IUltimateServiceProvider services, INestedWordAutomatonOldApi<LETTER, STATE> buechi,
			boolean useSCCs, StateFactory<STATE> stateFactory) throws AutomataLibraryException {
		m_Services = services;
		m_Logger = m_Services.getLoggingService().getLogger(LibraryIdentifiers.s_LibraryID);
		m_StateFactory = stateFactory;
		m_UseSCCs = useSCCs;
		m_Buechi = buechi;
		m_SccComp = null;
		m_SccFactory = null;
		m_SuccessorProvider = null;
		m_pokedFromNeighborSCC = null;
		m_Game = new FairGameGraph<>(services, buechi);
		
		doSimulation();
	}
	
	protected FairGameGraph<LETTER, STATE> getGameGraph() {
		return m_Game;
	}

	private int calcBestNghbMeasure(Vertex<LETTER, STATE> state, int localInfinity, Set<Vertex<LETTER, STATE>> scc) {
		boolean isVZeroNode = state.isInV0();

		// If there are no successors the corresponding player looses
		if (!m_Game.hasSuccessors(state)) {
			if (isVZeroNode) {
				return globalInfinity;
			} else {
				return 0;
			}
		}

		int optimum;
		if (isVZeroNode) {
			optimum = globalInfinity;
		} else {
			optimum = 0;
		}

		// TODO Why no useSCC handling if successor out of scc? -> getPM returns 0 if out of scc
		// TODO Why globalInfinity?
		for (Vertex<LETTER, STATE> successor : m_Game.getSuccessors(state)) {
			int progressMeasure = successor.getPM(scc, globalInfinity);
			if (isVZeroNode) {
				if (progressMeasure < optimum) {
					optimum = progressMeasure;
				}
			} else {
				if (progressMeasure > optimum) {
					optimum = progressMeasure;
				}
			}
		}

		return decreaseVector(state.getPriority(), optimum, localInfinity);
	}

	private int calcNghbCounter(Vertex<LETTER, STATE> state, int l_inf, Set<Vertex<LETTER, STATE>> scc) {
		// If there are no successors
		if (!m_Game.hasSuccessors(state)) {
			return 0;
		}
		int counter = 0;
		// TODO Why no useSCC handling if successor out of scc? -> getPM returns 0 if out of scc
		// TODO Why globalInfinity?
		for (Vertex<LETTER, STATE> successor : m_Game.getSuccessors(state))
			if (decreaseVector(state.getPriority(), successor.getPM(scc, globalInfinity), l_inf) == state.getBEff()) {
				counter++;
			}
		return counter;
	}

	private int calculateInfinityOfSCC(StronglyConnectedComponent<Vertex<LETTER, STATE>> scc) {
		int localInfinity = 0;
		for (Vertex<LETTER, STATE> state : scc.getNodes()) {
			if (state.getPriority() == (byte) 1) {
				localInfinity++;
			}
		}
		localInfinity++;
		return localInfinity;
	}

	private int decreaseVector(byte index, int vector, int localInfinity) {
		// TODO Why globalInfinity, for safety?
		if (vector >= localInfinity) {
			return globalInfinity;
		}
		if (index == (byte) 0) {
			return 0;
		} else {
			return vector;
		}
	}

	private void doSimulation() throws AutomataLibraryException {
		long startTime = System.currentTimeMillis();
		long startTimeSCCCalc = 0;
		long durationSCCCalc = 0;

		globalInfinity = m_Game.getGlobalInfinity();
		stepCounter = 0;

		if (m_UseSCCs) {
			startTimeSCCCalc = System.currentTimeMillis();
			m_pokedFromNeighborSCC = new HashSet<>();
			m_SccFactory = new DefaultStronglyConnectedComponentFactory<>();
			m_SuccessorProvider = new GameGraphSuccessorProvider<>(m_Game);
			m_SccComp = new SccComputation<>(m_Logger, m_SuccessorProvider,
					m_SccFactory, m_Game.getSize(), m_Game.getNodes());
			durationSCCCalc = System.currentTimeMillis() - startTimeSCCCalc;
			
			System.out.println("Amount of SCCs: " + m_SccComp.getSCCs().size());
			
			Iterator<StronglyConnectedComponent<Vertex<LETTER, STATE>>> iter =
					new LinkedList<>(m_SccComp.getSCCs()).iterator();
			while(iter.hasNext()) {
				StronglyConnectedComponent<Vertex<LETTER, STATE>> scc =
						iter.next();
				iter.remove();
				
				efficientLiftingAlgorithm(
						calculateInfinityOfSCC(scc), scc.getNodes());
			}
		} else {
			efficientLiftingAlgorithm(globalInfinity, null);
		}
		// TODO Assign the reduced buechi
		result = m_Game.generateBuchiAutomatonFromGraph();

		long duration = System.currentTimeMillis() - startTime;
		m_Logger.info((m_UseSCCs ? "SCC version" : "nonSCC version") + " took " + duration + " milliseconds.");
		
		// XXX Remove debugging information
		System.out.println("Simulation took " + stepCounter + " steps and " + duration + "ms.");
		if (m_UseSCCs) {
			System.out.println("Calculating SCCs took " + durationSCCCalc + "ms.");
		}
	}

	private void efficientLiftingAlgorithm(int localInfinity, Set<Vertex<LETTER, STATE>> scc)
			throws AutomataLibraryException {
		initSimulation(false, localInfinity, scc);
		
		// XXX Remove debugging information
		if (!workingList.isEmpty()) {
			printWorkingList();
		}
		
		while (!workingList.isEmpty()) {
			stepCounter++;
			
			Random rnd = new Random();
			Vertex<LETTER, STATE> workingState = workingList.get(rnd.nextInt(workingList.size()));
			removeStateFromWorkingList(workingState);
			
			Set<Vertex<LETTER, STATE>> usedSCCForNeighborCalculation = scc;
			if (m_UseSCCs && m_pokedFromNeighborSCC.contains(workingState)) {
				usedSCCForNeighborCalculation = null;
				
				// XXX Remove debugging information
				System.out.println("Poking state " + workingState);
			}

			// TODO Why globalInfinity?
			int tempProgressMeasure = workingState.getPM(scc, globalInfinity);

			workingState.setBEff(calcBestNghbMeasure(workingState, localInfinity, usedSCCForNeighborCalculation));
			workingState.setC(calcNghbCounter(workingState, localInfinity, usedSCCForNeighborCalculation));
			int currentProgressMeasure = increaseVector(workingState.getPriority(),
					workingState.getBEff(), localInfinity);
			workingState.setPM(currentProgressMeasure);

			HashSet<Vertex<LETTER, STATE>> predNodes = m_Game.getPredecessors(workingState);
			if (predNodes == null || predNodes.isEmpty()) {
				continue;
			}
			for (Vertex<LETTER, STATE> predecessor : predNodes) {
				if (predecessor.isInWL()) {
					continue;
				}
				// If state has reached localInfinity and predecessor,
				// which is a 1-distance neighbor of SCC, is interested
				boolean pokePossible = false;
				if (m_UseSCCs && !scc.contains(predecessor)) {
					pokePossible = currentProgressMeasure >= localInfinity
							&& !m_pokedFromNeighborSCC.contains(predecessor);
					
					if (!pokePossible) {
						continue;
					}
				}

				// TODO Why globalInfinity?
				if (decreaseVector(predecessor.getPriority(), workingState.getPM(scc, globalInfinity),
						localInfinity) > predecessor.getBEff()) {

					if (predecessor.isInV0() && decreaseVector(predecessor.getPriority(),
							tempProgressMeasure, localInfinity) == predecessor.getBEff()) {
						
						// If trying to use a state outside of the SCC make sure
						// to initialize the neighbor counter before accessing it
						if (pokePossible) {
							predecessor.setC(m_Game.getSuccessors(predecessor).size());
						}
						
						if (predecessor.getC() == 1) {
							if (pokePossible) {
								m_pokedFromNeighborSCC.add(predecessor);
								System.err.println("Case: V_0 and C == 1");
							} else {
								addStateToWorkingList(predecessor);
							}
						} else if (predecessor.getC() > 1) {
							predecessor.setC(predecessor.getC() - 1);
						}
					} else if (predecessor.isInV1()) {
						if (pokePossible) {
							m_pokedFromNeighborSCC.add(predecessor);
							System.err.println("Case: V_1");
						} else {
							addStateToWorkingList(predecessor);
						}
					}
				}
			}
			
			if (m_UseSCCs && m_pokedFromNeighborSCC.contains(workingState)) {
				m_pokedFromNeighborSCC.remove(workingState);
			}
		}
	}

	private int increaseVector(byte index, int vector, int localInfinity) {
		// TODO Why globalInfinity, for safety?
		if (vector >= localInfinity) {
			return globalInfinity;
		}
		if (index == (byte) 1) {
			vector++;
			return vector;
		} else {
			return decreaseVector(index, vector, localInfinity);
		}
	}
	
	private void addStateToWorkingList(Vertex<LETTER, STATE> state) {
		workingList.add(state);
		state.setInWL(true);
	}
	
	private void removeStateFromWorkingList(Vertex<LETTER, STATE> state) {
		workingList.remove(state);
		state.setInWL(false);
	}

	private void initSimulation(boolean reuseResults, int localInfinity, Set<Vertex<LETTER, STATE>> scc) {
		workingList = new ArrayList<>();
		if (m_UseSCCs) {
			for (Vertex<LETTER, STATE> state : scc) {
				initWorkingListAndCWithState(state, localInfinity, scc);
			}
		} else {
			for (Player1Vertex<LETTER, STATE> vOneState : m_Game.getPlayer1States()) {
				initWorkingListAndCWithState(vOneState, localInfinity, scc);
			}
			for (Player0Vertex<LETTER, STATE> vZeroState : m_Game.getPlayer0States()) {
				initWorkingListAndCWithState(vZeroState, localInfinity, scc);
			}
		}
	}

	private void initWorkingListAndCWithState(Vertex<LETTER, STATE> state, int localInfinity,
			Set<Vertex<LETTER, STATE>> scc) {
		// TODO Implement priority queue where big PM comes before small PM and
		// dead end comes before everything
		if (!m_Game.hasSuccessors(state) || state.getPriority() == (byte) 1
				|| (m_UseSCCs && m_pokedFromNeighborSCC.contains(state))) {
			addStateToWorkingList(state);
		}
		if (m_UseSCCs) {
			Set<Vertex<LETTER, STATE>> usedSCCForNeighborCalculation = scc;
			if (m_pokedFromNeighborSCC.contains(state)) {
				usedSCCForNeighborCalculation = null;
			}
			state.setC(calcNghbCounter(state, localInfinity, usedSCCForNeighborCalculation));
		} else if (m_Game.hasSuccessors(state)) {
			state.setC(m_Game.getSuccessors(state).size());
		}
	}
	
	@Override
	public String toString() {
		StringBuilder result = new StringBuilder();
		String lineSeparator = System.lineSeparator();
		// Header
		result.append("FairSimulationResults fsr = (");
		
		// Properties
		result.append(lineSeparator + "\tuseSCCs = " + m_UseSCCs);
		result.append(lineSeparator + "\tglobalInfinity = " + globalInfinity);
		result.append(lineSeparator + "\tstepCounter = " + stepCounter);
		result.append(lineSeparator + "\tbuechi size before = " + m_Buechi.size() + " states");
		result.append(lineSeparator + "\tbuechi size after = " + this.result.size() + " states");
		
		// Progress Measure
		result.append(lineSeparator + "\tprogress measure = {");
		for (Player1Vertex<LETTER, STATE> state : m_Game.getPlayer1States()) {
			int localInfinity = globalInfinity;
			if (m_UseSCCs) {
				for (StronglyConnectedComponent<Vertex<LETTER, STATE>> scc : m_SccComp.getSCCs()) {
					if (scc.getNodes().contains(state)) {
						localInfinity = calculateInfinityOfSCC(scc);
					}
				}
			}
			result.append(lineSeparator + "\t\t<(" + state.getQ0()
				+ ", " + state.getQ1() + "), pm:" + state.getPM(null, globalInfinity)
				+ " of " + localInfinity + ">");
		}
		for (Player0Vertex<LETTER, STATE> state : m_Game.getPlayer0States()) {
			int localInfinity = globalInfinity;
			if (m_UseSCCs) {
				for (StronglyConnectedComponent<Vertex<LETTER, STATE>> scc : m_SccComp.getSCCs()) {
					if (scc.getNodes().contains(state)) {
						localInfinity = calculateInfinityOfSCC(scc);
					}
				}
			}
			result.append(lineSeparator + "\t\t<(" + state.getQ0()
				+ ", " + state.getQ1() + ", " + state.getLetter()
				+ "), pm:" + state.getPM(null, globalInfinity) + " of "
				+ localInfinity + ">");
		}
		result.append(lineSeparator + "\t},");
		
		// Best Neighbor Measure
		result.append(lineSeparator + "\tbest neighbor measure = {");
		for (Player1Vertex<LETTER, STATE> state : m_Game.getPlayer1States()) {
			result.append(lineSeparator + "\t\t<(" + state.getQ0()
				+ ", " + state.getQ1() + "), bnm:" + state.getBEff() + ">");
		}
		for (Player0Vertex<LETTER, STATE> state : m_Game.getPlayer0States()) {
			result.append(lineSeparator + "\t\t<(" + state.getQ0()
				+ ", " + state.getQ1() + ", " + state.getLetter()
				+ "), bnm:" + state.getBEff() + ">");
		}
		result.append(lineSeparator + "\t},");
		
		// Neighbor counter
		result.append(lineSeparator + "\tneighbor counter = {");
		for (Player1Vertex<LETTER, STATE> state : m_Game.getPlayer1States()) {
			result.append(lineSeparator + "\t\t<(" + state.getQ0()
				+ ", " + state.getQ1() + "), nc:" + state.getC() + ">");
		}
		for (Player0Vertex<LETTER, STATE> state : m_Game.getPlayer0States()) {
			result.append(lineSeparator + "\t\t<(" + state.getQ0()
				+ ", " + state.getQ1() + ", " + state.getLetter()
				+ "), nc:" + state.getC() + ">");
		}
		result.append(lineSeparator + "\t},");
		
		// Footer
		result.append(lineSeparator + ");");
		
		return result.toString();
	}
	
	private void printWorkingList() {
		StringBuilder result = new StringBuilder();
		String lineSeparator = System.lineSeparator();
		// Header
		result.append("wL = (");
		Iterator<Vertex<LETTER, STATE>> iter = workingList.iterator();
		while (iter.hasNext()) {
			Vertex<LETTER, STATE> state = iter.next();
				result.append(lineSeparator + "\t(" + state.getQ0()
			+ ", " + state.getQ1());
			if (state instanceof Player0Vertex) {
				Player0Vertex<LETTER, STATE> stateAsPlayer0 = (Player0Vertex<LETTER, STATE>) state;
				result.append(", " + stateAsPlayer0.getLetter());
			}
			result.append(")");
		}
		// Footer
		result.append(lineSeparator + ");");
		
		System.out.println(result);
	}
}