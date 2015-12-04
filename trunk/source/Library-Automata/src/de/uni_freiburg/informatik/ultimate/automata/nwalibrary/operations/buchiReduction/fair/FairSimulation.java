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

import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.GameGraphSuccessorProvider;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.DuplicatorVertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.SpoilerVertex;
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

	private final INestedWordAutomatonOldApi<LETTER, STATE> m_Buechi;

	private final FairGameGraph<LETTER, STATE> m_Game;

	private final int m_GlobalInfinity;

	private final boolean m_UseSCCs;

	private ArrayList<Vertex<LETTER, STATE>> m_WorkingList;

	protected final Logger m_Logger;

	protected final IUltimateServiceProvider m_Services;

	protected final StateFactory<STATE> m_StateFactory;

	protected NestedWordAutomaton<LETTER, STATE> m_Result;
	
	private int m_StepCounter;
	
	private SccComputation<Vertex<LETTER, STATE>,
		StronglyConnectedComponent<Vertex<LETTER, STATE>>> m_SccComp;
	
	private DefaultStronglyConnectedComponentFactory<Vertex<LETTER,STATE>> m_SccFactory;
	
	private GameGraphSuccessorProvider<LETTER, STATE> m_SuccProvider;
	
	private HashSet<Vertex<LETTER, STATE>> m_pokedFromNeighborSCC;

	public FairSimulation(IUltimateServiceProvider services, INestedWordAutomatonOldApi<LETTER, STATE> buechi,
			boolean useSCCs, StateFactory<STATE> stateFactory) {
		m_Services = services;
		m_Logger = m_Services.getLoggingService().getLogger(LibraryIdentifiers.s_LibraryID);
		m_StateFactory = stateFactory;
		m_UseSCCs = useSCCs;
		m_Buechi = buechi;
		m_SccComp = null;
		m_SccFactory = null;
		m_SuccProvider = null;
		m_pokedFromNeighborSCC = null;
		m_Game = new FairGameGraph<LETTER, STATE>(services, buechi);
		m_GlobalInfinity = m_Game.getGlobalInfinity();
		
		doSimulation();
	}
	
	protected FairGameGraph<LETTER, STATE> getGameGraph() {
		return m_Game;
	}

	private int calcBestNghbMeasure(Vertex<LETTER, STATE> vertex, int localInfinity, Set<Vertex<LETTER, STATE>> scc) {
		boolean isDuplicatorVertex = vertex.isDuplicatorVertex();

		// If there are no successors the corresponding player looses
		if (!m_Game.hasSuccessors(vertex)) {
			if (isDuplicatorVertex) {
				return m_GlobalInfinity;
			} else {
				return 0;
			}
		}

		int optimum;
		if (isDuplicatorVertex) {
			optimum = m_GlobalInfinity;
		} else {
			optimum = 0;
		}

		// TODO Why no useSCC handling if successor out of scc? -> getPM returns 0 if out of scc
		// TODO Why globalInfinity?
		for (Vertex<LETTER, STATE> succ : m_Game.getSuccessors(vertex)) {
			int progressMeasure = succ.getPM(scc, m_GlobalInfinity);
			if (isDuplicatorVertex) {
				if (progressMeasure < optimum) {
					optimum = progressMeasure;
				}
			} else {
				if (progressMeasure > optimum) {
					optimum = progressMeasure;
				}
			}
		}

		return decreaseVector(vertex.getPriority(), optimum, localInfinity);
	}

	private int calcNghbCounter(Vertex<LETTER, STATE> vertex, int localInfinity, Set<Vertex<LETTER, STATE>> scc) {
		// If there are no successors
		if (!m_Game.hasSuccessors(vertex)) {
			return 0;
		}
		int counter = 0;
		// TODO Why no useSCC handling if successor out of scc? -> getPM returns 0 if out of scc
		// TODO Why globalInfinity?
		for (Vertex<LETTER, STATE> succ : m_Game.getSuccessors(vertex))
			if (decreaseVector(vertex.getPriority(), succ.getPM(scc, m_GlobalInfinity), localInfinity) == vertex.getBEff()) {
				counter++;
			}
		return counter;
	}

	private int calculateInfinityOfSCC(StronglyConnectedComponent<Vertex<LETTER, STATE>> scc) {
		int localInfinity = 0;
		for (Vertex<LETTER, STATE> vertex : scc.getNodes()) {
			if (vertex.getPriority() == 1) {
				localInfinity++;
			}
		}
		localInfinity++;
		return localInfinity;
	}

	private int decreaseVector(int index, int vector, int localInfinity) {
		// TODO Why globalInfinity, for safety?
		if (vector >= localInfinity) {
			return m_GlobalInfinity;
		}
		if (index == 0) {
			return 0;
		} else {
			return vector;
		}
	}

	private void doSimulation() {
		// XXX Remove debugging information
		System.out.println(">Starting minimization, useSCCs: " + m_UseSCCs);
		
		long startTime = System.currentTimeMillis();
		long startTimeSCCCalc = 0;
		long durationSCCCalc = 0;
		
		m_StepCounter = 0;

		if (m_UseSCCs) {
			// XXX Remove debugging information
			System.out.println(">Calculating SCCs...");
			
			startTimeSCCCalc = System.currentTimeMillis();
			m_pokedFromNeighborSCC = new HashSet<Vertex<LETTER, STATE>>();
			m_SccFactory = new DefaultStronglyConnectedComponentFactory<Vertex<LETTER, STATE>>();
			m_SuccProvider = new GameGraphSuccessorProvider<LETTER, STATE>(m_Game);
			m_SccComp = new SccComputation<Vertex<LETTER, STATE>, StronglyConnectedComponent<Vertex<LETTER, STATE>>>(m_Logger, m_SuccProvider,
					m_SccFactory, m_Game.getSize(), m_Game.getVertices());
			durationSCCCalc = System.currentTimeMillis() - startTimeSCCCalc;
			
			// XXX Remove debugging information
			System.out.println("\tAmount of SCCs: " + m_SccComp.getSCCs().size());
			
			Iterator<StronglyConnectedComponent<Vertex<LETTER, STATE>>> iter =
					new LinkedList<StronglyConnectedComponent<Vertex<LETTER, STATE>>>(m_SccComp.getSCCs()).iterator();
			
			// XXX Remove debugging information
			System.out.println(">Starting iterations...");
			
			while(iter.hasNext()) {
				StronglyConnectedComponent<Vertex<LETTER, STATE>> scc =
						iter.next();
				iter.remove();
				
				int infinityOfSCC = calculateInfinityOfSCC(scc);
				
				// XXX Remove debugging information
				System.out.println("Using SCC: " + sccToString(scc));
				System.out.println("\tLocal infinity: " + infinityOfSCC);
				
				efficientLiftingAlgorithm(infinityOfSCC, scc.getNodes());
			}
		} else {
			// XXX Remove debugging information
			System.out.println(">Starting iterations...");
			
			efficientLiftingAlgorithm(m_GlobalInfinity, null);
		}
		// TODO Assign the reduced buechi
		m_Result = m_Game.generateBuchiAutomatonFromGraph();

		long duration = System.currentTimeMillis() - startTime;
		m_Logger.info((m_UseSCCs ? "SCC version" : "nonSCC version") + " took " + duration + " milliseconds.");
		
		// XXX Remove debugging information
		System.out.println(">Simulation took " + m_StepCounter + " steps and " + duration + "ms.");
		if (m_UseSCCs) {
			System.out.println(">Calculating SCCs took " + durationSCCCalc + "ms.");
		}
		System.out.println(">Ending minimization.");
	}

	private void efficientLiftingAlgorithm(int localInfinity, Set<Vertex<LETTER, STATE>> scc) {
		initSimulation(false, localInfinity, scc);
		
		// XXX Remove debugging information
		printWorkingList();
		
		while (!m_WorkingList.isEmpty()) {
			m_StepCounter++;
			
			Random rnd = new Random();
			Vertex<LETTER, STATE> workingVertex = m_WorkingList.get(rnd.nextInt(m_WorkingList.size()));
			removeVertexFromWorkingList(workingVertex);
			
			// XXX Remove debugging information
			System.out.println("\tWorkingVertex: " + workingVertex);
			
			Set<Vertex<LETTER, STATE>> usedSCCForNeighborCalculation = scc;
			if (m_UseSCCs && m_pokedFromNeighborSCC.contains(workingVertex)) {
				usedSCCForNeighborCalculation = null;
				
				// XXX Remove debugging information
				System.out.println("\t\tWorkingVertex is poked vertex: " + workingVertex);
			}

			// TODO Why globalInfinity?
			int tempProgressMeasure = workingVertex.getPM(scc, m_GlobalInfinity);

			// XXX Remove debugging information
			System.out.print("\t\tBNM: " + workingVertex.getBEff());
			
			workingVertex.setBEff(calcBestNghbMeasure(workingVertex, localInfinity, usedSCCForNeighborCalculation));
			
			// XXX Remove debugging information
			System.out.println(" -> " + workingVertex.getBEff());
			System.out.print("\t\tNC: " + workingVertex.getC());
			
			workingVertex.setC(calcNghbCounter(workingVertex, localInfinity, usedSCCForNeighborCalculation));
			
			// XXX Remove debugging information
			System.out.println(" -> " + workingVertex.getC());
			System.out.print("\t\tPM: " + tempProgressMeasure);
			
			int currentProgressMeasure = increaseVector(workingVertex.getPriority(),
					workingVertex.getBEff(), localInfinity);
			workingVertex.setPM(currentProgressMeasure);
			
			// XXX Remove debugging information
			System.out.println(" -> " + currentProgressMeasure);

			Set<Vertex<LETTER, STATE>> predVertices = m_Game.getPredecessors(workingVertex);
			if (predVertices == null || predVertices.isEmpty()) {
				continue;
			}
			
			// XXX Remove debugging information
			System.out.println("\t\tWorking predecessors:");
			
			for (Vertex<LETTER, STATE> pred : predVertices) {
				if (pred.isInWL()) {
					continue;
				}
				// If vertex has reached localInfinity and predecessor,
				// which is a 1-distance neighbor of SCC, is interested
				boolean pokePossible = false;
				if (m_UseSCCs && !scc.contains(pred)) {
					pokePossible = currentProgressMeasure >= localInfinity
							&& !m_pokedFromNeighborSCC.contains(pred);
					if (!pokePossible) {
						continue;
					}
				}

				// TODO Why globalInfinity?
				if (decreaseVector(pred.getPriority(), workingVertex.getPM(scc, m_GlobalInfinity),
						localInfinity) > pred.getBEff()) {

					if (pred.isDuplicatorVertex() && (decreaseVector(pred.getPriority(),
							tempProgressMeasure, localInfinity) == pred.getBEff()
							|| (pokePossible && pred.getBEff() == 0))) {
						
						// If trying to use a vertex outside of the SCC make sure
						// the neighbor counter was initialized before accessing it
						if (pokePossible) {
							if (pred.getC() == 0) {
								// XXX Remove debugging information
								System.out.println("\t\t\tInit C for pokePossible predecessor: " + pred);
								System.out.print("\t\t\t\tC: " + pred.getC());
								
								pred.setC(m_Game.getSuccessors(pred).size());
								
								// XXX Remove debugging information
								System.out.println(" -> " + pred.getC());
							} else {
								// XXX Remove debugging information
								System.out.println("\t\t\tPokePossible predecessor was already initialized: " + pred);
							}
						}
						
						if (pred.getC() == 1) {
							if (pokePossible) {
								// XXX Remove debugging information
								System.out.println("\t\t\tOnly one good neighbor, poking: " + pred);
								
								m_pokedFromNeighborSCC.add(pred);
							} else {
								// XXX Remove debugging information
								System.out.println("\t\t\tOnly one good neighbor, adding to wL: " + pred);
								
								addVertexToWorkingList(pred);
							}
						} else if (pred.getC() > 1) {
							// XXX Remove debugging information
							System.out.println("\t\t\tMore good neighbors, decreasing C: " + pred);
							
							pred.setC(pred.getC() - 1);
						}
					} else if (pred.isSpoilerVertex()) {
						if (pokePossible) {
							// XXX Remove debugging information
							System.out.println("\t\t\tIs spoiler vertex, poking: " + pred);
							
							m_pokedFromNeighborSCC.add(pred);
						} else {
							// XXX Remove debugging information
							System.out.println("\t\t\tIs spoiler vertex, adding to wL: " + pred);
							
							addVertexToWorkingList(pred);
						}
					}
				}
			}
			
			if (m_UseSCCs && m_pokedFromNeighborSCC.contains(workingVertex)) {
				m_pokedFromNeighborSCC.remove(workingVertex);
			}
		}
	}

	private int increaseVector(int index, int vector, int localInfinity) {
		if (vector >= localInfinity) {
			return m_GlobalInfinity;
		}
		if (index == 1) {
			vector++;
			if (vector == localInfinity) {
				return m_GlobalInfinity;
			}
			return vector;
		} else {
			return decreaseVector(index, vector, localInfinity);
		}
	}
	
	private void addVertexToWorkingList(Vertex<LETTER, STATE> vertex) {
		m_WorkingList.add(vertex);
		vertex.setInWL(true);
	}
	
	private void removeVertexFromWorkingList(Vertex<LETTER, STATE> vertex) {
		m_WorkingList.remove(vertex);
		vertex.setInWL(false);
	}

	private void initSimulation(boolean reuseResults, int localInfinity, Set<Vertex<LETTER, STATE>> scc) {
		// XXX Remove debugging information
		System.out.println("\tInit:");
				
		m_WorkingList = new ArrayList<Vertex<LETTER, STATE>>();
		if (m_UseSCCs) {
			for (Vertex<LETTER, STATE> vertex : scc) {
				initWorkingListAndCWithVertex(vertex, localInfinity, scc);
			}
		} else {
			for (SpoilerVertex<LETTER, STATE> spoilerVertex : m_Game.getSpoilerVertices()) {
				initWorkingListAndCWithVertex(spoilerVertex, localInfinity, scc);
			}
			for (DuplicatorVertex<LETTER, STATE> duplicatorVertex : m_Game.getDuplicatorVertices()) {
				initWorkingListAndCWithVertex(duplicatorVertex, localInfinity, scc);
			}
		}
	}

	private void initWorkingListAndCWithVertex(Vertex<LETTER, STATE> vertex, int localInfinity,
			Set<Vertex<LETTER, STATE>> scc) {
		// TODO Implement priority queue where big PM comes before small PM and
		// dead end comes before everything
		if (!m_Game.hasSuccessors(vertex) || vertex.getPriority() == 1
				|| (m_UseSCCs && m_pokedFromNeighborSCC.contains(vertex))) {
			addVertexToWorkingList(vertex);
			
			// XXX Remove debugging information
			if (!m_Game.hasSuccessors(vertex)) {
				System.out.println("\t\tIs dead-end, adding to wL: " + vertex);
			} else if (m_UseSCCs && m_pokedFromNeighborSCC.contains(vertex)) {
				System.out.println("\t\tWas poked, adding to wL: " + vertex);
			}
			
		}
		if (m_UseSCCs) {
			Set<Vertex<LETTER, STATE>> usedSCCForNeighborCalculation = scc;
			if (m_pokedFromNeighborSCC.contains(vertex)) {
				usedSCCForNeighborCalculation = null;
			}
			vertex.setC(calcNghbCounter(vertex, localInfinity, usedSCCForNeighborCalculation));
		} else if (m_Game.hasSuccessors(vertex)) {
			vertex.setC(m_Game.getSuccessors(vertex).size());
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
		result.append(lineSeparator + "\tglobalInfinity = " + m_GlobalInfinity);
		result.append(lineSeparator + "\tstepCounter = " + m_StepCounter);
		result.append(lineSeparator + "\tbuechi size before = " + m_Buechi.size() + " states");
		result.append(lineSeparator + "\tbuechi size after = " + this.m_Result.size() + " states");
		
		// Progress Measure
		result.append(lineSeparator + "\tprogress measure = {");
		for (SpoilerVertex<LETTER, STATE> vertex : m_Game.getSpoilerVertices()) {
			int localInfinity = m_GlobalInfinity;
			if (m_UseSCCs) {
				for (StronglyConnectedComponent<Vertex<LETTER, STATE>> scc : m_SccComp.getSCCs()) {
					if (scc.getNodes().contains(vertex)) {
						localInfinity = calculateInfinityOfSCC(scc);
					}
				}
			}
			result.append(lineSeparator + "\t\t<(" + vertex.getQ0()
				+ ", " + vertex.getQ1() + "), pm:" + vertex.getPM(null, m_GlobalInfinity)
				+ " of " + localInfinity + ">");
		}
		for (DuplicatorVertex<LETTER, STATE> vertex : m_Game.getDuplicatorVertices()) {
			int localInfinity = m_GlobalInfinity;
			if (m_UseSCCs) {
				for (StronglyConnectedComponent<Vertex<LETTER, STATE>> scc : m_SccComp.getSCCs()) {
					if (scc.getNodes().contains(vertex)) {
						localInfinity = calculateInfinityOfSCC(scc);
					}
				}
			}
			result.append(lineSeparator + "\t\t<(" + vertex.getQ0()
				+ ", " + vertex.getQ1() + ", " + vertex.getLetter()
				+ "), pm:" + vertex.getPM(null, m_GlobalInfinity) + " of "
				+ localInfinity + ">");
		}
		result.append(lineSeparator + "\t},");
		
		// Best Neighbor Measure
		result.append(lineSeparator + "\tbest neighbor measure = {");
		for (SpoilerVertex<LETTER, STATE> vertex : m_Game.getSpoilerVertices()) {
			result.append(lineSeparator + "\t\t<(" + vertex.getQ0()
				+ ", " + vertex.getQ1() + "), bnm:" + vertex.getBEff() + ">");
		}
		for (DuplicatorVertex<LETTER, STATE> vertex : m_Game.getDuplicatorVertices()) {
			result.append(lineSeparator + "\t\t<(" + vertex.getQ0()
				+ ", " + vertex.getQ1() + ", " + vertex.getLetter()
				+ "), bnm:" + vertex.getBEff() + ">");
		}
		result.append(lineSeparator + "\t},");
		
		// Neighbor counter
		result.append(lineSeparator + "\tneighbor counter = {");
		for (SpoilerVertex<LETTER, STATE> vertex : m_Game.getSpoilerVertices()) {
			result.append(lineSeparator + "\t\t<(" + vertex.getQ0()
				+ ", " + vertex.getQ1() + "), nc:" + vertex.getC() + ">");
		}
		for (DuplicatorVertex<LETTER, STATE> vertex : m_Game.getDuplicatorVertices()) {
			result.append(lineSeparator + "\t\t<(" + vertex.getQ0()
				+ ", " + vertex.getQ1() + ", " + vertex.getLetter()
				+ "), nc:" + vertex.getC() + ">");
		}
		result.append(lineSeparator + "\t},");
		
		// Footer
		result.append(lineSeparator + ");");
		
		return result.toString();
	}
	
	private void printWorkingList() {
		StringBuilder result = new StringBuilder();
		String lineSeparator = System.lineSeparator();
		// Inline
		if (m_WorkingList.size() <= 1) {
			lineSeparator = "";
		}
		
		// Header
		result.append("\twL = (");
		Iterator<Vertex<LETTER, STATE>> iter = m_WorkingList.iterator();
		while (iter.hasNext()) {
			result.append(lineSeparator + "\t\t" + iter.next());
		}
		// Footer
		result.append(lineSeparator + "\t);");
		
		System.out.println(result);
	}
	
	private String sccToString(StronglyConnectedComponent<Vertex<LETTER, STATE>> scc) {
		StringBuilder result = new StringBuilder();
		
		result.append("{");
		for (Vertex<LETTER, STATE> vertex : scc.getNodes()) {
			result.append("(" + vertex.getQ0()
				+ ", " + vertex.getQ1());
			if (vertex instanceof DuplicatorVertex) {
				DuplicatorVertex<LETTER, STATE> vertexAsDuplicatorVertex = (DuplicatorVertex<LETTER, STATE>) vertex;
				result.append(", " + vertexAsDuplicatorVertex.getLetter());
			}
			result.append("), ");
		}
		result.append("}");
		
		return result.toString();
	}
}