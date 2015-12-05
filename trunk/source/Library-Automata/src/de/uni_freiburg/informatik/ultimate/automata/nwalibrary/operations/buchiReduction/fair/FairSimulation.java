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

import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.AGameGraph;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.ASimulation;
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
 * 
 * @param <LETTER>
 * @param <STATE>
 *
 */
public final class FairSimulation<LETTER, STATE> extends ASimulation<LETTER, STATE> {

	private final INestedWordAutomatonOldApi<LETTER, STATE> m_Buechi;

	private final FairGameGraph<LETTER, STATE> m_Game;

	private final int m_GlobalInfinity;
	
	private HashSet<Vertex<LETTER, STATE>> m_pokedFromNeighborSCC;
	
	private int m_StepCounter;
	
	// XXX Remove debugging field
	private boolean useDebugPrints = false;
	
	// XXX Remove debugging field
	private boolean useDeepDebugPrints = false;

	public FairSimulation(final IUltimateServiceProvider services,
			final INestedWordAutomatonOldApi<LETTER, STATE> buechi,
			final boolean useSCCs, final StateFactory<STATE> stateFactory)
					throws OperationCanceledException {
		super(services, useSCCs, stateFactory);
		
		m_Buechi = buechi;
		m_pokedFromNeighborSCC = null;
		
		// XXX Remove debugging information
		if (useDeepDebugPrints) System.out.println("Start constructing game graph...");
		
		m_Game = new FairGameGraph<LETTER, STATE>(services, buechi);
		
		// XXX Remove debugging information
		if (useDeepDebugPrints) System.out.println("End constructing game graph.");
		
		m_GlobalInfinity = m_Game.getGlobalInfinity();
		
		doSimulation();
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
	
	private void addVertexToWorkingList(final Vertex<LETTER, STATE> vertex) {
		m_WorkingList.add(vertex);
		vertex.setInWL(true);
	}
	
	private void initSimulation(final boolean reuseResults,
			final int localInfinity, final Set<Vertex<LETTER, STATE>> scc) {
		// XXX Remove debugging information
		if (useDeepDebugPrints) System.out.println("\tInit:");
				
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
	
	private void initWorkingListAndCWithVertex(final Vertex<LETTER, STATE> vertex,
			final int localInfinity, final Set<Vertex<LETTER, STATE>> scc) {
		// TODO Implement priority queue where big PM comes before small PM and
		// dead end comes before everything
		if (!m_Game.hasSuccessors(vertex) || vertex.getPriority() == 1
				|| (m_UseSCCs && m_pokedFromNeighborSCC.contains(vertex))) {
			addVertexToWorkingList(vertex);
			
			// XXX Remove debugging information
			if (!m_Game.hasSuccessors(vertex)) {
				if (useDeepDebugPrints) System.out.println("\t\tIs dead-end, adding to wL: " + vertex);
			} else if (m_UseSCCs && m_pokedFromNeighborSCC.contains(vertex)) {
				if (useDeepDebugPrints) System.out.println("\t\tWas poked, adding to wL: " + vertex);
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
		
		if (useDeepDebugPrints) System.out.println(result);
	}

	private void removeVertexFromWorkingList(final Vertex<LETTER, STATE> vertex) {
		m_WorkingList.remove(vertex);
		vertex.setInWL(false);
	}
	
	private String sccToString(final StronglyConnectedComponent<Vertex<LETTER, STATE>> scc) {
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
	
	@Override
	protected void clear() {
		super.clear();
		m_pokedFromNeighborSCC.clear();
	}
	
	@Override
	protected void doSimulation() {
		// XXX Remove debugging information
		if (useDebugPrints) System.out.println(">Starting minimization, useSCCs: " + m_UseSCCs);
		
		long startTime = System.currentTimeMillis();
		long startTimeSCCCalc = 0;
		long durationSCCCalc = 0;
		
		m_StepCounter = 0;
		int stepsWorked = 0;

		if (m_UseSCCs) {
			// XXX Remove debugging information
			if (useDebugPrints) System.out.println(">Calculating SCCs...");
			
			startTimeSCCCalc = System.currentTimeMillis();
			m_pokedFromNeighborSCC = new HashSet<Vertex<LETTER, STATE>>();
			m_SccFactory = new DefaultStronglyConnectedComponentFactory<Vertex<LETTER, STATE>>();
			m_SuccProvider = new GameGraphSuccessorProvider<LETTER, STATE>(m_Game);
			m_SccComp = new SccComputation<Vertex<LETTER, STATE>, StronglyConnectedComponent<Vertex<LETTER, STATE>>>(m_Logger, m_SuccProvider,
					m_SccFactory, m_Game.getSize(), m_Game.getVertices());
			durationSCCCalc = System.currentTimeMillis() - startTimeSCCCalc;
			
			// XXX Remove debugging information
			if (useDebugPrints) System.out.println("\tAmount of SCCs: " + m_SccComp.getSCCs().size());
			
			Iterator<StronglyConnectedComponent<Vertex<LETTER, STATE>>> iter =
					new LinkedList<StronglyConnectedComponent<Vertex<LETTER, STATE>>>(m_SccComp.getSCCs()).iterator();
			
			// XXX Remove debugging information
			if (useDebugPrints) System.out.println(">Starting iterations...");
			
			while(iter.hasNext()) {
				// XXX Remove debugging information
				stepsWorked++;
				
				StronglyConnectedComponent<Vertex<LETTER, STATE>> scc =
						iter.next();
				iter.remove();
				
				int infinityOfSCC = calculateInfinityOfSCC(scc);
				
				// XXX Remove debugging information
				if (useDeepDebugPrints) System.out.println("Using SCC: " + sccToString(scc));
				if (useDeepDebugPrints) System.out.println("\tLocal infinity: " + infinityOfSCC);
				if (stepsWorked % 10_000 == 0) {
					if (useDebugPrints) System.out.println("Worked " + stepsWorked + " SCCs of " + m_SccComp.getSCCs().size());
				}
				
				efficientLiftingAlgorithm(infinityOfSCC, scc.getNodes());
			}
		} else {
			// XXX Remove debugging information
			if (useDebugPrints) System.out.println(">Starting iterations...");
			
			efficientLiftingAlgorithm(m_GlobalInfinity, null);
		}
		// TODO Assign the reduced buechi
		m_Result = m_Game.generateBuchiAutomatonFromGraph();

		long duration = System.currentTimeMillis() - startTime;
		m_Logger.info((m_UseSCCs ? "SCC version" : "nonSCC version") + " took " + duration + " milliseconds.");
		
		// XXX Remove debugging information
		if (useDebugPrints) System.out.println(">Simulation took " + m_StepCounter + " steps and " + duration + "ms.");
		if (m_UseSCCs) {
			if (useDebugPrints) System.out.println(">Calculating SCCs took " + durationSCCCalc + "ms.");
		}
		if (useDebugPrints) System.out.println(">Ending minimization.");
	}
	
	@Override
	protected void efficientLiftingAlgorithm(final int localInfinity,
			final Set<Vertex<LETTER, STATE>> scc) {
		initSimulation(false, localInfinity, scc);
		
		// XXX Remove debugging information
		printWorkingList();
		
		while (!m_WorkingList.isEmpty()) {
			m_StepCounter++;
			
			Random rnd = new Random();
			Vertex<LETTER, STATE> workingVertex = m_WorkingList.get(rnd.nextInt(m_WorkingList.size()));
			removeVertexFromWorkingList(workingVertex);
			
			// XXX Remove debugging information
			if (useDeepDebugPrints) System.out.println("\tWorkingVertex: " + workingVertex);
			
			Set<Vertex<LETTER, STATE>> usedSCCForNeighborCalculation = scc;
			if (m_UseSCCs && m_pokedFromNeighborSCC.contains(workingVertex)) {
				usedSCCForNeighborCalculation = null;
				
				// XXX Remove debugging information
				if (useDeepDebugPrints) System.out.println("\t\tWorkingVertex is poked vertex: " + workingVertex);
			}

			// TODO Why globalInfinity?
			int tempProgressMeasure = workingVertex.getPM(scc, m_GlobalInfinity);

			// XXX Remove debugging information
			if (useDeepDebugPrints) System.out.print("\t\tBNM: " + workingVertex.getBEff());
			
			workingVertex.setBEff(calcBestNghbMeasure(workingVertex, localInfinity, usedSCCForNeighborCalculation));
			
			// XXX Remove debugging information
			if (useDeepDebugPrints) System.out.println(" -> " + workingVertex.getBEff());
			if (useDeepDebugPrints) System.out.print("\t\tNC: " + workingVertex.getC());
			
			workingVertex.setC(calcNghbCounter(workingVertex, localInfinity, usedSCCForNeighborCalculation));
			
			// XXX Remove debugging information
			if (useDeepDebugPrints) System.out.println(" -> " + workingVertex.getC());
			if (useDeepDebugPrints) System.out.print("\t\tPM: " + tempProgressMeasure);
			
			int currentProgressMeasure = increaseVector(workingVertex.getPriority(),
					workingVertex.getBEff(), localInfinity);
			workingVertex.setPM(currentProgressMeasure);
			
			// XXX Remove debugging information
			if (useDeepDebugPrints) System.out.println(" -> " + currentProgressMeasure);

			Set<Vertex<LETTER, STATE>> predVertices = m_Game.getPredecessors(workingVertex);
			if (predVertices == null || predVertices.isEmpty()) {
				continue;
			}
			
			// XXX Remove debugging information
			if (useDeepDebugPrints) System.out.println("\t\tWorking predecessors:");
			
			for (Vertex<LETTER, STATE> pred : predVertices) {
				if (pred.isInWL()) {
					continue;
				}
				// If vertex has newly reached localInfinity and predecessor,
				// which is a 1-distance neighbor of SCC, is interested
				boolean pokePossible = false;
				if (m_UseSCCs && !scc.contains(pred)) {
					pokePossible = currentProgressMeasure >= localInfinity
							&& tempProgressMeasure < localInfinity
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
								if (useDeepDebugPrints) System.out.println("\t\t\tInit C for pokePossible predecessor: " + pred);
								if (useDeepDebugPrints) System.out.print("\t\t\t\tC: " + pred.getC());
								
								pred.setC(m_Game.getSuccessors(pred).size());
								
								// XXX Remove debugging information
								if (useDeepDebugPrints) System.out.println(" -> " + pred.getC());
							} else {
								// XXX Remove debugging information
								if (useDeepDebugPrints) System.out.println("\t\t\tPokePossible predecessor was already initialized: " + pred);
							}
						}
						
						if (pred.getC() == 1) {
							if (pokePossible) {
								// XXX Remove debugging information
								if (useDeepDebugPrints) System.out.println("\t\t\tOnly one good neighbor, poking: " + pred);
								
								m_pokedFromNeighborSCC.add(pred);
							} else {
								// XXX Remove debugging information
								if (useDeepDebugPrints) System.out.println("\t\t\tOnly one good neighbor, adding to wL: " + pred);
								
								addVertexToWorkingList(pred);
							}
						} else if (pred.getC() > 1) {
							// XXX Remove debugging information
							if (useDeepDebugPrints) System.out.println("\t\t\tMore good neighbors, decreasing C: " + pred);
							
							pred.setC(pred.getC() - 1);
						}
					} else if (pred.isSpoilerVertex()) {
						if (pokePossible) {
							// XXX Remove debugging information
							if (useDeepDebugPrints) System.out.println("\t\t\tIs spoiler vertex, poking: " + pred);
							
							m_pokedFromNeighborSCC.add(pred);
						} else {
							// XXX Remove debugging information
							if (useDeepDebugPrints) System.out.println("\t\t\tIs spoiler vertex, adding to wL: " + pred);
							
							addVertexToWorkingList(pred);
						}
					}
				}
			}
			
			if (m_UseSCCs && m_pokedFromNeighborSCC.contains(workingVertex)) {
				m_pokedFromNeighborSCC.remove(workingVertex);
			}
			
			// XXX Remove debugging information
			if (m_StepCounter % 1_000_000 == 0) {
				if (useDebugPrints) System.out.println("Worked " + m_StepCounter + " steps, wL has size of " + m_WorkingList.size());
			}
		}
	}

	@Override
	protected AGameGraph<LETTER, STATE> getGameGraph() {
		return m_Game;
	}
}