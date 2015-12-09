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

import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.AGameGraph;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.ASimulation;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.GameGraphChanges;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.GameGraphSuccessorProvider;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.DuplicatorVertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.SpoilerVertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.Vertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.util.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.relation.Triple;
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

	private static <LETTER, STATE> void saveBEffChange(Vertex<LETTER, STATE> vertex,
			int oldValue, GameGraphChanges<LETTER, STATE> changes) {
		if (changes != null && oldValue != vertex.getBEff()
				&& !changes.hasBEffEntry(vertex)) {
			changes.rememberBEffVertex(vertex, oldValue);
		}
	}

	private static <LETTER, STATE> void saveCChange(Vertex<LETTER, STATE> vertex, int oldValue,
			GameGraphChanges<LETTER, STATE> changes) {
		if (changes != null && oldValue != vertex.getC()
				&& !changes.hasCEntry(vertex)) {
			changes.rememberCVertex(vertex, oldValue);
		}
	}

	private static <LETTER, STATE> void savePmChange(Vertex<LETTER, STATE> vertex, int oldValue,
			GameGraphChanges<LETTER, STATE> changes) {
		if (changes != null && oldValue != vertex.getPM(null, 0)
				&& !changes.hasPmEntry(vertex)) {
			changes.rememberPmVertex(vertex, oldValue);
		}
	}
	
	private static <LETTER, STATE> String sccToString(
			final StronglyConnectedComponent<Vertex<LETTER, STATE>> scc) {
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
	
	private boolean m_AttemptingChanges;
	
	private final INestedWordAutomatonOldApi<LETTER, STATE> m_Buechi;
	
	private GameGraphChanges<LETTER, STATE> m_CurrentChanges;
	
	private final FairGameGraph<LETTER, STATE> m_Game;
	
	private final int m_GlobalInfinity;
	
	private Set<SpoilerVertex<LETTER, STATE>> m_NotSimulatingNonTrivialVertices;
	
	private HashSet<Vertex<LETTER, STATE>> m_pokedFromNeighborSCC;

	private boolean m_SimulationWasAborted;
	
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
		m_NotSimulatingNonTrivialVertices = new HashSet<SpoilerVertex<LETTER, STATE>>();
		m_CurrentChanges = null;
		
		// XXX Remove debugging information
		if (useDeepDebugPrints) System.out.println("Start constructing game graph...");
		
		m_Game = new FairGameGraph<LETTER, STATE>(services, buechi);
		
		// XXX Remove debugging information
		if (useDeepDebugPrints) System.out.println("End constructing game graph.");
		
		m_GlobalInfinity = m_Game.getGlobalInfinity();
		
		m_AttemptingChanges = false;
		m_SimulationWasAborted = false;
		
		doSimulation();
	}
	
	@Override
	public String toString() {
		StringBuilder result = new StringBuilder();
		String lineSeparator = System.lineSeparator();
		// Header
		result.append("FairSimulationResults fsr = (");
		
		// Properties
		result.append(lineSeparator + "\tuseSCCs = " + isUsingSCCs());
		result.append(lineSeparator + "\tglobalInfinity = " + m_GlobalInfinity);
		result.append(lineSeparator + "\tstepCounter = " + m_StepCounter);
		result.append(lineSeparator + "\tbuechi size before = " + m_Buechi.size() + " states");
		if (getResult() != null) {
			result.append(lineSeparator + "\tbuechi size after = " + getResult().size() + " states");
		}
		
		// Progress Measure
		result.append(lineSeparator + "\tprogress measure = {");
		for (SpoilerVertex<LETTER, STATE> vertex : m_Game.getSpoilerVertices()) {
			int localInfinity = m_GlobalInfinity;
			if (isUsingSCCs()) {
				for (StronglyConnectedComponent<Vertex<LETTER, STATE>> scc : getSccComp().getSCCs()) {
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
			if (isUsingSCCs()) {
				for (StronglyConnectedComponent<Vertex<LETTER, STATE>> scc : getSccComp().getSCCs()) {
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
//		result.append(lineSeparator + "\tbest neighbor measure = {");
//		for (SpoilerVertex<LETTER, STATE> vertex : m_Game.getSpoilerVertices()) {
//			result.append(lineSeparator + "\t\t<(" + vertex.getQ0()
//				+ ", " + vertex.getQ1() + "), bnm:" + vertex.getBEff() + ">");
//		}
//		for (DuplicatorVertex<LETTER, STATE> vertex : m_Game.getDuplicatorVertices()) {
//			result.append(lineSeparator + "\t\t<(" + vertex.getQ0()
//				+ ", " + vertex.getQ1() + ", " + vertex.getLetter()
//				+ "), bnm:" + vertex.getBEff() + ">");
//		}
//		result.append(lineSeparator + "\t},");
		
		// Neighbor counter
//		result.append(lineSeparator + "\tneighbor counter = {");
//		for (SpoilerVertex<LETTER, STATE> vertex : m_Game.getSpoilerVertices()) {
//			result.append(lineSeparator + "\t\t<(" + vertex.getQ0()
//				+ ", " + vertex.getQ1() + "), nc:" + vertex.getC() + ">");
//		}
//		for (DuplicatorVertex<LETTER, STATE> vertex : m_Game.getDuplicatorVertices()) {
//			result.append(lineSeparator + "\t\t<(" + vertex.getQ0()
//				+ ", " + vertex.getQ1() + ", " + vertex.getLetter()
//				+ "), nc:" + vertex.getC() + ">");
//		}
//		result.append(lineSeparator + "\t},");
		
		// Footer
		result.append(lineSeparator + ");");
		
		return result.toString();
	}
	
	private void addVertexToWorkingList(final Vertex<LETTER, STATE> vertex) {
		getWorkingList().add(vertex);
		vertex.setInWL(true);
	}
	
	private FairGameGraphChanges<LETTER, STATE> attemptEdgeRemoval(final STATE src,
			final LETTER a, final STATE dest) {
		FairGameGraphChanges<LETTER, STATE> changes =
				m_Game.removeBuechiTransition(src, a, dest);
		
		return validateChange(changes);
	}

	private FairGameGraphChanges<LETTER, STATE> attemptMerge(final STATE firstState,
			final STATE secondState) {
		FairGameGraphChanges<LETTER, STATE> changes =
				m_Game.equalizeBuechiStates(firstState, secondState);
		
		return validateChange(changes);
	}

	private boolean doSingleSimulation(
			final GameGraphChanges<LETTER, STATE> changes) {
		long startTimeSCCCalc = 0;
		long durationSCCCalc = 0;
		m_StepCounter = 0;
		int stepsWorked = 0;

		if (isUsingSCCs()) {
			// XXX Remove debugging information
			if (useDebugPrints) System.out.println(">Calculating SCCs...");
			
			startTimeSCCCalc = System.currentTimeMillis();
			m_pokedFromNeighborSCC = new HashSet<Vertex<LETTER, STATE>>();
			DefaultStronglyConnectedComponentFactory<Vertex<LETTER, STATE>> sccFactory =
        			new DefaultStronglyConnectedComponentFactory<Vertex<LETTER, STATE>>();
        	GameGraphSuccessorProvider<LETTER, STATE> succProvider =
        			new GameGraphSuccessorProvider<LETTER, STATE>(m_Game);
			setSccComp(new SccComputation<Vertex<LETTER, STATE>, StronglyConnectedComponent<Vertex<LETTER, STATE>>>(getLogger(), succProvider,
					sccFactory, m_Game.getSize(), m_Game.getVertices()));
			durationSCCCalc = System.currentTimeMillis() - startTimeSCCCalc;
			
			// XXX Remove debugging information
			if (useDebugPrints) System.out.println("\tAmount of SCCs: " + getSccComp().getSCCs().size());
			
			Iterator<StronglyConnectedComponent<Vertex<LETTER, STATE>>> iter =
					new LinkedList<StronglyConnectedComponent<Vertex<LETTER, STATE>>>(getSccComp().getSCCs()).iterator();
			
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
					if (useDebugPrints) System.out.println("Worked " + stepsWorked + " SCCs of " + getSccComp().getSCCs().size());
				}
				
				m_CurrentChanges = changes;
				efficientLiftingAlgorithm(infinityOfSCC, scc.getNodes());
				if (m_SimulationWasAborted) {
					return false;
				}
			}
		} else {
			// XXX Remove debugging information
			if (useDebugPrints) System.out.println(">Starting iterations...");
			
			m_CurrentChanges = changes;
			efficientLiftingAlgorithm(m_GlobalInfinity, null);
			if (m_SimulationWasAborted) {
				return false;
			}
		}
		
		// XXX Remove debugging information
		if (isUsingSCCs()) {
			if (useDebugPrints) System.out.println(">Calculating SCCs took " + durationSCCCalc + "ms.");
		}
		
		return true;
	}
	
	private NestedMap2<STATE, LETTER, STATE> edgeCandidates(
			final Set<SpoilerVertex<LETTER, STATE>> exclusiveSet) {
		NestedMap2<STATE, LETTER, STATE> edgeCandidates =
				new NestedMap2<STATE, LETTER, STATE>();
		Set<SpoilerVertex<LETTER, STATE>> spoilerVertices =
				m_Game.getSpoilerVertices();
		for (SpoilerVertex<LETTER, STATE> vertex : spoilerVertices) {
			if (vertex.getPM(null, m_GlobalInfinity) < m_GlobalInfinity
					&& !exclusiveSet.contains(vertex)) {
				// Skip vertex if it is a trivial simulation
				if (vertex.getQ0().equals(vertex.getQ1())) {
					continue;
				}
				
				// Searching for transition
				// q1 -a-> q2 where q1 -a-> q3 and q3 simulating q2
				STATE simulatingState = vertex.getQ1();
				STATE simulatedState = vertex.getQ0();
				for (IncomingInternalTransition<LETTER, STATE> predTrans
						: m_Buechi.internalPredecessors(simulatingState)) {
					boolean transCovered = false;
					for (IncomingInternalTransition<LETTER, STATE> coveringTrans
							: m_Buechi.internalPredecessors(
									predTrans.getLetter(), simulatedState)) {
						if (coveringTrans.getPred().equals(predTrans.getPred())) {
							transCovered = true;
							break;
						}
					}
					if (transCovered) {
						edgeCandidates.put(predTrans.getPred(),
								predTrans.getLetter(), simulatedState);
					}
				}
				
			}
		}
		return edgeCandidates;
	}
	
	private void initSimulation(final int localInfinity,
			final Set<Vertex<LETTER, STATE>> scc) {
		// XXX Remove debugging information
		if (useDeepDebugPrints) System.out.println("\tInit:");
		
		m_SimulationWasAborted = false;
		createWorkingList();
		if (isUsingSCCs()) {
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
		if (!m_Game.hasSuccessors(vertex) || vertex.getPriority() == 1
				|| (isUsingSCCs() && m_pokedFromNeighborSCC.contains(vertex))
				|| (m_AttemptingChanges && m_CurrentChanges != null
					&& m_CurrentChanges.isAddedVertex(vertex)
					&& vertex.getPriority() != 0)
				|| (m_AttemptingChanges && m_CurrentChanges != null
					&& m_CurrentChanges.isChangedEdgeSource(vertex))) {
			addVertexToWorkingList(vertex);
			
			// XXX Remove debugging information
			if (!m_Game.hasSuccessors(vertex)) {
				if (useDeepDebugPrints) System.out.println("\t\tIs dead-end, adding to wL: " + vertex);
			} else if (isUsingSCCs() && m_pokedFromNeighborSCC.contains(vertex)) {
				if (useDeepDebugPrints) System.out.println("\t\tWas poked, adding to wL: " + vertex);
			} else if (m_AttemptingChanges && m_CurrentChanges != null
					&& m_CurrentChanges.isAddedVertex(vertex)
					&& vertex.getPriority() != 0) {
				if (useDeepDebugPrints) System.out.println("\t\tWas added previously and can contribute, adding to wL: " + vertex);
			} else if (m_AttemptingChanges && m_CurrentChanges != null
					&& m_CurrentChanges.isChangedEdgeSource(vertex)) {
				if (useDeepDebugPrints) System.out.println("\t\tIs source of a changed edge, adding to wL: " + vertex);
			}
		}
		if (isUsingSCCs()) {
			Set<Vertex<LETTER, STATE>> usedSCCForNeighborCalculation = scc;
			if (m_pokedFromNeighborSCC.contains(vertex)) {
				usedSCCForNeighborCalculation = null;
			}
			int oldC = vertex.getC();
			vertex.setC(calcNghbCounter(vertex, localInfinity, usedSCCForNeighborCalculation));
			saveCChange(vertex, oldC, m_CurrentChanges);
		} else if (m_Game.hasSuccessors(vertex)) {
			if (!m_AttemptingChanges || vertex.getC() == 0) {
				int oldC = vertex.getC();
				vertex.setC(m_Game.getSuccessors(vertex).size());
				saveCChange(vertex, oldC, m_CurrentChanges);
			}
		}
	}
	
	private Set<SpoilerVertex<LETTER, STATE>> mergeCandidates() {
		Set<SpoilerVertex<LETTER, STATE>> mergeCandidates = new HashSet<SpoilerVertex<LETTER, STATE>>();
		Set<SpoilerVertex<LETTER, STATE>> spoilerVertices =
				m_Game.getSpoilerVertices();
		Set<SpoilerVertex<LETTER, STATE>> workedPairs = new HashSet<SpoilerVertex<LETTER, STATE>>();
		for (SpoilerVertex<LETTER, STATE> vertex : spoilerVertices) {
			if (vertex.getPM(null, m_GlobalInfinity) < m_GlobalInfinity) {
				// Skip vertex if it is a trivial simulation
				if (vertex.getQ0().equals(vertex.getQ1())) {
					continue;
				}
				// Found a one-directed fair simulating pair
				boolean pairIsNew = workedPairs.add(vertex);
				
				if (pairIsNew && workedPairs.contains(
						m_Game.getSpoilerVertex(vertex.getQ1(),
								vertex.getQ0(), false))) {
					// Found a two-directed fair simulating pair
					mergeCandidates.add(vertex);
				}
			}
		}
		return mergeCandidates;
	}
	
	private Vertex<LETTER, STATE> pollVertexFromWorkingList() {
		Vertex<LETTER, STATE> polledState = getWorkingList().poll();
		polledState.setInWL(false);
		return polledState;
	}
	
	private void printWorkingList() {
		StringBuilder result = new StringBuilder();
		String lineSeparator = System.lineSeparator();
		// Inline
		if (getWorkingList().size() <= 1) {
			lineSeparator = "";
		}
		
		// Header
		result.append("\twL = (");
		Iterator<Vertex<LETTER, STATE>> iter = getWorkingList().iterator();
		while (iter.hasNext()) {
			result.append(lineSeparator + "\t\t" + iter.next());
		}
		// Footer
		result.append(lineSeparator + "\t);");
		
		if (useDeepDebugPrints) System.out.println(result);
	}
	
	private FairGameGraphChanges<LETTER, STATE> validateChange(
			FairGameGraphChanges<LETTER, STATE> changes) {
		// Only do simulation if there actually was a change
		boolean wasSuccessful = true;
		if (changes != null) {
			wasSuccessful = doSingleSimulation(changes);
		}
		
		// Discard changes if language did not change
		// so that they can not be undone.
		if (wasSuccessful) {
			changes = null;
		}
		
		return changes;
	}
	
	@Override
	protected void doSimulation() throws OperationCanceledException {
		// XXX Remove debugging information
		if (useDebugPrints) System.out.println(">Starting minimization, useSCCs: " + isUsingSCCs());
		long startTime = System.currentTimeMillis();
		
		// First simulation
		doSingleSimulation(null);
		
		// XXX Remove debugging information
//		System.out.println("Before changes: ");
//		System.out.println(this);
		
		// Merge states
		m_AttemptingChanges = true;
		Set<SpoilerVertex<LETTER, STATE>> mergeCandidates = mergeCandidates();
		Set<SpoilerVertex<LETTER, STATE>> noEdgeCandidates = new HashSet<SpoilerVertex<LETTER, STATE>>();
		for (SpoilerVertex<LETTER, STATE> mergeCandidate : mergeCandidates) {
			FairGameGraphChanges<LETTER, STATE> changes =
					attemptMerge(mergeCandidate.getQ0(), mergeCandidate.getQ1());
			if (changes != null) {
				System.out.println("Not successfully merged, undoing: " + mergeCandidate);
				
				// XXX Remove debugging information
//				System.out.println("After modification: ");
//				System.out.println(this);
				
				m_Game.undoChanges(changes);
				
				// XXX Remove debugging information
//				System.out.println("After undoing: ");
//				System.out.println(this);
			} else {
				System.out.println("Successfully merged: " + mergeCandidate);
				noEdgeCandidates.add(mergeCandidate);
				SpoilerVertex<LETTER, STATE> mirroredCandidate =
						m_Game.getSpoilerVertex(mergeCandidate.getQ1(), mergeCandidate.getQ0(), false);
				if (mirroredCandidate != null) {
					noEdgeCandidates.add(mirroredCandidate);
				}
			}
		}
		
		// Remove redundant edges
		NestedMap2<STATE, LETTER, STATE> edgeCandidates = edgeCandidates(noEdgeCandidates);
		for (Triple<STATE, LETTER, STATE> edgeCandidate
				: edgeCandidates.entrySet()) {
			FairGameGraphChanges<LETTER, STATE> changes =
					attemptEdgeRemoval(edgeCandidate.getFirst(),
							edgeCandidate.getSecond(), edgeCandidate.getThird());
			if (changes != null) {
				System.out.println("Not successfully removed, undoing: " + edgeCandidate);
				
				// XXX Remove debugging information
//				System.out.println("After modification: ");
//				System.out.println(this);
				
				m_Game.undoChanges(changes);
				
				// XXX Remove debugging information
//				System.out.println("After undoing: ");
//				System.out.println(this);
			} else {
				System.out.println("Successfully removed: " + edgeCandidate);
			}
		}
		
		// XXX Remove debugging information
//		System.out.println("After everything: ");
//		System.out.println(this);
		
		// TODO Assign the reduced buechi
		setResult(m_Game.generateBuchiAutomatonFromGraph());

		long duration = System.currentTimeMillis() - startTime;
		getLogger().info((isUsingSCCs() ? "SCC version" : "nonSCC version") + " took " + duration + " milliseconds.");
		
		// XXX Remove debugging information
		if (useDebugPrints) System.out.println(">Simulation took " + m_StepCounter + " steps and " + duration + "ms.");
		if (useDebugPrints) System.out.println(">Ending minimization.");
	}
	
	@Override
	protected void efficientLiftingAlgorithm(final int localInfinity,
			final Set<Vertex<LETTER, STATE>> scc) {
		initSimulation(localInfinity, scc);
		
		// XXX Remove debugging information
		printWorkingList();
		
		while (!getWorkingList().isEmpty()) {
			m_StepCounter++;
			
			Vertex<LETTER, STATE> workingVertex = pollVertexFromWorkingList();
			
			// XXX Remove debugging information
			if (useDeepDebugPrints) System.out.println("\tWorkingVertex: " + workingVertex);
			
			Set<Vertex<LETTER, STATE>> usedSCCForNeighborCalculation = scc;
			if (isUsingSCCs() && m_pokedFromNeighborSCC.contains(workingVertex)) {
				usedSCCForNeighborCalculation = null;
				
				// XXX Remove debugging information
				if (useDeepDebugPrints) System.out.println("\t\tWorkingVertex is poked vertex: " + workingVertex);
			}
			
			int oldProgressMeasure = workingVertex.getPM(scc, m_GlobalInfinity);

			// XXX Remove debugging information
			if (useDeepDebugPrints) System.out.print("\t\tBNM: " + workingVertex.getBEff());
			
			int oldBEff = workingVertex.getBEff();
			workingVertex.setBEff(calcBestNghbMeasure(workingVertex, localInfinity, usedSCCForNeighborCalculation));
			saveBEffChange(workingVertex, oldBEff, m_CurrentChanges);
			
			// XXX Remove debugging information
			if (useDeepDebugPrints) System.out.println(" -> " + workingVertex.getBEff());
			if (useDeepDebugPrints) System.out.print("\t\tNC: " + workingVertex.getC());
			
			int oldC = workingVertex.getC();
			workingVertex.setC(calcNghbCounter(workingVertex, localInfinity, usedSCCForNeighborCalculation));
			saveCChange(workingVertex, oldC, m_CurrentChanges);
			
			// XXX Remove debugging information
			if (useDeepDebugPrints) System.out.println(" -> " + workingVertex.getC());
			if (useDeepDebugPrints) System.out.print("\t\tPM: " + oldProgressMeasure);
			
			int currentProgressMeasure = increaseVector(workingVertex.getPriority(),
					workingVertex.getBEff(), localInfinity);
			workingVertex.setPM(currentProgressMeasure);
			savePmChange(workingVertex, oldProgressMeasure, m_CurrentChanges);
			
			if (currentProgressMeasure >= m_GlobalInfinity) {
				if (workingVertex.isSpoilerVertex() &&
						!workingVertex.getQ0().equals(workingVertex.getQ1())) {
					// TODO Addition must be can undone
					boolean wasAdded = m_NotSimulatingNonTrivialVertices.add(
							(SpoilerVertex<LETTER, STATE>) workingVertex);
					if (m_AttemptingChanges && wasAdded) {
						// Abort simulation since progress measure
						// has changed on a non trivial vertex
						// which indicates language change
						m_NotSimulatingNonTrivialVertices.remove(
								(SpoilerVertex<LETTER, STATE>) workingVertex);
						m_SimulationWasAborted = true;
						return;
					}
				}
			}
			
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
				if (isUsingSCCs() && !scc.contains(pred)) {
					pokePossible = currentProgressMeasure >= localInfinity
							&& oldProgressMeasure < localInfinity
							&& !m_pokedFromNeighborSCC.contains(pred);
					if (!pokePossible) {
						continue;
					}
				}

				// TODO Why globalInfinity?
				if (decreaseVector(pred.getPriority(), workingVertex.getPM(scc, m_GlobalInfinity),
						localInfinity) > pred.getBEff()) {

					if (pred.isDuplicatorVertex() && (decreaseVector(pred.getPriority(),
							oldProgressMeasure, localInfinity) == pred.getBEff()
							|| (pokePossible && pred.getBEff() == 0))) {
						
						// If trying to use a vertex outside of the SCC make sure
						// the neighbor counter was initialized before accessing it
						if (pokePossible) {
							if (pred.getC() == 0) {
								// XXX Remove debugging information
								if (useDeepDebugPrints) System.out.println("\t\t\tInit C for pokePossible predecessor: " + pred);
								if (useDeepDebugPrints) System.out.print("\t\t\t\tC: " + pred.getC());
								
								int oldPredC = pred.getC();
								pred.setC(m_Game.getSuccessors(pred).size());
								saveCChange(pred, oldPredC, m_CurrentChanges);
								
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
							
							int oldPredC = pred.getC();
							pred.setC(pred.getC() - 1);
							saveCChange(pred, oldPredC, m_CurrentChanges);
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
			
			if (isUsingSCCs() && m_pokedFromNeighborSCC.contains(workingVertex)) {
				m_pokedFromNeighborSCC.remove(workingVertex);
			}
			
			// XXX Remove debugging information
			if (m_StepCounter % 1_000_000 == 0) {
				if (useDebugPrints) System.out.println("Worked " + m_StepCounter + " steps, wL has size of " + getWorkingList().size());
			}
		}
	}

	@Override
	protected AGameGraph<LETTER, STATE> getGameGraph() {
		return m_Game;
	}
}