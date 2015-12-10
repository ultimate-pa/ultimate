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
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StringFactory;
import de.uni_freiburg.informatik.ultimate.core.services.ToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;

/**
 * Doc comes later.
 * 
 * @author Daniel Tischner
 * 
 * @param <LETTER>
 * @param <STATE>
 *
 */
public final class ReduceBuchiFairSimulation<LETTER, STATE> implements IOperation<LETTER, STATE> {
	
	public static void main(final String[] args) throws OperationCanceledException {
		ToolchainStorage service = new ToolchainStorage();
		StateFactory<String> snf = (StateFactory<String>) new StringFactory();
		
		// Buechi automaton
		Set<String> alphabet = new HashSet<String>();
		alphabet.add("a");
		alphabet.add("b");
		NestedWordAutomaton<String, String> buechi =
				new NestedWordAutomaton<String, String>(service, alphabet, null, null, snf);
		
		// Big example from tutors cardboard
//		buechi.addState(true, false, "q0");
//		buechi.addState(false, false, "q1");
//		buechi.addState(false, true, "q2");
//		buechi.addState(false, false, "q3");
//		buechi.addState(false, true, "q4");
//		buechi.addInternalTransition("q0", "a", "q1");
//		buechi.addInternalTransition("q1", "a", "q1");
//		buechi.addInternalTransition("q1", "a", "q2");
//		buechi.addInternalTransition("q2", "a", "q2");
//		buechi.addInternalTransition("q2", "a", "q1");
//		buechi.addInternalTransition("q0", "a", "q3");
//		buechi.addInternalTransition("q3", "b", "q3");
//		buechi.addInternalTransition("q3", "a", "q4");
//		buechi.addInternalTransition("q4", "a", "q4");
//		buechi.addInternalTransition("q4", "b", "q3");
		
		// Small example from cav02 paper
//		buechi.addState(true, true, "q1");
//		buechi.addState(false, false, "q2");
//		buechi.addInternalTransition("q1", "a", "q1");
//		buechi.addInternalTransition("q1", "b", "q2");
//		buechi.addInternalTransition("q2", "b", "q2");
//		buechi.addInternalTransition("q2", "a", "q1");
		
		// Small example from cav02 paper extended so that nodes share the same transitions
//		buechi.addState(true, true, "q1");
//		buechi.addState(false, false, "q2");
//		buechi.addInternalTransition("q1", "a", "q1");
//		buechi.addInternalTransition("q1", "b", "q1");
//		buechi.addInternalTransition("q1", "a", "q2");
//		buechi.addInternalTransition("q1", "b", "q2");
//		buechi.addInternalTransition("q2", "a", "q2");
//		buechi.addInternalTransition("q2", "b", "q2");
//		buechi.addInternalTransition("q2", "a", "q1");
//		buechi.addInternalTransition("q2", "b", "q1");
		
		// Small circle example from mind
//		buechi.addState(true, true, "q1");
//		buechi.addState(false, false, "q2");
//		buechi.addState(true, false, "q3");
//		buechi.addState(false, false, "q4");
//		buechi.addInternalTransition("q1", "a", "q2");
//		buechi.addInternalTransition("q2", "b", "q3");
//		buechi.addInternalTransition("q3", "a", "q4");
//		buechi.addInternalTransition("q4", "b", "q1");
		
		// Non merge-able example with a one-directed fair simulation
//		buechi.addState(true, true, "q0");
//		buechi.addState(false, false, "q1");
//		buechi.addInternalTransition("q0", "b", "q0");
//		buechi.addInternalTransition("q0", "a", "q1");
//		buechi.addInternalTransition("q1", "a", "q1");
//		buechi.addInternalTransition("q1", "b", "q1");
		
		// Big example from cav02
		buechi.addState(true, false, "q1");
		buechi.addState(false, false, "q2");
		buechi.addState(false, true, "q3");
		buechi.addState(false, true, "q4");
		buechi.addState(false, false, "q5");
		buechi.addState(false, true, "q6");
		buechi.addState(false, false, "q7");
		buechi.addState(false, false, "q8");
		buechi.addState(false, false, "q9");
		buechi.addState(false, true, "q10");
		buechi.addInternalTransition("q1", "a", "q2");
		buechi.addInternalTransition("q1", "a", "q3");
		buechi.addInternalTransition("q2", "a", "q6");
		buechi.addInternalTransition("q2", "b", "q4");
		buechi.addInternalTransition("q2", "b", "q7");
		buechi.addInternalTransition("q4", "a", "q2");
		buechi.addInternalTransition("q6", "a", "q6");
		buechi.addInternalTransition("q3", "b", "q5");
		buechi.addInternalTransition("q3", "b", "q7");
		buechi.addInternalTransition("q5", "a", "q3");
		buechi.addInternalTransition("q7", "b", "q8");
		buechi.addInternalTransition("q8", "a", "q9");
		buechi.addInternalTransition("q8", "b", "q10");
		buechi.addInternalTransition("q9", "a", "q9");
		buechi.addInternalTransition("q9", "b", "q10");
		buechi.addInternalTransition("q10", "b", "q10");
		
		// Debug test automata 1
//		buechi.addState(true, false, "q0");
//		buechi.addState(false, false, "q1");
//		buechi.addState(false, false, "q2");
//		buechi.addState(false, true, "q3");
//		buechi.addState(false, false, "q4");
//		buechi.addInternalTransition("q1", "b", "q0");
//		buechi.addInternalTransition("q2", "b", "q2");
//		buechi.addInternalTransition("q2", "a", "q3");
//		buechi.addInternalTransition("q3", "b", "q4");
//		buechi.addInternalTransition("q4", "b", "q3");
//		buechi.addInternalTransition("q0", "b", "q1");
//		buechi.addInternalTransition("q0", "b", "q2");
//		buechi.addInternalTransition("q0", "b", "q4");
//		buechi.addInternalTransition("q0", "a", "q2");
//		buechi.addInternalTransition("q0", "a", "q4");
		
		// Debug test automata 2
//		alphabet = new HashSet<String>();
//		alphabet.add("a");
//		alphabet.add("b");
//		alphabet.add("c");
//		buechi = new NestedWordAutomaton<String, String>(service, alphabet, null, null, snf);
//		buechi.addState(true, false, "q0");
//		buechi.addState(false, false, "q1");
//		buechi.addState(false, false, "q2");
//		buechi.addState(false, false, "q3");
//		buechi.addState(false, true, "q4");
//		buechi.addState(false, true, "q5");
//		buechi.addState(false, false, "q6");
//		buechi.addState(false, false, "q7");
//		buechi.addState(false, false, "q8");
//		buechi.addState(false, false, "q9");
//		buechi.addInternalTransition("q1", "b", "q1");
//		buechi.addInternalTransition("q1", "c", "q3");
//		buechi.addInternalTransition("q1", "c", "q8");
//		buechi.addInternalTransition("q1", "a", "q7");
//		buechi.addInternalTransition("q2", "b", "q2");
//		buechi.addInternalTransition("q2", "b", "q7");
//		buechi.addInternalTransition("q2", "b", "q8");
//		buechi.addInternalTransition("q2", "b", "q9");
//		buechi.addInternalTransition("q2", "c", "q2");
//		buechi.addInternalTransition("q2", "c", "q5");
//		buechi.addInternalTransition("q2", "c", "q7");
//		buechi.addInternalTransition("q2", "a", "q3");
//		buechi.addInternalTransition("q2", "a", "q6");
//		buechi.addInternalTransition("q3", "b", "q3");
//		buechi.addInternalTransition("q3", "b", "q4");
//		buechi.addInternalTransition("q3", "b", "q5");
//		buechi.addInternalTransition("q3", "b", "q7");
//		buechi.addInternalTransition("q3", "b", "q8");
//		buechi.addInternalTransition("q3", "a", "q6");
//		buechi.addInternalTransition("q3", "a", "q7");
//		buechi.addInternalTransition("q3", "a", "q9");
//		buechi.addInternalTransition("q4", "b", "q1");
//		buechi.addInternalTransition("q4", "b", "q4");
//		buechi.addInternalTransition("q4", "b", "q9");
//		buechi.addInternalTransition("q4", "c", "q5");
//		buechi.addInternalTransition("q4", "a", "q4");
//		buechi.addInternalTransition("q5", "c", "q5");
//		buechi.addInternalTransition("q6", "b", "q2");
//		buechi.addInternalTransition("q6", "b", "q5");
//		buechi.addInternalTransition("q6", "b", "q9");
//		buechi.addInternalTransition("q6", "b", "q0");
//		buechi.addInternalTransition("q6", "c", "q2");
//		buechi.addInternalTransition("q6", "c", "q7");
//		buechi.addInternalTransition("q6", "c", "q9");
//		buechi.addInternalTransition("q6", "a", "q9");
//		buechi.addInternalTransition("q6", "a", "q0");
//		buechi.addInternalTransition("q7", "c", "q2");
//		buechi.addInternalTransition("q7", "c", "q0");
//		buechi.addInternalTransition("q7", "a", "q6");
//		buechi.addInternalTransition("q7", "a", "q9");
//		buechi.addInternalTransition("q8", "b", "q2");
//		buechi.addInternalTransition("q8", "b", "q8");
//		buechi.addInternalTransition("q8", "a", "q4");
//		buechi.addInternalTransition("q8", "a", "q5");
//		buechi.addInternalTransition("q8", "a", "q0");
//		buechi.addInternalTransition("q9", "b", "q3");
//		buechi.addInternalTransition("q9", "b", "q7");
//		buechi.addInternalTransition("q9", "c", "q1");
//		buechi.addInternalTransition("q9", "c", "q2");
//		buechi.addInternalTransition("q9", "a", "q2");
//		buechi.addInternalTransition("q9", "a", "q4");
//		buechi.addInternalTransition("q9", "a", "q8");
//		buechi.addInternalTransition("q0", "b", "q1");
//		buechi.addInternalTransition("q0", "b", "q3");
//		buechi.addInternalTransition("q0", "b", "q6");
//		buechi.addInternalTransition("q0", "c", "q3");
//		buechi.addInternalTransition("q0", "c", "q8");
//		buechi.addInternalTransition("q0", "c", "q0");
//		buechi.addInternalTransition("q0", "a", "q3");
//		buechi.addInternalTransition("q0", "a", "q8");
		
		// Comparing test 'SCC vs. nonSCC'
		/*
		int n = 50;
		int k = 10;
		int f = 20;
		int amount = 1;
		System.out.println("Start comparing test 'SCC vs. nonSCC' with " + amount
				+ " random automata (n=" + n + ", k=" + k + ", f=" + f + ")...");
		
		for (int i = 1; i <= amount; i++) {
			if (i % 100 == 0) {
				System.out.println("\tWorked " + i + " automata");
			}
			
//			System.out.println("Start calculating random DFA (n=" + n + ", k=" + k + ", f=" + f + ")...");
//			buechi = new GetRandomNwa(service, k, n, 0.2, 0, 0, 0.2).getResult();
			buechi = new GetRandomDfa(service, n, k, f, 5, true, false, false, false).getResult();
//			System.out.println("End calculating random DFA.");
//			System.out.println();
			
			System.out.println("Start Simulation with SCC...");
			FairSimulation<String, String> simulationSCC = new FairSimulation<String, String>(service, buechi, true, snf);
			System.out.println();
			
			System.out.println("Start Simulation without SCC...");
			FairSimulation<String, String> simulationNoSCC = new FairSimulation<String, String>(service, buechi, false, snf);
			System.out.println();
			
			System.out.println("Start comparing results...");
			boolean errorOccurred = false;
			FairGameGraph<String, String> simNoSCCGraph = (FairGameGraph<String, String>) simulationNoSCC.getGameGraph();
			Set<Vertex<String, String>> simSCCVertices = simulationSCC.getGameGraph().getVertices();
			Set<Vertex<String, String>> simNoSCCVertices = simulationNoSCC.getGameGraph().getVertices();
			int globalInfinity = simNoSCCGraph.getGlobalInfinity();
			if (simSCCVertices.size() != simSCCVertices.size()) {
				System.err.println("SimSCC and SimNoSCC have different size: " + simSCCVertices.size()
					+ " & " + simNoSCCVertices.size());
				errorOccurred = true;
			}
			if (globalInfinity != simulationSCC.getGameGraph().getGlobalInfinity()) {
				System.err.println("SimSCC and SimNoSCC have different infinities: "
						+ simulationSCC.getGameGraph().getGlobalInfinity() + " & " + globalInfinity);
				errorOccurred = true;
			}
			for (Vertex<String, String> simSCCVertex : simSCCVertices) {
				if (simSCCVertex.isSpoilerVertex()) {
					SpoilerVertex<String, String> asSV = (SpoilerVertex<String, String>) simSCCVertex;
					SpoilerVertex<String, String> simNoSCCVertex = simNoSCCGraph.getSpoilerVertex(asSV.getQ0(), asSV.getQ1(), false);
					if (simNoSCCVertex == null) {
						System.err.println("SCCVertex unknown for nonSCC version: " + asSV);
						errorOccurred = true;
					} else {
						int sccPM = asSV.getPM(null, globalInfinity);
						int nonSCCPM = simNoSCCVertex.getPM(null, globalInfinity);
						if (sccPM < globalInfinity && nonSCCPM >= globalInfinity) {
							System.err.println("SCCVertex is not infinity but nonSCC is (" + asSV + "): " + sccPM + " & " + nonSCCPM);
							errorOccurred = true;
						} else if (sccPM >= globalInfinity && nonSCCPM < globalInfinity) {
							System.err.println("SCCVertex is infinity but nonSCC is not (" + asSV + "): " + sccPM + " & " + nonSCCPM);
							errorOccurred = true;
						}
					}
				} else {
					DuplicatorVertex<String, String> asDV = (DuplicatorVertex<String, String>) simSCCVertex;
					DuplicatorVertex<String, String> simNoSCCVertex = simNoSCCGraph.getDuplicatorVertex(asDV.getQ0(),
							asDV.getQ1(), asDV.getLetter(), false);
					if (simNoSCCVertex == null) {
						System.err.println("SCCVertex unknown for nonSCC version: " + asDV);
						errorOccurred = true;
					} else {
						int sccPM = asDV.getPM(null, globalInfinity);
						int nonSCCPM = simNoSCCVertex.getPM(null, globalInfinity);
						if (sccPM < globalInfinity && nonSCCPM >= globalInfinity) {
							System.err.println("SCCVertex is not infinity but nonSCC is (" + asDV + "): " + sccPM + " & " + nonSCCPM);
							errorOccurred = true;
						} else if (sccPM >= globalInfinity && nonSCCPM < globalInfinity) {
							System.err.println("SCCVertex is infinity but nonSCC is not (" + asDV + "): " + sccPM + " & " + nonSCCPM);
							errorOccurred = true;
						}
					}
				}
			}
			
			if (errorOccurred) {
				System.out.println("End comparing results, an error occurred. Printing buechi...");
				System.out.println(buechi);
				break;
			} else {
				System.out.println("End comparing results, no error occurred.");
			}
			
			System.out.println(simulationSCC);
		}
		*/
		
		// Single automata comparison
		/*
		System.out.println("Start Simulation with SCC...");
		FairSimulation<String, String> simulationSCC = new FairSimulation<String, String>(service, buechi, true, snf);
		System.out.println(simulationSCC);
		
		System.out.println("Start Simulation without SCC...");
		FairSimulation<String, String> simulationNoSCC = new FairSimulation<String, String>(service, buechi, false, snf);
		System.out.println(simulationNoSCC);
		*/
		
		// Merge tests
//		FairSimulation<String, String> simulation = new FairSimulation<String, String>(service, buechi, true, snf);
		
		// Operation tests
		ReduceBuchiFairSimulation<String, String> operation =
				new ReduceBuchiFairSimulation<String, String>(service, snf, buechi);
		try {
			if (operation.checkResult(snf)) {
				System.out.println("Operation is correct.");
			} else {
				System.out.println("Operation is NOT correct.");
			}
		} catch (AutomataLibraryException e) {
			e.printStackTrace();
		}
		
		System.out.println("Program terminated.");
	}
	
	private final Logger m_Logger;

	private final INestedWordAutomatonOldApi<LETTER, STATE> m_Operand;

	private final INestedWordAutomatonOldApi<LETTER, STATE> m_Result;

	private final IUltimateServiceProvider m_Services;

	public ReduceBuchiFairSimulation(final IUltimateServiceProvider services,
			final StateFactory<STATE> stateFactory,
			final INestedWordAutomatonOldApi<LETTER, STATE> operand)
					throws OperationCanceledException {
		m_Services = services;
		m_Logger = m_Services.getLoggingService().getLogger(LibraryIdentifiers.s_LibraryID);
		m_Operand = operand;
		m_Logger.info(startMessage());

		m_Result = new FairSimulation<LETTER, STATE>(m_Services, m_Operand, true, stateFactory).getResult();

		boolean compareWithNonSccResult = false;
		if (compareWithNonSccResult) {
			NestedWordAutomaton<LETTER, STATE> nonSCCresult = new FairSimulation<LETTER, STATE>(m_Services, m_Operand,
					false, stateFactory).getResult();
			if (m_Result.size() != nonSCCresult.size()) {
				throw new AssertionError();
			}
		}

		m_Logger.info(exitMessage());
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.IOperation#checkResult(
	 * de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory)
	 */
	@SuppressWarnings("deprecation")
	@Override
	public boolean checkResult(final StateFactory<STATE> stateFactory) throws AutomataLibraryException {
		m_Logger.info("Start testing correctness of " + operationName());
		boolean correct = true;
		correct &= (ResultChecker.nwaLanguageInclusion(m_Services, m_Operand, m_Result, stateFactory) == null);
		correct &= (ResultChecker.nwaLanguageInclusion(m_Services, m_Result, m_Operand, stateFactory) == null);
		if (!correct) {
			ResultChecker.writeToFileIfPreferred(m_Services, operationName() + "Failed", "", m_Operand);
		}
		m_Logger.info("Finished testing correctness of " + operationName());
		return correct;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.automata.IOperation#exitMessage()
	 */
	@Override
	public String exitMessage() {
		return "Finished " + operationName() + " Result " + m_Result.sizeInformation();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.IOperation#getResult()
	 */
	@Override
	public Object getResult() throws AutomataLibraryException {
		return m_Result;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.automata.IOperation#operationName()
	 */
	@Override
	public String operationName() {
		return "reduceBuchiFairSimulation";
	}
	
	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.automata.IOperation#startMessage()
	 */
	@Override
	public String startMessage() {
		return "Start " + operationName() + ". Operand has " + m_Operand.sizeInformation();
	}

}
