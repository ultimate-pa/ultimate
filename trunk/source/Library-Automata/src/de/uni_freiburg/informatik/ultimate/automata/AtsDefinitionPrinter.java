/*
 * Copyright (C) 2009-2014 University of Freiburg
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
 * along with the ULTIMATE Automata Library.  If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Automata Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.text.DateFormat;
import java.text.SimpleDateFormat;
import java.util.Collection;
import java.util.Date;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.AlternatingAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Place;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.PetriNetJulian;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;


/**
 * Writes an automaton definition in the .ats format for a given automaton.
 * if Labeling == TOSTRING
 * The String representation of LETTER and STATE is used.
 * if Labeling == QUOTED
 * The String representation of LETTER and STATE plus the hashcode() is used.
 * if Labeling == NUMERATE
 * The String representations of LETTER and STATE are ignored.
 * The TestFileWriter introduces new names, e.g. the letters of the alphabet are
 * a0, ..., an.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 */

public class AtsDefinitionPrinter<LETTER,STATE> {

		public enum Labeling { NUMERATE, TOSTRING, QUOTED, BA_FORMAT };
		
		private final IUltimateServiceProvider m_Services;
		private static Logger s_Logger = 
			NestedWordAutomata.getLogger();
		
		/**
		 * Print hash modulo this number to get shorter identifiers.
		 */
		private static int m_HashDivisor = 1;
		
		PrintWriter m_printWriter;
		
		StringWriter m_StringWriter;
		
		private void initializePrintWriter(String filename) {
			File testfile = new File(filename + ".ats");
			try {
				FileWriter fileWriter = new FileWriter(testfile);
				m_printWriter = new PrintWriter(fileWriter);
			} catch (IOException e) {
				e.printStackTrace();
			} 
		}
		
		
		public AtsDefinitionPrinter(IUltimateServiceProvider services,
				String automatonName, String filename, Labeling labels, String message, Object... automata) {
			m_Services = services;
			s_Logger.warn("Dumping Testfile");
			initializePrintWriter(filename);
			m_printWriter.println("// Testfile dumped by Ultimate at "+getDateTime());
			m_printWriter.println("//");
			m_printWriter.println("// " + message);
			m_printWriter.println("");
			if (automata.length == 1) {
				printAutomaton(automatonName, automata[0], labels);
			}
			for (int i=0; i< automata.length; i++) {
				printAutomaton(automatonName + String.valueOf(i), automata[i], labels);
			}
		}
		
		
		public AtsDefinitionPrinter(IUltimateServiceProvider services, String name, Object automaton) {
			m_Services = services;
			m_StringWriter = new StringWriter();
			m_printWriter = new PrintWriter(m_StringWriter);
			printAutomaton(name, automaton, Labeling.TOSTRING);
		}
		
		public String getDefinitionAsString() {
			if (m_StringWriter == null) {
				throw new AssertionError("only available with different constructor");
			}
			m_StringWriter.flush();
			return m_StringWriter.toString();
		}
		
		
		@SuppressWarnings("unchecked")
		private void printAutomaton(String name, Object automaton, Labeling labels) {
			if (automaton instanceof INestedWordAutomatonSimple) {
				INestedWordAutomaton<LETTER,STATE> nwa;
				if (automaton instanceof INestedWordAutomaton) {
					nwa = (INestedWordAutomaton<LETTER, STATE>) automaton;
				} else {
					try {
						nwa = new NestedWordAutomatonReachableStates<LETTER, STATE>(m_Services, (INestedWordAutomatonSimple<LETTER, STATE>) automaton);
					} catch (OperationCanceledException e) {
						throw new AssertionError("Timeout while preparing automaton for printing.");
					}
				}
					
				if (labels == Labeling.TOSTRING) {
					new NwaTestFileWriterToString(name, nwa);
				} else if (labels == Labeling.QUOTED) {
					new NwaTestFileWriterToStringWithHash(name, nwa);
				
				} else if (labels == Labeling.NUMERATE) {
					new NwaTestFileWriter(name, nwa);
				} else if (labels == Labeling.BA_FORMAT) {
					new BaFormatWriter(nwa);
				}
				
				else {
					throw new AssertionError("unsupported labeling");
				}
			}
			
			else if (automaton instanceof IPetriNet) {
				IPetriNet<LETTER,STATE> net = (IPetriNet<LETTER,STATE>) automaton;
				if (labels == Labeling.TOSTRING) {
					new NetTestFileWriterToString(net);
				} else if (labels == Labeling.QUOTED) {
					new NetTestFileWriterToStringWithUniqueNumber(net);
				
				} else if (labels == Labeling.NUMERATE) {
					new NetTestFileWriter(net);
				} else {
					throw new AssertionError("unsupported labeling");
				}
			}
			
			else if(automaton instanceof AlternatingAutomaton){
				AlternatingAutomaton<LETTER,STATE> aa = (AlternatingAutomaton<LETTER,STATE>) automaton;
				new AATestFileWriter(aa);
			}
			m_printWriter.close();
		}
		
		

	    private String getDateTime() {
	        DateFormat dateFormat = new SimpleDateFormat("yyyy/MM/dd HH:mm:ss");
	        Date date = new Date();
	        return dateFormat.format(date);
	    }
	    
 
		/**
		 * Constructor takes a NestedWordAutomaton and writes it to testfile.
		 */
		private class NwaTestFileWriter {

			INestedWordAutomaton<LETTER,STATE> m_Nwa;
			Map<LETTER, String> internalAlphabet;
			Map<LETTER, String> callAlphabet;
			Map<LETTER, String> returnAlphabet;
			Map<STATE, String> stateMapping;

			public NwaTestFileWriter(String name, INestedWordAutomaton<LETTER,STATE> nwa) {
				m_Nwa = nwa;
				internalAlphabet = getAlphabetMapping(nwa.getInternalAlphabet(), "a");
				callAlphabet = getAlphabetMapping(nwa.getCallAlphabet(), "c");
				returnAlphabet = getAlphabetMapping(nwa.getReturnAlphabet(), "r");
				stateMapping = getStateMapping(m_Nwa.getStates());

				m_printWriter.println("NestedWordAutomaton " + name + " = (");
				printAlphabetes();
				printStates();
				printInitialStates(m_Nwa.getInitialStates());
				printFinalStates(m_Nwa.getStates());
				printCallTransitions(m_Nwa.getStates());
				printInternalTransitions(m_Nwa.getStates());
				printReturnTransitions(m_Nwa.getStates());
				m_printWriter.println(");");
				m_printWriter.close();
			}

			protected Map<LETTER,String> getAlphabetMapping(Collection<LETTER> alphabet,
					String symbol) {
				Integer counter = 0;
				Map<LETTER,String> alphabetMapping = new HashMap<LETTER,String>();
				for (LETTER letter : alphabet) {
					alphabetMapping.put(letter, symbol + counter.toString());
					counter++;
				}
				return alphabetMapping;
			}

			protected Map<STATE,String> getStateMapping(Collection<STATE> states) {
				Integer counter = 0;
				Map<STATE,String> stateMapping = new HashMap<STATE,String>();
				for (STATE state : states) {
					stateMapping.put(state, "s" + counter.toString());
					counter++;
				}
				return stateMapping;
			}

			private void printAlphabetes() {
				m_printWriter.print('\t' + "callAlphabet = {");
				printAlphabet(callAlphabet);
				m_printWriter.print("},\n");

				m_printWriter.print('\t' + "internalAlphabet = {");
				printAlphabet(internalAlphabet);
				m_printWriter.print("},\n");

				m_printWriter.print('\t' + "returnAlphabet = {");
				printAlphabet(returnAlphabet);
				m_printWriter.print("},\n");
			}

			private void printAlphabet(Map<LETTER,String> alphabet) {
				for (LETTER letter : alphabet.keySet()) {
					m_printWriter.print(alphabet.get(letter) + " ");		
				}
			}

			private void printStates() {
				m_printWriter.print('\t' + "states = {");
				for (STATE state : stateMapping.keySet()) {
					m_printWriter.print(stateMapping.get(state) + " ");		
				}
				m_printWriter.print("},\n");
			}

			private void printInitialStates(Collection<STATE> initialStates) {
				m_printWriter.print('\t' + "initialStates = {");
				for (STATE state : initialStates) {
					m_printWriter.print(stateMapping.get(state) + " ");		
				}
				m_printWriter.print("},\n");
			}

			private void printFinalStates(Collection<STATE> allStates) {
				m_printWriter.print('\t' + "finalStates = {");
				for (STATE state : allStates) {
					if (m_Nwa.isFinal(state)) {
						m_printWriter.print(stateMapping.get(state) + " ");
					}
				}
				m_printWriter.print("},\n");
			}

			private void printCallTransitions(Collection<STATE> allStates) {
				m_printWriter.println('\t' + "callTransitions = {");
				for (STATE state : allStates) {
					for (OutgoingCallTransition<LETTER, STATE> outTrans : m_Nwa.callSuccessors(state)) {
						printCallTransition(state, outTrans);
					}
				}
				m_printWriter.println("\t},");
			}

			private void printInternalTransitions(Collection<STATE> allStates) {
				m_printWriter.println('\t' + "internalTransitions = {");
				for (STATE state : allStates) {
					for (OutgoingInternalTransition<LETTER, STATE> outTrans : m_Nwa.internalSuccessors(state)) {
						printInternalTransition(state, outTrans);
					}
				}
				m_printWriter.println("\t},");
			}

			private void printReturnTransitions(Collection<STATE> allStates) {
				m_printWriter.println('\t' + "returnTransitions = {");
				for (STATE state : allStates) {
					for (OutgoingReturnTransition<LETTER, STATE> outTrans : m_Nwa.returnSuccessors(state)) {
						printReturnTransition(state, outTrans);
					}
				}
				m_printWriter.println("\t}");
			}


			private void printCallTransition(STATE state, OutgoingCallTransition<LETTER, STATE> callTrans) {
				m_printWriter.println("\t\t (" +
						stateMapping.get(state) + " " +
						callAlphabet.get(callTrans.getLetter()) + " " +
						stateMapping.get(callTrans.getSucc()) + ")"
				);
			}

			private void printInternalTransition(STATE state, OutgoingInternalTransition<LETTER, STATE> internalTrans) {
				m_printWriter.println("\t\t (" +
						stateMapping.get(state) + " " +
						internalAlphabet.get(internalTrans.getLetter()) + " " +
						stateMapping.get(internalTrans.getSucc()) + ")"
				);
			}

			private void printReturnTransition(STATE state, OutgoingReturnTransition<LETTER, STATE> returnTrans) {
				m_printWriter.println("\t\t (" +
						stateMapping.get(state) + " " +
						stateMapping.get(returnTrans.getHierPred()) + " " +
						returnAlphabet.get(returnTrans.getLetter()) + " " +
						stateMapping.get(returnTrans.getSucc()) + ")"
				);		
			}
		}
		
		
		
		/**
		 * Takes NestedWordAutomaton writes it to testfile. In this version
		 * letters and states are represented by their toString method.
		 */
		private class NwaTestFileWriterToString extends NwaTestFileWriter{

			public NwaTestFileWriterToString(String name, INestedWordAutomaton<LETTER,STATE> nwa) {
				super(name, nwa);
			}

			@Override
			protected Map<LETTER, String> getAlphabetMapping(Collection<LETTER> alphabet,
					String symbol) {
				Map<LETTER,String> alphabetMapping = new HashMap<LETTER,String>();
				for (LETTER letter : alphabet) {
					alphabetMapping.put(letter, "\"" + letter.toString().replaceAll("\"", "\\\"") + "\"");
				}
				return alphabetMapping;
			}

			@Override
			protected Map<STATE, String> getStateMapping(
					Collection<STATE> states) {
				Map<STATE,String> stateMapping = new HashMap<STATE,String>();
				for (STATE state : states) {
					stateMapping.put(state, "\"" + state.toString().replaceAll("\"", "\\\"") + "\"");
				}
				return stateMapping;
			}
		}
		
		
		/**
		 * Takes NestedWordAutomaton writes it to testfile. In this version
		 * letters and states are represented by their toString method.
		 */
		private class NwaTestFileWriterToStringWithHash extends NwaTestFileWriter{

			public NwaTestFileWriterToStringWithHash(String name, INestedWordAutomaton<LETTER,STATE> nwa) {
				super(name, nwa);
			}

			@Override
			protected Map<LETTER, String> getAlphabetMapping(Collection<LETTER> alphabet,
					String symbol) {
				Map<LETTER,String> alphabetMapping = new HashMap<LETTER,String>();
				for (LETTER letter : alphabet) {
					alphabetMapping.put(letter, "\"" + letter.toString().replaceAll("\"", "\\\"") + (letter.hashCode()/m_HashDivisor) + "\"");
				}
				return alphabetMapping;
			}

			@Override
			protected Map<STATE, String> getStateMapping(
					Collection<STATE> states) {
				Map<STATE,String> stateMapping = new HashMap<STATE,String>();
				for (STATE state : states) {
					stateMapping.put(state, "\"" + state.toString().replaceAll("\"", "\\\"") + (state.hashCode()/m_HashDivisor) + "\"");
				}
				return stateMapping;
			}
		}
		
		
		
		
		/**
		 * Constructor takes a PetriNet and writes it to a testfile.
		 */
		private class NetTestFileWriter {

			Map<LETTER, String> alphabet;
			Map<Place<LETTER,STATE>, String> placesMapping;

			public NetTestFileWriter(IPetriNet<LETTER,STATE> net) {
				alphabet = getAlphabetMapping(net.getAlphabet());
				placesMapping = getPlacesMapping(net.getPlaces());

				m_printWriter.println("PetriNet net = (");
				printAlphabet();
				printPlaces();
				printInternalTransitions(net.getTransitions());
				printInitialMarking(net.getInitialMarking());
				if (net instanceof PetriNetJulian) {
					printAcceptingPlaces(((PetriNetJulian<LETTER,STATE>) net).getAcceptingPlaces());
				}
				else {
					throw new IllegalArgumentException("unknown kinde of net");
				}
				m_printWriter.println(")");
				m_printWriter.close();
			}
			

			protected Map<LETTER,String> getAlphabetMapping(Collection<LETTER> alphabet) {
				Integer counter = 0;
				Map<LETTER,String> alphabetMapping = new HashMap<LETTER,String>();
				for (LETTER letter : alphabet) {
					alphabetMapping.put(letter, "a" + counter.toString());
					counter++;
				}
				return alphabetMapping;
			}
			
			protected Map<Place<LETTER, STATE>, String> getPlacesMapping(Collection<Place<LETTER,STATE>> places) {
				Integer counter = 0;
				HashMap<Place<LETTER,STATE>, String> placesMapping = new HashMap<Place<LETTER,STATE>,String>();
				for (Place<LETTER,STATE> place : places) {
					placesMapping.put(place, "p" + counter.toString());
					counter++;
				}
				return placesMapping;
			}
			
			private void printAlphabet() {
				m_printWriter.print('\t' + "alphabet = {");
				printAlphabet(alphabet);
				m_printWriter.print("},\n");
			}

			private void printAlphabet(Map<LETTER,String> alphabet) {
				for (LETTER letter : alphabet.keySet()) {
					m_printWriter.print(alphabet.get(letter) + " ");		
				}
			}
			
			private void printPlaces() {
				m_printWriter.print('\t' + "places = {");
				for (Place<LETTER,STATE> place : placesMapping.keySet()) {
					m_printWriter.print(placesMapping.get(place) + " ");		
				}
				m_printWriter.print("},\n");
			}
			
			private void printInternalTransitions(
					Collection<ITransition<LETTER,STATE>> transitions) {
				m_printWriter.println('\t' + "transitions = {");
				for (ITransition<LETTER,STATE> transition : transitions) {
					printTransition(transition);
				}
				m_printWriter.println("\t},");
			}

			private void printTransition(ITransition<LETTER,STATE> transition) {
				m_printWriter.print("\t\t( " );
				printMarking(transition.getPredecessors());
				m_printWriter.print(" " );
				m_printWriter.print(alphabet.get(transition.getSymbol()));
				m_printWriter.print(" " );
				printMarking(transition.getSuccessors());
				m_printWriter.print(" )\n" );
			}
			
			private void printMarking(Marking<LETTER,STATE> marking) {
				m_printWriter.print("{" );
				for (Place<LETTER,STATE> place : marking) {
					m_printWriter.print(placesMapping.get(place) + " ");
				}
				m_printWriter.print("}" );
			}
			
			private void printMarking(Collection<Place<LETTER,STATE>> marking) {
				m_printWriter.print("{" );
				for (Place<LETTER,STATE> place : marking) {
					m_printWriter.print(placesMapping.get(place) + " ");
				}
				m_printWriter.print("}" );
			}

			private void printInitialMarking(Marking<LETTER,STATE> initialMarking) {
				m_printWriter.print('\t' + "initialMarking = ");
				printMarking(initialMarking);
				m_printWriter.print(",\n");
			}
			
			private void printAcceptingPlaces(Collection<Place<LETTER,STATE>> acceptingPlaces) {
				m_printWriter.print('\t' + "acceptingPlaces = ");
				printMarking(acceptingPlaces);
				m_printWriter.print("\n");
			}


		}
		
		private class NetTestFileWriterToString extends NetTestFileWriter{

			public NetTestFileWriterToString(IPetriNet<LETTER,STATE> net) {
				super(net);

			}
			
			@Override
			protected Map<LETTER, String> getAlphabetMapping(Collection<LETTER> alphabet) {
				Map<LETTER,String> alphabetMapping = new HashMap<LETTER,String>();
				for (LETTER letter : alphabet) {
					alphabetMapping.put(letter, "\"" + letter.toString().replaceAll("\"", "\\\"") + "\"");
				}
				return alphabetMapping;
			}
			
			@Override
			protected Map<Place<LETTER,STATE>, String> getPlacesMapping(Collection<Place<LETTER,STATE>> places) {
				Integer counter = 0;
				HashMap<Place<LETTER,STATE>, String> placesMapping = new HashMap<Place<LETTER,STATE>,String>();
				for (Place<LETTER,STATE> place : places) {
					placesMapping.put(place, "\"" +place.toString().replaceAll("\"", "\\\"") + "\"");
					counter++;
				}
				return placesMapping;
			}
		}
		
		
		
		
		private class NetTestFileWriterToStringWithUniqueNumber extends NetTestFileWriter{

			public NetTestFileWriterToStringWithUniqueNumber(IPetriNet<LETTER,STATE> net) {
				super(net);

			}
			
			@Override
			protected Map<LETTER, String> getAlphabetMapping(Collection<LETTER> alphabet) {
				int counter = 0;
				Map<LETTER,String> alphabetMapping = new HashMap<LETTER,String>();
				for (LETTER letter : alphabet) {
					alphabetMapping.put(letter, "\"" + letter.toString().replaceAll("\"", "\\\"") + (counter++));
				}
				return alphabetMapping;
			}
			
			@Override
			protected Map<Place<LETTER,STATE>, String> getPlacesMapping(Collection<Place<LETTER,STATE>> places) {
				int counter = 0;
				HashMap<Place<LETTER,STATE>, String> placesMapping = new HashMap<Place<LETTER,STATE>,String>();
				for (Place<LETTER,STATE> place : places) {
					placesMapping.put(place, "\"" +place.toString().replaceAll("\"", "\\\"") + (counter++));
				}
				return placesMapping;
			}
		}
		
		/**
		 * Constructor takes a AlternatingAutomaton and writes it to a testfile.
		 */
		private class AATestFileWriter {
			
			AlternatingAutomaton<LETTER, STATE> m_Aa;

			public AATestFileWriter(AlternatingAutomaton<LETTER,STATE> aa) {
				
				m_Aa = aa;

				m_printWriter.println("Alternating Automaton aa = (");
				printAlphabet(m_Aa.getAlphabet());
				printExistentialStates(m_Aa.getExistentialStates());
				printUniversalStates(m_Aa.getUniversalStates());
				printInitialStates(m_Aa.getInitialStates());
				printFinalStates(m_Aa.getFinalStates());
				printInternalTransitions(m_Aa.getTransitionsMap());
				

				m_printWriter.println(")");
				m_printWriter.close();
			}
			
			private void printAlphabet(Set<LETTER> set) {
				m_printWriter.print('\t' + "alphabet = { ");
				for (LETTER letter : set) {
					m_printWriter.print(letter + " ");		
				}
				m_printWriter.print("},\n");
			}
			
			private void printExistentialStates(Set<STATE> set) {
				m_printWriter.print('\t' + "existentialStates = { ");
				for (STATE state : set) {
					m_printWriter.print(state + " ");		
				}
				m_printWriter.print("},\n");
			}
			
			private void printUniversalStates(Set<STATE> set) {
				m_printWriter.print('\t' + "universalStates = { ");
				for (STATE state : set) {
					m_printWriter.print(state + " ");		
				}
				m_printWriter.print("},\n");
			}
			
			private void printInitialStates(Set<STATE> set) {
				m_printWriter.print('\t' + "initialStates = { ");
				for (STATE state : set) {
					m_printWriter.print(state + " ");		
				}
				m_printWriter.print("},\n");
			}
			
			private void printFinalStates(Set<STATE> set) {
				m_printWriter.print('\t' + "finalStates = { ");
				for (STATE state : set) {
					m_printWriter.print(state + " ");		
				}
				m_printWriter.print("},\n");
			}
			
			private void printInternalTransitions(Map<STATE, Map<LETTER, Set<STATE>>> map) {
				m_printWriter.println('\t' + "internalTransitions = {");
				for (Entry<STATE, Map<LETTER, Set<STATE>>> entry : map.entrySet()) {
				    STATE pre = entry.getKey();
				    Map<LETTER, Set<STATE>> transitionsMap = entry.getValue();
				    if (transitionsMap != null) {// state has no outgoing transitions, so nothing has to be printed
				    	for (Entry<LETTER, Set<STATE>> entry1 : transitionsMap.entrySet()) {
					        LETTER letter = entry1.getKey();
					        Set<STATE> succStates = entry1.getValue();
					        for (STATE succ : succStates) {
					        	printInternalTransition(pre, letter, succ);
					        }
					        
					        
					    }
				    }
				    
				}
				m_printWriter.println("\t},");
			}
			
			private void printInternalTransition(STATE pre, LETTER letter,
					STATE succ) {
				m_printWriter.println("\t\t (" +
						pre + " " +
						letter + " " +
						succ + ")"
				);
			}

		}
		
		private class BaFormatWriter {

			public BaFormatWriter(INestedWordAutomaton<LETTER, STATE> nwa) {
				Map<LETTER, String> alphabetMapping = computeAlphabetMapping(nwa.getInternalAlphabet());
				Map<STATE, String> stateMapping = computeStateMapping(nwa.getStates());
				StringBuilder initStateSb = computeStateString(nwa.getInitialStates(), stateMapping);
				StringBuilder transSb = computeTransitionString(nwa, stateMapping, alphabetMapping);
				StringBuilder finalStateSb = computeStateString(nwa.getFinalStates(), stateMapping);
				m_printWriter.print(initStateSb);
				m_printWriter.print(transSb);
				m_printWriter.print(finalStateSb);
			}

			private StringBuilder computeStateString(
					Collection<STATE> initialStates,
					Map<STATE, String> stateMapping) {
				StringBuilder result = new StringBuilder();
				for (STATE state : initialStates) {
					result.append("[" + stateMapping.get(state) + "]" + System.lineSeparator());
				}
				return result;
			}
			
			private StringBuilder computeTransitionString(
					INestedWordAutomaton<LETTER, STATE> nwa,
					Map<STATE, String> stateMapping,
					Map<LETTER, String> alphabetMapping) {
				StringBuilder result = new StringBuilder();
				for (STATE state : nwa.getStates()) {
					for (OutgoingInternalTransition<LETTER, STATE> outTrans : nwa.internalSuccessors(state)) {
						result.append(
								alphabetMapping.get(outTrans.getLetter()) + 
								"," + 
								"[" + stateMapping.get(state) + "]" + 
								"->" +
								"[" + stateMapping.get(outTrans.getSucc()) + "]" +
								System.lineSeparator());
					}
				}
				return result;
			}

			
			
			protected Map<LETTER,String> computeAlphabetMapping(Collection<LETTER> alphabet) {
				Integer counter = 0;
				Map<LETTER,String> alphabetMapping = new HashMap<LETTER,String>();
				for (LETTER letter : alphabet) {
					alphabetMapping.put(letter, counter.toString());
					counter++;
				}
				return alphabetMapping;
			}

			protected Map<STATE,String> computeStateMapping(Collection<STATE> states) {
				Integer counter = 0;
				Map<STATE,String> stateMapping = new HashMap<STATE,String>();
				for (STATE state : states) {
					stateMapping.put(state, counter.toString());
					counter++;
				}
				return stateMapping;
			}
			
		}
		

	}


