/*
 * Copyright (C) 2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
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

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.alternating.AlternatingAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Place;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.PetriNetJulian;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;


/**
 * Writes an automaton definition in for a given automaton.
 * 
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

public class AutomatonDefinitionPrinter<LETTER,STATE> {

		public enum Format {
			/**
			 * Automata script.
			 * The toString() representation of LETTER and STATE is used.
			 */
			ATS("ats"),
			/**
			 * Automata script.
			 * The String representations of LETTER and STATE are ignored.
			 * The TestFileWriter introduces new names, e.g. the letters of 
			 * the alphabet are a0, ..., an.
			 */
			ATS_NUMERATE("ats"), 
			/**
			 * Automata script.
			 * The String representation of LETTER and STATE plus the hashcode() is used.
			 */
			ATS_QUOTED("ats"),
			/**
			 * The BA format, that is also used by some tools of Yu-Fang Chen.
			 */
			BA("ba"),
			/**
			 * (GOAL File Format) - The XML file format used by GOAL.
			 */
			GFF("gff"),
			/**
			 * The Hanoi Omega Automaton Format
			 */
			HOA("hoa");
			
			private final String m_FileEnding;
			
			private Format(String fileEnding) {
				m_FileEnding = fileEnding;
			}
			
			public String getFileEnding() {
				return m_FileEnding;
			}
		};
		
		private final IUltimateServiceProvider m_Services;
		private final Logger m_Logger;
		
		/**
		 * Print hash modulo this number to get shorter identifiers.
		 */
		private static int m_HashDivisor = 1;
		
		PrintWriter m_printWriter;
		
		StringWriter m_StringWriter;
		
		private void initializePrintWriter(String filename, Format format) {
			File testfile = new File(filename + "." + format.getFileEnding());
			try {
				FileWriter fileWriter = new FileWriter(testfile);
				m_printWriter = new PrintWriter(fileWriter);
			} catch (IOException e) {
				e.printStackTrace();
			} 
		}
		
		
		public AutomatonDefinitionPrinter(IUltimateServiceProvider services,
				String automatonName, String filename, Format format, String message, Object... automata) {
			m_Services = services;
			m_Logger = m_Services.getLoggingService().getLogger(LibraryIdentifiers.s_LibraryID);
			m_Logger.warn("Dumping Testfile");
			initializePrintWriter(filename, format);
			switch (format) {
			case ATS:
			case ATS_NUMERATE:
			case ATS_QUOTED:
				m_printWriter.println("// Testfile dumped by Ultimate at "+getDateTime());
				m_printWriter.println("//");
				m_printWriter.println("// " + message);
				m_printWriter.println("");
				break;
			case BA:
			case HOA:
			case GFF:
				// add nothing
				break;
			default:
				throw new AssertionError();
			}
			if (automata.length == 1) {
				printAutomaton(automatonName, automata[0], format);
			}
			for (int i=0; i< automata.length; i++) {
				printAutomaton(automatonName + String.valueOf(i), automata[i], format);
			}
		}
		
		
		public AutomatonDefinitionPrinter(IUltimateServiceProvider services, String name, Format format, Object automaton) {
			m_Services = services;
			m_Logger = m_Services.getLoggingService().getLogger(LibraryIdentifiers.s_LibraryID);
			m_StringWriter = new StringWriter();
			m_printWriter = new PrintWriter(m_StringWriter);
			printAutomaton(name, automaton, format);
		}
		
		public String getDefinitionAsString() {
			if (m_StringWriter == null) {
				throw new AssertionError("only available with different constructor");
			}
			m_StringWriter.flush();
			return m_StringWriter.toString();
		}
		
		
		@SuppressWarnings("unchecked")
		private void printAutomaton(String name, Object automaton, Format format) {
			if (automaton instanceof INestedWordAutomatonSimple) {
				INestedWordAutomaton<LETTER,STATE> nwa;
				if (automaton instanceof INestedWordAutomaton) {
					nwa = (INestedWordAutomaton<LETTER, STATE>) automaton;
				} else {
					try {
						nwa = new NestedWordAutomatonReachableStates<LETTER, STATE>(m_Services, (INestedWordAutomatonSimple<LETTER, STATE>) automaton);
					} catch (AutomataLibraryException e) {
						throw new AssertionError("Timeout while preparing automaton for printing.");
					}
				}
					
				if (format == Format.ATS) {
					new NwaTestFileWriterToString(name, nwa);
				} else if (format == Format.ATS_QUOTED) {
					new NwaTestFileWriterToStringWithHash(name, nwa);
				} else if (format == Format.ATS_NUMERATE) {
					new NwaTestFileWriter(name, nwa);
				} else if (format == Format.BA) {
					new BaFormatWriter(nwa);
				} else if (format == Format.HOA) {
					new HanoiFormatWriter(nwa);
				} else if (format == Format.GFF) {
					new GoalFormatWriter(nwa);
				} else {
					throw new AssertionError("unsupported labeling");
				}
			}
			
			else if (automaton instanceof IPetriNet) {
				IPetriNet<LETTER,STATE> net = (IPetriNet<LETTER,STATE>) automaton;
				if (format == Format.ATS) {
					new NetTestFileWriterToString(net);
				} else if (format == Format.ATS_QUOTED) {
					new NetTestFileWriterToStringWithUniqueNumber(net);
				
				} else if (format == Format.ATS_NUMERATE) {
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
				m_printWriter.println(m_Aa.toString());
//				printAlphabet(m_Aa.getAlphabet());
//				printExistentialStates(m_Aa.getExistentialStates());
//				printUniversalStates(m_Aa.getUniversalStates());
//				printInitialStates(m_Aa.getInitialStates());
//				printFinalStates(m_Aa.getFinalStates());
//				printInternalTransitions(m_Aa.getTransitionsMap());
				

				m_printWriter.println(")");
				m_printWriter.close();
			}
			
//			private void printAlphabet(Set<LETTER> set) {
//				m_printWriter.print('\t' + "alphabet = { ");
//				for (LETTER letter : set) {
//					m_printWriter.print(letter + " ");		
//				}
//				m_printWriter.print("},\n");
//			}
//			
//			private void printExistentialStates(Set<STATE> set) {
//				m_printWriter.print('\t' + "existentialStates = { ");
//				for (STATE state : set) {
//					m_printWriter.print(state + " ");		
//				}
//				m_printWriter.print("},\n");
//			}
//			
//			private void printUniversalStates(Set<STATE> set) {
//				m_printWriter.print('\t' + "universalStates = { ");
//				for (STATE state : set) {
//					m_printWriter.print(state + " ");		
//				}
//				m_printWriter.print("},\n");
//			}
//			
//			private void printInitialStates(Set<STATE> set) {
//				m_printWriter.print('\t' + "initialStates = { ");
//				for (STATE state : set) {
//					m_printWriter.print(state + " ");		
//				}
//				m_printWriter.print("},\n");
//			}
//			
//			private void printFinalStates(Set<STATE> set) {
//				m_printWriter.print('\t' + "finalStates = { ");
//				for (STATE state : set) {
//					m_printWriter.print(state + " ");		
//				}
//				m_printWriter.print("},\n");
//			}
//			
//			private void printInternalTransitions(Map<STATE, Map<LETTER, Set<STATE>>> map) {
//				m_printWriter.println('\t' + "internalTransitions = {");
//				for (Entry<STATE, Map<LETTER, Set<STATE>>> entry : map.entrySet()) {
//				    STATE pre = entry.getKey();
//				    Map<LETTER, Set<STATE>> transitionsMap = entry.getValue();
//				    if (transitionsMap != null) {// state has no outgoing transitions, so nothing has to be printed
//				    	for (Entry<LETTER, Set<STATE>> entry1 : transitionsMap.entrySet()) {
//					        LETTER letter = entry1.getKey();
//					        Set<STATE> succStates = entry1.getValue();
//					        for (STATE succ : succStates) {
//					        	printInternalTransition(pre, letter, succ);
//					        }
//					        
//					        
//					    }
//				    }
//				    
//				}
//				m_printWriter.println("\t},");
//			}
//			
//			private void printInternalTransition(STATE pre, LETTER letter,
//					STATE succ) {
//				m_printWriter.println("\t\t (" +
//						pre + " " +
//						letter + " " +
//						succ + ")"
//				);
//			}

		}
		
		private class AbstractWriter {
			
			protected final Map<LETTER, String> m_AlphabetMapping;
			protected final Map<STATE, String> m_StateMapping;
			protected final INestedWordAutomaton<LETTER, STATE> m_Nwa;

			public AbstractWriter(INestedWordAutomaton<LETTER, STATE> nwa) {
				m_AlphabetMapping = computeAlphabetMapping(nwa.getInternalAlphabet());
				m_StateMapping = computeStateMapping(nwa.getStates());
				m_Nwa = nwa;
			}
			
			private Map<LETTER,String> computeAlphabetMapping(Collection<LETTER> alphabet) {
				Integer counter = 0;
				Map<LETTER,String> alphabetMapping = new HashMap<LETTER,String>();
				for (LETTER letter : alphabet) {
					alphabetMapping.put(letter, counter.toString());
					counter++;
				}
				return alphabetMapping;
			}

			private Map<STATE,String> computeStateMapping(Collection<STATE> states) {
				Integer counter = 0;
				Map<STATE,String> stateMapping = new HashMap<STATE,String>();
				for (STATE state : states) {
					stateMapping.put(state, counter.toString());
					counter++;
				}
				return stateMapping;
			}
			
		}
		
		private class BaFormatWriter extends AbstractWriter {

			public BaFormatWriter(INestedWordAutomaton<LETTER, STATE> nwa) {
				super(nwa);
				doPrint();
			}

			protected void doPrint() {
				StringBuilder initStateSb = computeStateString(m_Nwa.getInitialStates(), m_StateMapping);
				StringBuilder transSb = computeTransitionString(m_Nwa, m_StateMapping, m_AlphabetMapping);
				StringBuilder finalStateSb = computeStateString(m_Nwa.getFinalStates(), m_StateMapping);
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

			
			

			
		}
		
		
		private class HanoiFormatWriter extends AbstractWriter {
			
			private final boolean m_UseLabels = false;
			private final Converter<LETTER> m_LetterConverterAP;

			public HanoiFormatWriter(INestedWordAutomaton<LETTER, STATE> nwa) {
				super(nwa);
				if (m_UseLabels) {
					m_LetterConverterAP = new ToStringConverter<LETTER>();
				} else {
					m_LetterConverterAP = new MapBasedConverter<LETTER, String>(m_AlphabetMapping, "");
				}
				doPrint();
			}

			protected void doPrint() {
				String header = constructHeader();
				m_printWriter.print(header);
				String bodyToken = "--BODY--";
				m_printWriter.print(bodyToken);
				m_printWriter.print(System.lineSeparator());
				String body = constructBody();
				m_printWriter.print(body);
				String endToken = "--END--";
				m_printWriter.print(endToken);
			}

			private String constructHeader() {
				StringBuilder sb = new StringBuilder();
				sb.append("HOA: v1");
				sb.append(System.lineSeparator());
				
				sb.append("States: " + m_Nwa.getStates().size());
				sb.append(System.lineSeparator());
				
				for (STATE state : m_Nwa.getInitialStates()) {
					sb.append("Start: " + m_StateMapping.get(state));
					sb.append(System.lineSeparator());
				}
				
				sb.append("AP: " + m_Nwa.getInternalAlphabet().size());
				for (LETTER letter : m_Nwa.getInternalAlphabet()) {
					sb.append(" \"" + m_LetterConverterAP.convert(letter) + "\"");
				}
				sb.append(System.lineSeparator());
				
				for (LETTER letter : m_Nwa.getInternalAlphabet()) {
					sb.append("Alias: @");
					sb.append(m_AlphabetMapping.get(letter));
					boolean firstOther = true;
					for (LETTER otherLetter : m_Nwa.getInternalAlphabet()) {
						if (firstOther) {
							firstOther = false;
						} else {
							sb.append(" &");
						}
						if (otherLetter == letter) {
							sb.append(" ");
							sb.append(m_AlphabetMapping.get(otherLetter));
						} else {
							sb.append(" !");
							sb.append(m_AlphabetMapping.get(otherLetter));

						}
					}
					sb.append(System.lineSeparator());
				}
				
				sb.append("Acceptance: 1 Inf(0)");
				sb.append(System.lineSeparator());
				
				
				sb.append("acc-name: Buchi");
				sb.append(System.lineSeparator());
				
				sb.append("tool: \"Ultimate Automata Library\"");
				sb.append(System.lineSeparator());
				
				return sb.toString();
			}
			
			private String constructBody() {
				StringBuilder sb = new StringBuilder();

				String accSig = "{0}";
				for (STATE state : m_Nwa.getStates()) {
					sb.append("State: " + m_StateMapping.get(state));
					if (m_UseLabels) {
						sb.append(" \"");
						sb.append(state);
						sb.append(" \"");
					}
					if (m_Nwa.isFinal(state)) {
						sb.append(" " + accSig);
					}
					sb.append(System.lineSeparator());
					for (LETTER letter : m_Nwa.lettersInternal(state)) {
						for (OutgoingInternalTransition<LETTER, STATE> tes : m_Nwa.internalSuccessors(state, letter)) {
							sb.append("[@");
							sb.append(m_AlphabetMapping.get(tes.getLetter()));
							sb.append("] ");
							sb.append(m_StateMapping.get(tes.getSucc()));
							sb.append(System.lineSeparator());
						}
					}
					
				}
				return sb.toString();
			}


		}
		
		
		
		
		private class GoalFormatWriter extends AbstractWriter {
			
			private final Converter<LETTER> m_LetterConverter;
			private final Converter<STATE> m_StateConverter;

			public GoalFormatWriter(INestedWordAutomaton<LETTER, STATE> nwa) {
				super(nwa);
				m_LetterConverter = new MapBasedConverter<LETTER, String>(m_AlphabetMapping, "");
				m_StateConverter = new MapBasedConverter<STATE, String>(m_StateMapping, "");
				doPrint();
			}

			protected void doPrint() {
				StringBuilder sb = new StringBuilder();
				sb.append("<?xml version=\"1.0\" encoding=\"UTF-8\" standalone=\"no\"?>");
				sb.append(System.lineSeparator());
				sb.append("<Structure label-on=\"Transition\" type=\"FiniteStateAutomaton\">");
				sb.append(System.lineSeparator());
				sb.append(constuctAlphabetSection());
				sb.append(constuctStateSection());
				sb.append(constuctInitialStateSection());
				sb.append(constuctTransitionSection());
				sb.append(constuctAcceptingStateSection());
				sb.append("</Structure>");
				sb.append(System.lineSeparator());
				m_printWriter.print(sb.toString());
			}
			
			private String constuctAlphabetSection() {
				StringBuilder sb = new StringBuilder();
				sb.append("\t");
				sb.append("<Alphabet type=\"Classical\">");
				sb.append(System.lineSeparator());
				for (LETTER letter : m_Nwa.getInternalAlphabet()) {
					sb.append("\t");
					sb.append("\t");
					sb.append("<Symbol>");
					sb.append(m_LetterConverter.convert(letter));
					sb.append("</Symbol>");
					sb.append(System.lineSeparator());
				}
				sb.append("\t");
				sb.append("</Alphabet>");
				sb.append(System.lineSeparator());
				return sb.toString();
			}
			
			private String constuctStateSection() {
				StringBuilder sb = new StringBuilder();
				sb.append("\t");
				sb.append("<StateSet>");
				sb.append(System.lineSeparator());
				for (STATE state : m_Nwa.getStates()) {
					sb.append("\t");
					sb.append("\t");
					sb.append("<State sid=\"");
					sb.append(m_StateConverter.convert(state));
					sb.append("\" />");
					sb.append(System.lineSeparator());
				}
				sb.append("\t");
				sb.append("</StateSet>");
				sb.append(System.lineSeparator());
				return sb.toString();
			}
			
			private String constuctInitialStateSection() {
				StringBuilder sb = new StringBuilder();
				sb.append("\t");
				sb.append("<InitialStateSet>");
				sb.append(System.lineSeparator());
				for (STATE state : m_Nwa.getInitialStates()) {
					sb.append("\t");
					sb.append("\t");
					sb.append("<StateID>");
					sb.append(m_StateConverter.convert(state));
					sb.append("</StateID>");
					sb.append(System.lineSeparator());
				}
				sb.append("\t");
				sb.append("</InitialStateSet>");
				sb.append(System.lineSeparator());
				return sb.toString();
			}
			
			private String constuctTransitionSection() {
				int tid = 0;
				StringBuilder sb = new StringBuilder();
				sb.append("\t");
				sb.append("<TransitionSet complete=\"false\">");
				sb.append(System.lineSeparator());
				for (STATE state : m_Nwa.getStates()) {
					for (OutgoingInternalTransition<LETTER, STATE> trans : m_Nwa.internalSuccessors(state)) {
						sb.append("\t");
						sb.append("\t");
						sb.append("<Transition tid=\"");
						sb.append(tid++);
						sb.append("\">");
						sb.append("<From>");
						sb.append(m_StateConverter.convert(state));
						sb.append("</From>");
						sb.append("<To>");
						sb.append(m_StateConverter.convert(trans.getSucc()));
						sb.append("</To>");
						sb.append("<Label>");
						sb.append(m_LetterConverter.convert(trans.getLetter()));
						sb.append("</Label>");
						sb.append("</Transition>");
						sb.append(System.lineSeparator());
					}
				}
				sb.append("\t");
				sb.append("</TransitionSet>");
				sb.append(System.lineSeparator());
				return sb.toString();
			}
			
			private String constuctAcceptingStateSection() {
				StringBuilder sb = new StringBuilder();
				sb.append("\t");
				sb.append("<Acc type=\"Buchi\">");
				sb.append(System.lineSeparator());
				for (STATE state : m_Nwa.getInitialStates()) {
					sb.append("\t");
					sb.append("\t");
					sb.append("<StateID>");
					sb.append(m_StateConverter.convert(state));
					sb.append("</StateID>");
					sb.append(System.lineSeparator());
				}
				sb.append("\t");
				sb.append("</Acc>");
				sb.append(System.lineSeparator());
				return sb.toString();
			}
		}
		
		
		
	private interface Converter<E> {
		public String convert(E elem);
	}
	
	private class ToStringConverter<E> implements Converter<E> {

		@Override
		public String convert(E elem) {
			return String.valueOf(elem);
		}
		
	}
	
	private class MapBasedConverter<E,V> implements Converter<E> {
		
		private final Map<E,V> m_Map;
		private final String m_Prefix;
		
		public MapBasedConverter(Map<E, V> map, String prefix) {
			super();
			m_Prefix = prefix;
			m_Map = map;
		}

		@Override
		public String convert(E elem) {
			V value = m_Map.get(elem);
			if (value == null) {
				throw new IllegalArgumentException("unknown element: " + elem);
			}
			return m_Prefix + String.valueOf(value);
		}
		
	}

}


