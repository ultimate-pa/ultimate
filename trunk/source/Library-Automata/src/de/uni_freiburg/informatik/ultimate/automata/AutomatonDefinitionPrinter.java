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
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;


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
			
			private final String mFileEnding;
			
			private Format(String fileEnding) {
				mFileEnding = fileEnding;
			}
			
			public String getFileEnding() {
				return mFileEnding;
			}
		};
		
		private final AutomataLibraryServices mServices;
		private final ILogger mLogger;
		
		/**
		 * Print hash modulo this number to get shorter identifiers.
		 */
		private static int mHashDivisor = 1;
		
		PrintWriter mprintWriter;
		
		StringWriter mStringWriter;
		
		private void initializePrintWriter(String filename, Format format) {
			File testfile = new File(filename + "." + format.getFileEnding());
			try {
				FileWriter fileWriter = new FileWriter(testfile);
				mprintWriter = new PrintWriter(fileWriter);
			} catch (IOException e) {
				e.printStackTrace();
			} 
		}
		
		
		public AutomatonDefinitionPrinter(AutomataLibraryServices services,
				String automatonName, String filename, Format format, String message, Object... automata) {
			mServices = services;
			mLogger = mServices.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
			mLogger.warn("Dumping Testfile");
			initializePrintWriter(filename, format);
			switch (format) {
			case ATS:
			case ATS_NUMERATE:
			case ATS_QUOTED:
				mprintWriter.println("// Testfile dumped by Ultimate at "+getDateTime());
				mprintWriter.println("//");
				mprintWriter.println("// " + message);
				mprintWriter.println("");
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
		
		
		public AutomatonDefinitionPrinter(AutomataLibraryServices services, String name, Format format, Object automaton) {
			mServices = services;
			mLogger = mServices.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
			mStringWriter = new StringWriter();
			mprintWriter = new PrintWriter(mStringWriter);
			printAutomaton(name, automaton, format);
		}
		
		public String getDefinitionAsString() {
			if (mStringWriter == null) {
				throw new AssertionError("only available with different constructor");
			}
			mStringWriter.flush();
			return mStringWriter.toString();
		}
		
		
		@SuppressWarnings("unchecked")
		private void printAutomaton(String name, Object automaton, Format format) {
			if (automaton instanceof INestedWordAutomatonSimple) {
				INestedWordAutomaton<LETTER,STATE> nwa;
				if (automaton instanceof INestedWordAutomaton) {
					nwa = (INestedWordAutomaton<LETTER, STATE>) automaton;
				} else {
					try {
						nwa = new NestedWordAutomatonReachableStates<LETTER, STATE>(mServices, (INestedWordAutomatonSimple<LETTER, STATE>) automaton);
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
			mprintWriter.close();
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

			INestedWordAutomaton<LETTER,STATE> mNwa;
			Map<LETTER, String> internalAlphabet;
			Map<LETTER, String> callAlphabet;
			Map<LETTER, String> returnAlphabet;
			Map<STATE, String> stateMapping;

			public NwaTestFileWriter(String name, INestedWordAutomaton<LETTER,STATE> nwa) {
				mNwa = nwa;
				internalAlphabet = getAlphabetMapping(nwa.getInternalAlphabet(), "a");
				callAlphabet = getAlphabetMapping(nwa.getCallAlphabet(), "c");
				returnAlphabet = getAlphabetMapping(nwa.getReturnAlphabet(), "r");
				stateMapping = getStateMapping(mNwa.getStates());

				mprintWriter.println("NestedWordAutomaton " + name + " = (");
				printAlphabetes();
				printStates();
				printInitialStates(mNwa.getInitialStates());
				printFinalStates(mNwa.getStates());
				printCallTransitions(mNwa.getStates());
				printInternalTransitions(mNwa.getStates());
				printReturnTransitions(mNwa.getStates());
				mprintWriter.println(");");
				mprintWriter.close();
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
				mprintWriter.print('\t' + "callAlphabet = {");
				printAlphabet(callAlphabet);
				mprintWriter.print("},\n");

				mprintWriter.print('\t' + "internalAlphabet = {");
				printAlphabet(internalAlphabet);
				mprintWriter.print("},\n");

				mprintWriter.print('\t' + "returnAlphabet = {");
				printAlphabet(returnAlphabet);
				mprintWriter.print("},\n");
			}

			private void printAlphabet(Map<LETTER,String> alphabet) {
				for (LETTER letter : alphabet.keySet()) {
					mprintWriter.print(alphabet.get(letter) + " ");		
				}
			}

			private void printStates() {
				mprintWriter.print('\t' + "states = {");
				for (STATE state : stateMapping.keySet()) {
					mprintWriter.print(stateMapping.get(state) + " ");		
				}
				mprintWriter.print("},\n");
			}

			private void printInitialStates(Collection<STATE> initialStates) {
				mprintWriter.print('\t' + "initialStates = {");
				for (STATE state : initialStates) {
					mprintWriter.print(stateMapping.get(state) + " ");		
				}
				mprintWriter.print("},\n");
			}

			private void printFinalStates(Collection<STATE> allStates) {
				mprintWriter.print('\t' + "finalStates = {");
				for (STATE state : allStates) {
					if (mNwa.isFinal(state)) {
						mprintWriter.print(stateMapping.get(state) + " ");
					}
				}
				mprintWriter.print("},\n");
			}

			private void printCallTransitions(Collection<STATE> allStates) {
				mprintWriter.println('\t' + "callTransitions = {");
				for (STATE state : allStates) {
					for (OutgoingCallTransition<LETTER, STATE> outTrans : mNwa.callSuccessors(state)) {
						printCallTransition(state, outTrans);
					}
				}
				mprintWriter.println("\t},");
			}

			private void printInternalTransitions(Collection<STATE> allStates) {
				mprintWriter.println('\t' + "internalTransitions = {");
				for (STATE state : allStates) {
					for (OutgoingInternalTransition<LETTER, STATE> outTrans : mNwa.internalSuccessors(state)) {
						printInternalTransition(state, outTrans);
					}
				}
				mprintWriter.println("\t},");
			}

			private void printReturnTransitions(Collection<STATE> allStates) {
				mprintWriter.println('\t' + "returnTransitions = {");
				for (STATE state : allStates) {
					for (OutgoingReturnTransition<LETTER, STATE> outTrans : mNwa.returnSuccessors(state)) {
						printReturnTransition(state, outTrans);
					}
				}
				mprintWriter.println("\t}");
			}


			private void printCallTransition(STATE state, OutgoingCallTransition<LETTER, STATE> callTrans) {
				mprintWriter.println("\t\t (" +
						stateMapping.get(state) + " " +
						callAlphabet.get(callTrans.getLetter()) + " " +
						stateMapping.get(callTrans.getSucc()) + ")"
				);
			}

			private void printInternalTransition(STATE state, OutgoingInternalTransition<LETTER, STATE> internalTrans) {
				mprintWriter.println("\t\t (" +
						stateMapping.get(state) + " " +
						internalAlphabet.get(internalTrans.getLetter()) + " " +
						stateMapping.get(internalTrans.getSucc()) + ")"
				);
			}

			private void printReturnTransition(STATE state, OutgoingReturnTransition<LETTER, STATE> returnTrans) {
				mprintWriter.println("\t\t (" +
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
					alphabetMapping.put(letter, "\"" + letter.toString().replaceAll("\"", "\\\"") + (letter.hashCode()/mHashDivisor) + "\"");
				}
				return alphabetMapping;
			}

			@Override
			protected Map<STATE, String> getStateMapping(
					Collection<STATE> states) {
				Map<STATE,String> stateMapping = new HashMap<STATE,String>();
				for (STATE state : states) {
					stateMapping.put(state, "\"" + state.toString().replaceAll("\"", "\\\"") + (state.hashCode()/mHashDivisor) + "\"");
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

				mprintWriter.println("PetriNet net = (");
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
				mprintWriter.println(")");
				mprintWriter.close();
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
				mprintWriter.print('\t' + "alphabet = {");
				printAlphabet(alphabet);
				mprintWriter.print("},\n");
			}

			private void printAlphabet(Map<LETTER,String> alphabet) {
				for (LETTER letter : alphabet.keySet()) {
					mprintWriter.print(alphabet.get(letter) + " ");		
				}
			}
			
			private void printPlaces() {
				mprintWriter.print('\t' + "places = {");
				for (Place<LETTER,STATE> place : placesMapping.keySet()) {
					mprintWriter.print(placesMapping.get(place) + " ");		
				}
				mprintWriter.print("},\n");
			}
			
			private void printInternalTransitions(
					Collection<ITransition<LETTER,STATE>> transitions) {
				mprintWriter.println('\t' + "transitions = {");
				for (ITransition<LETTER,STATE> transition : transitions) {
					printTransition(transition);
				}
				mprintWriter.println("\t},");
			}

			private void printTransition(ITransition<LETTER,STATE> transition) {
				mprintWriter.print("\t\t( " );
				printMarking(transition.getPredecessors());
				mprintWriter.print(" " );
				mprintWriter.print(alphabet.get(transition.getSymbol()));
				mprintWriter.print(" " );
				printMarking(transition.getSuccessors());
				mprintWriter.print(" )\n" );
			}
			
			private void printMarking(Marking<LETTER,STATE> marking) {
				mprintWriter.print("{" );
				for (Place<LETTER,STATE> place : marking) {
					mprintWriter.print(placesMapping.get(place) + " ");
				}
				mprintWriter.print("}" );
			}
			
			private void printMarking(Collection<Place<LETTER,STATE>> marking) {
				mprintWriter.print("{" );
				for (Place<LETTER,STATE> place : marking) {
					mprintWriter.print(placesMapping.get(place) + " ");
				}
				mprintWriter.print("}" );
			}

			private void printInitialMarking(Marking<LETTER,STATE> initialMarking) {
				mprintWriter.print('\t' + "initialMarking = ");
				printMarking(initialMarking);
				mprintWriter.print(",\n");
			}
			
			private void printAcceptingPlaces(Collection<Place<LETTER,STATE>> acceptingPlaces) {
				mprintWriter.print('\t' + "acceptingPlaces = ");
				printMarking(acceptingPlaces);
				mprintWriter.print("\n");
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
			
			AlternatingAutomaton<LETTER, STATE> mAa;

			public AATestFileWriter(AlternatingAutomaton<LETTER,STATE> aa) {
				
				mAa = aa;

				mprintWriter.println("Alternating Automaton aa = (");
				mprintWriter.println(mAa.toString());
//				printAlphabet(mAa.getAlphabet());
//				printExistentialStates(mAa.getExistentialStates());
//				printUniversalStates(mAa.getUniversalStates());
//				printInitialStates(mAa.getInitialStates());
//				printFinalStates(mAa.getFinalStates());
//				printInternalTransitions(mAa.getTransitionsMap());
				

				mprintWriter.println(")");
				mprintWriter.close();
			}
			
//			private void printAlphabet(Set<LETTER> set) {
//				mprintWriter.print('\t' + "alphabet = { ");
//				for (LETTER letter : set) {
//					mprintWriter.print(letter + " ");		
//				}
//				mprintWriter.print("},\n");
//			}
//			
//			private void printExistentialStates(Set<STATE> set) {
//				mprintWriter.print('\t' + "existentialStates = { ");
//				for (STATE state : set) {
//					mprintWriter.print(state + " ");		
//				}
//				mprintWriter.print("},\n");
//			}
//			
//			private void printUniversalStates(Set<STATE> set) {
//				mprintWriter.print('\t' + "universalStates = { ");
//				for (STATE state : set) {
//					mprintWriter.print(state + " ");		
//				}
//				mprintWriter.print("},\n");
//			}
//			
//			private void printInitialStates(Set<STATE> set) {
//				mprintWriter.print('\t' + "initialStates = { ");
//				for (STATE state : set) {
//					mprintWriter.print(state + " ");		
//				}
//				mprintWriter.print("},\n");
//			}
//			
//			private void printFinalStates(Set<STATE> set) {
//				mprintWriter.print('\t' + "finalStates = { ");
//				for (STATE state : set) {
//					mprintWriter.print(state + " ");		
//				}
//				mprintWriter.print("},\n");
//			}
//			
//			private void printInternalTransitions(Map<STATE, Map<LETTER, Set<STATE>>> map) {
//				mprintWriter.println('\t' + "internalTransitions = {");
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
//				mprintWriter.println("\t},");
//			}
//			
//			private void printInternalTransition(STATE pre, LETTER letter,
//					STATE succ) {
//				mprintWriter.println("\t\t (" +
//						pre + " " +
//						letter + " " +
//						succ + ")"
//				);
//			}

		}
		
		private class AbstractWriter {
			
			protected final Map<LETTER, String> mAlphabetMapping;
			protected final Map<STATE, String> mStateMapping;
			protected final INestedWordAutomaton<LETTER, STATE> mNwa;

			public AbstractWriter(INestedWordAutomaton<LETTER, STATE> nwa) {
				mAlphabetMapping = computeAlphabetMapping(nwa.getInternalAlphabet());
				mStateMapping = computeStateMapping(nwa.getStates());
				mNwa = nwa;
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
				StringBuilder initStateSb = computeStateString(mNwa.getInitialStates(), mStateMapping);
				StringBuilder transSb = computeTransitionString(mNwa, mStateMapping, mAlphabetMapping);
				StringBuilder finalStateSb = computeStateString(mNwa.getFinalStates(), mStateMapping);
				mprintWriter.print(initStateSb);
				mprintWriter.print(transSb);
				mprintWriter.print(finalStateSb);
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
			
			private final boolean mUseLabels = false;
			private final Converter<LETTER> mLetterConverterAP;

			public HanoiFormatWriter(INestedWordAutomaton<LETTER, STATE> nwa) {
				super(nwa);
				if (mUseLabels) {
					mLetterConverterAP = new ToStringConverter<LETTER>();
				} else {
					mLetterConverterAP = new MapBasedConverter<LETTER, String>(mAlphabetMapping, "");
				}
				doPrint();
			}

			protected void doPrint() {
				String header = constructHeader();
				mprintWriter.print(header);
				String bodyToken = "--BODY--";
				mprintWriter.print(bodyToken);
				mprintWriter.print(System.lineSeparator());
				String body = constructBody();
				mprintWriter.print(body);
				String endToken = "--END--";
				mprintWriter.print(endToken);
			}

			private String constructHeader() {
				StringBuilder sb = new StringBuilder();
				sb.append("HOA: v1");
				sb.append(System.lineSeparator());
				
				sb.append("States: " + mNwa.getStates().size());
				sb.append(System.lineSeparator());
				
				for (STATE state : mNwa.getInitialStates()) {
					sb.append("Start: " + mStateMapping.get(state));
					sb.append(System.lineSeparator());
				}
				
				sb.append("AP: " + mNwa.getInternalAlphabet().size());
				for (LETTER letter : mNwa.getInternalAlphabet()) {
					sb.append(" \"p" + mLetterConverterAP.convert(letter) + "\"");
				}
				sb.append(System.lineSeparator());
				
				for (LETTER letter : mNwa.getInternalAlphabet()) {
					sb.append("Alias: @");
					sb.append(mAlphabetMapping.get(letter));
					boolean firstOther = true;
					for (LETTER otherLetter : mNwa.getInternalAlphabet()) {
						if (firstOther) {
							firstOther = false;
						} else {
							sb.append(" &");
						}
						if (otherLetter == letter) {
							sb.append(" ");
							sb.append(mAlphabetMapping.get(otherLetter));
						} else {
							sb.append(" !");
							sb.append(mAlphabetMapping.get(otherLetter));

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
				for (STATE state : mNwa.getStates()) {
					sb.append("State: " + mStateMapping.get(state));
					if (mUseLabels) {
						sb.append(" \"");
						sb.append(state);
						sb.append(" \"");
					}
					if (mNwa.isFinal(state)) {
						sb.append(" " + accSig);
					}
					sb.append(System.lineSeparator());
					for (LETTER letter : mNwa.lettersInternal(state)) {
						for (OutgoingInternalTransition<LETTER, STATE> tes : mNwa.internalSuccessors(state, letter)) {
							sb.append("[@");
							sb.append(mAlphabetMapping.get(tes.getLetter()));
							sb.append("] ");
							sb.append(mStateMapping.get(tes.getSucc()));
							sb.append(System.lineSeparator());
						}
					}
					
				}
				return sb.toString();
			}


		}
		
		
		
		
		private class GoalFormatWriter extends AbstractWriter {
			
			private final Converter<LETTER> mLetterConverter;
			private final Converter<STATE> mStateConverter;

			public GoalFormatWriter(INestedWordAutomaton<LETTER, STATE> nwa) {
				super(nwa);
				mLetterConverter = new MapBasedConverter<LETTER, String>(mAlphabetMapping, "");
				mStateConverter = new MapBasedConverter<STATE, String>(mStateMapping, "");
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
				mprintWriter.print(sb.toString());
			}
			
			private String constuctAlphabetSection() {
				StringBuilder sb = new StringBuilder();
				sb.append("\t");
				sb.append("<Alphabet type=\"Classical\">");
				sb.append(System.lineSeparator());
				for (LETTER letter : mNwa.getInternalAlphabet()) {
					sb.append("\t");
					sb.append("\t");
					sb.append("<Symbol>");
					sb.append(mLetterConverter.convert(letter));
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
				for (STATE state : mNwa.getStates()) {
					sb.append("\t");
					sb.append("\t");
					sb.append("<State sid=\"");
					sb.append(mStateConverter.convert(state));
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
				for (STATE state : mNwa.getInitialStates()) {
					sb.append("\t");
					sb.append("\t");
					sb.append("<StateID>");
					sb.append(mStateConverter.convert(state));
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
				for (STATE state : mNwa.getStates()) {
					for (OutgoingInternalTransition<LETTER, STATE> trans : mNwa.internalSuccessors(state)) {
						sb.append("\t");
						sb.append("\t");
						sb.append("<Transition tid=\"");
						sb.append(tid++);
						sb.append("\">");
						sb.append("<From>");
						sb.append(mStateConverter.convert(state));
						sb.append("</From>");
						sb.append("<To>");
						sb.append(mStateConverter.convert(trans.getSucc()));
						sb.append("</To>");
						sb.append("<Label>");
						sb.append(mLetterConverter.convert(trans.getLetter()));
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
				for (STATE state : mNwa.getFinalStates()) {
					sb.append("\t");
					sb.append("\t");
					sb.append("<StateID>");
					sb.append(mStateConverter.convert(state));
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
		
		private final Map<E,V> mMap;
		private final String mPrefix;
		
		public MapBasedConverter(Map<E, V> map, String prefix) {
			super();
			mPrefix = prefix;
			mMap = map;
		}

		@Override
		public String convert(E elem) {
			V value = mMap.get(elem);
			if (value == null) {
				throw new IllegalArgumentException("unknown element: " + elem);
			}
			return mPrefix + String.valueOf(value);
		}
		
	}

}


