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

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Place;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.PetriNetJulian;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;


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

		public enum Labeling { NUMERATE, TOSTRING, QUOTED };
		
		private static Logger s_Logger = 
			UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);
		
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
		
		
		public AtsDefinitionPrinter(Object automaton, String filename, Labeling labels, String message) {
			s_Logger.warn("Dumping Testfile");
			initializePrintWriter(filename);
			m_printWriter.println("// Testfile dumped by Ultimate at "+getDateTime());
			m_printWriter.println("");
			m_printWriter.println(message);
			m_printWriter.println("");
			printAutomaton(automaton, labels);
		}
		
		
		public AtsDefinitionPrinter(Object automaton) {
			m_StringWriter = new StringWriter();
			m_printWriter = new PrintWriter(m_StringWriter);
			printAutomaton(automaton, Labeling.TOSTRING);
		}
		
		public String getDefinitionAsString() {
			if (m_StringWriter == null) {
				throw new AssertionError("only available with different constructor");
			}
			m_StringWriter.flush();
			return m_StringWriter.toString();
		}
		
		
		@SuppressWarnings("unchecked")
		private void printAutomaton(Object automaton, Labeling labels) {
			if (automaton instanceof INestedWordAutomatonOldApi) {
				INestedWordAutomatonOldApi<LETTER,STATE> nwa = (INestedWordAutomatonOldApi<LETTER,STATE>) automaton;
				if (labels == Labeling.TOSTRING) {
					new NwaTestFileWriterToString(nwa);
				}
				else if (labels == Labeling.QUOTED) {
					new NwaTestFileWriterToStringWithHash(nwa);
				
				}
				else if (labels == Labeling.NUMERATE) {
					new NwaTestFileWriter(nwa);
				}
			}
			else if (automaton instanceof IPetriNet) {
				IPetriNet<LETTER,STATE> net = (IPetriNet<LETTER,STATE>) automaton;
				if (labels == Labeling.TOSTRING) {
					new NetTestFileWriterToString(net);
				}
				else if (labels == Labeling.QUOTED) {
					new NetTestFileWriterToStringWithUniqueNumber(net);
				
				}
				else if (labels == Labeling.NUMERATE) {
					new NetTestFileWriter(net);
				}
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

			INestedWordAutomatonOldApi<LETTER,STATE> m_Nwa;
			Map<LETTER, String> internalAlphabet;
			Map<LETTER, String> callAlphabet;
			Map<LETTER, String> returnAlphabet;
			Map<STATE, String> stateMapping;

			public NwaTestFileWriter(INestedWordAutomatonOldApi<LETTER,STATE> nwa) {
				m_Nwa = nwa;
				internalAlphabet = getAlphabetMapping(nwa.getInternalAlphabet(), "a");
				callAlphabet = getAlphabetMapping(nwa.getCallAlphabet(), "c");
				returnAlphabet = getAlphabetMapping(nwa.getReturnAlphabet(), "r");
				stateMapping = getStateMapping(nwa.getStates());

				m_printWriter.println("NestedWordAutomaton nwa = (");
				printAlphabetes();
				printStates();
				printInitialStates(nwa.getInitialStates());
				printFinalStates(nwa.getStates());
				printCallTransitions(nwa.getStates());
				printInternalTransitions(nwa.getStates());
				printReturnTransitions(nwa.getStates());
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
					for (LETTER letter : m_Nwa.lettersCall(state)) {
						for (STATE succ : m_Nwa.succCall(state, letter)) {
							printCallTransition(state,letter,succ);
						}
					}
				}
				m_printWriter.println("\t},");
			}

			private void printInternalTransitions(Collection<STATE> allStates) {
				m_printWriter.println('\t' + "internalTransitions = {");
				for (STATE state : allStates) {
					for (LETTER letter : m_Nwa.lettersInternal(state)) {
						for (STATE succ : m_Nwa.succInternal(state, letter)) {
							printInternalTransition(state,letter,succ);
						}
					}
				}
				m_printWriter.println("\t},");
			}

			private void printReturnTransitions(Collection<STATE> allStates) {
				m_printWriter.println('\t' + "returnTransitions = {");
				for (STATE state : allStates) {
					for (LETTER letter : m_Nwa.lettersReturn(state)) {
						for (STATE hierPred : m_Nwa.hierPred(state, letter)) {
							for (STATE succ : m_Nwa.succReturn(state, hierPred, letter)) {
								printReturnTransition(state,hierPred,letter,succ);
							}
						}
					}
				}
				m_printWriter.println("\t}");
			}


			private void printCallTransition(STATE state, LETTER letter,
					STATE succ) {
				m_printWriter.println("\t\t (" +
						stateMapping.get(state) + " " +
						callAlphabet.get(letter) + " " +
						stateMapping.get(succ) + ")"
				);
			}

			private void printInternalTransition(STATE state, LETTER letter,
					STATE succ) {
				m_printWriter.println("\t\t (" +
						stateMapping.get(state) + " " +
						internalAlphabet.get(letter) + " " +
						stateMapping.get(succ) + ")"
				);
			}

			private void printReturnTransition(STATE state,
					STATE linPred, LETTER letter, STATE succ) {
				m_printWriter.println("\t\t (" +
						stateMapping.get(state) + " " +
						stateMapping.get(linPred) + " " +
						returnAlphabet.get(letter) + " " +
						stateMapping.get(succ) + ")"
				);		
			}
		}
		
		
		
		/**
		 * Takes NestedWordAutomaton writes it to testfile. In this version
		 * letters and states are represented by their toString method.
		 */
		private class NwaTestFileWriterToString extends NwaTestFileWriter{

			public NwaTestFileWriterToString(INestedWordAutomatonOldApi<LETTER,STATE> nwa) {
				super(nwa);
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

			public NwaTestFileWriterToStringWithHash(INestedWordAutomatonOldApi<LETTER,STATE> nwa) {
				super(nwa);
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
		

	}


