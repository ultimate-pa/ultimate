package de.uni_freiburg.informatik.ultimate.automata;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.text.DateFormat;
import java.text.SimpleDateFormat;
import java.util.Collection;
import java.util.Date;
import java.util.HashMap;
import java.util.Map;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Place;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.PetriNetJulian;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;

/**
 * Writes an automaton definition in the .fat format for a given automaton.
 * if Labeling == NUMERATE
 * The String representation of Symbol and Content is used.
 * if Labeling == TOSTRING
 * A quoted String representation of Symbol and Content is used.
 * if Labeling == QUOTED
 * The String representations of Symbol and Content are ignored.
 * The TestFileWriter introduces new names, e.g. the symbols of the alphabet are
 * a0, ..., an.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <S> Symbol
 * @param <C> Content
 */
public class TestFileWriter<S,C> {
	
	public enum Labeling { NUMERATE, TOSTRING, QUOTED };
	
	private static Logger s_Logger = 
		UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);
	
	/**
	 * Print hash modulo this number to get shorter identifiers.
	 */
	private static int m_HashDivisor = 1;
	
	PrintWriter m_printWriter;
	
	private void initializePrintWriter(String filename) {
		File testfile = new File(filename + ".fat");
		try {
			FileWriter fileWriter = new FileWriter(testfile);
			m_printWriter = new PrintWriter(fileWriter);
		} catch (IOException e) {
			e.printStackTrace();
		} 
	}
	
	@SuppressWarnings("unchecked")
	@Deprecated
	public TestFileWriter(Object automaton) {
		initializePrintWriter("dumpedTestfile");
		m_printWriter.println("// Testfile dumped by Ultimate at "+getDateTime());
		m_printWriter.println("");
		if (automaton instanceof NestedWordAutomaton) {
			NestedWordAutomaton<S,C> nwa = (NestedWordAutomaton<S,C>) automaton;
			new NwaTestFileWriter(nwa);
		}
		else if (automaton instanceof PetriNetJulian) {
			PetriNetJulian<S,C> net = (PetriNetJulian<S,C>) automaton;
			new NetTestFileWriter(net);
		} 
		m_printWriter.close();
	}
	
	@SuppressWarnings("unchecked")
	public TestFileWriter(Object automaton, String filename, Labeling labels, String message) {
		s_Logger.warn("Dumping Testfile");
		initializePrintWriter(filename);
		m_printWriter.println("// Testfile dumped by Ultimate at "+getDateTime());
		m_printWriter.println("");
		m_printWriter.println(message);
		m_printWriter.println("");
		if (automaton instanceof NestedWordAutomaton) {
			NestedWordAutomaton<S,C> nwa = (NestedWordAutomaton<S,C>) automaton;
			if (labels == Labeling.TOSTRING) {
				new NwaTestFileWriterToString(nwa);
			}
			else if (labels == Labeling.QUOTED) {
				new NwaTestFileWriterToStringQuote(nwa);
			
			}
			else if (labels == Labeling.NUMERATE) {
				new NwaTestFileWriter(nwa);
			}
		}
		else if (automaton instanceof IPetriNet) {
			IPetriNet<S,C> net = (IPetriNet<S,C>) automaton;
			if (labels == Labeling.TOSTRING) {
				new NetTestFileWriterToString(net);
			}
			else if (labels == Labeling.QUOTED) {
				new NetTestFileWriterToStringQuote(net);
			
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
     * Copied from SMTInterface.
     */
    
	public static String quoteId(String id) {
		StringBuilder sb = new StringBuilder();
		char c = id.charAt(0); 
		for (int i = 0; i < id.length(); i++) {
			c = id.charAt(i);
			if ((c >= '0' && c <= '9') || (c >= 'A' && c <= 'Z') 
					|| (c >= 'a' && c <= 'z'))
				sb.append(c);
			else if (c == '_')
				sb.append("__");
			else if (c == '\'')
				sb.append("_q");
			else if (c == '!')
				sb.append("_b");
			else if (c == '$')
				sb.append("_d");
			else if (c == '~')
				sb.append("_s");
			else if (c == '?')
				sb.append("_x");
			else if (c == '#')
				sb.append("_h");
			else if (c == '.')
				sb.append("_p");
			else
				sb.append('_').append(Integer.toHexString(c)).append('_');
		}
		return sb.toString();
	}
	

    
	/**
	 * Constructor takes a NestedWordAutomaton and writes it to testfile.
	 */
	private class NwaTestFileWriter {

		INestedWordAutomaton<S, C> m_Nwa;
		Map<S, String> internalAlphabet;
		Map<S, String> callAlphabet;
		Map<S, String> returnAlphabet;
		Map<C, String> stateMapping;

		public NwaTestFileWriter(NestedWordAutomaton<S,C> nwa) {
			m_Nwa = nwa;
			internalAlphabet = getAlphabetMapping(nwa.getInternalAlphabet(), "a");
			callAlphabet = getAlphabetMapping(nwa.getCallAlphabet(), "c");
			returnAlphabet = getAlphabetMapping(nwa.getReturnAlphabet(), "r");
			stateMapping = getStateMapping(nwa.getStates());

			m_printWriter.println("#Print nwa");
			m_printWriter.println("");
			m_printWriter.println("#nwa nwa := (");
			printAlphabetes();
			printStates();
			printInitialStates(nwa.getInitialStates());
			printFinalStates(nwa.getStates());
			printCallTransitions(nwa.getStates());
			printInternalTransitions(nwa.getStates());
			printReturnTransitions(nwa.getStates());
			m_printWriter.println(")");
			m_printWriter.close();
		}

		protected Map<S,String> getAlphabetMapping(Collection<S> alphabet,
				String letter) {
			Integer counter = 0;
			Map<S,String> alphabetMapping = new HashMap<S,String>();
			for (S symbol : alphabet) {
				alphabetMapping.put(symbol, letter + counter.toString());
				counter++;
			}
			return alphabetMapping;
		}

		protected Map<C,String> getStateMapping(Collection<C> states) {
			Integer counter = 0;
			Map<C,String> stateMapping = new HashMap<C,String>();
			for (C state : states) {
				stateMapping.put(state, "s" + counter.toString());
				counter++;
			}
			return stateMapping;
		}

		private void printAlphabetes() {
			m_printWriter.print('\t' + "#callAlphabet := {");
			printAlphabet(callAlphabet);
			m_printWriter.print("},\n");

			m_printWriter.print('\t' + "#internalAlphabet := {");
			printAlphabet(internalAlphabet);
			m_printWriter.print("},\n");

			m_printWriter.print('\t' + "#returnAlphabet := {");
			printAlphabet(returnAlphabet);
			m_printWriter.print("},\n");
		}

		private void printAlphabet(Map<S,String> alphabet) {
			for (S symbol : alphabet.keySet()) {
				m_printWriter.print(alphabet.get(symbol) + " ");		
			}
		}

		private void printStates() {
			m_printWriter.print('\t' + "#states := {");
			for (C state : stateMapping.keySet()) {
				m_printWriter.print(stateMapping.get(state) + " ");		
			}
			m_printWriter.print("},\n");
		}

		private void printInitialStates(Collection<C> initialStates) {
			m_printWriter.print('\t' + "#initialStates := {");
			for (C state : initialStates) {
				m_printWriter.print(stateMapping.get(state) + " ");		
			}
			m_printWriter.print("},\n");
		}

		private void printFinalStates(Collection<C> allStates) {
			m_printWriter.print('\t' + "#finalStates := {");
			for (C state : allStates) {
				if (m_Nwa.isFinal(state)) {
					m_printWriter.print(stateMapping.get(state) + " ");
				}
			}
			m_printWriter.print("},\n");
		}

		private void printCallTransitions(Collection<C> allStates) {
			m_printWriter.println('\t' + "#callTransitions := {");
			for (C state : allStates) {
				for (S symbol : m_Nwa.lettersCall(state)) {
					for (C succ : m_Nwa.succCall(state, symbol)) {
						printCallTransition(state,symbol,succ);
					}
				}
			}
			m_printWriter.println("\t},");
		}

		private void printInternalTransitions(Collection<C> allStates) {
			m_printWriter.println('\t' + "#internalTransitions := {");
			for (C state : allStates) {
				for (S symbol : m_Nwa.lettersInternal(state)) {
					for (C succ : m_Nwa.succInternal(state, symbol)) {
						printInternalTransition(state,symbol,succ);
					}
				}
			}
			m_printWriter.println("\t},");
		}

		private void printReturnTransitions(Collection<C> allStates) {
			m_printWriter.println('\t' + "#returnTransitions := {");
			for (C state : allStates) {
				for (S symbol : m_Nwa.lettersReturn(state)) {
					for (C hierPred : m_Nwa.hierPred(state, symbol)) {
						for (C succ : m_Nwa.succReturn(state, hierPred, symbol)) {
							printReturnTransition(state,hierPred,symbol,succ);
						}
					}
				}
			}
			m_printWriter.println("\t}");
		}


		private void printCallTransition(C state, S symbol,
				C succ) {
			m_printWriter.println("\t\t (" +
					stateMapping.get(state) + " " +
					callAlphabet.get(symbol) + " " +
					stateMapping.get(succ) + ")"
			);
		}

		private void printInternalTransition(C state, S symbol,
				C succ) {
			m_printWriter.println("\t\t (" +
					stateMapping.get(state) + " " +
					internalAlphabet.get(symbol) + " " +
					stateMapping.get(succ) + ")"
			);
		}

		private void printReturnTransition(C state,
				C linPred, S symbol, C succ) {
			m_printWriter.println("\t\t (" +
					stateMapping.get(state) + " " +
					stateMapping.get(linPred) + " " +
					returnAlphabet.get(symbol) + " " +
					stateMapping.get(succ) + ")"
			);		
		}
	}
	
	
	
	/**
	 * Takes NestedWordAutomaton writes it to testfile. In this version
	 * symbols and states are represented by their toString method.
	 */
	private class NwaTestFileWriterToString extends NwaTestFileWriter{

		public NwaTestFileWriterToString(NestedWordAutomaton<S, C> nwa) {
			super(nwa);
		}

		@Override
		protected Map<S, String> getAlphabetMapping(Collection<S> alphabet,
				String letter) {
			Map<S,String> alphabetMapping = new HashMap<S,String>();
			for (S symbol : alphabet) {
				alphabetMapping.put(symbol, "\"" + symbol.toString() + (symbol.hashCode()/m_HashDivisor) + "\"");
			}
			return alphabetMapping;
		}

		@Override
		protected Map<C, String> getStateMapping(
				Collection<C> states) {
			Map<C,String> stateMapping = new HashMap<C,String>();
			for (C state : states) {
				stateMapping.put(state, "\"" + state.toString() + (state.hashCode()/m_HashDivisor) + "\"");
			}
			return stateMapping;
		}
	}
	
	
	/**
	 * Takes NestedWordAutomaton writes it to testfile. In this version
	 * symbols and states are represented by their toString method.
	 */
	private class NwaTestFileWriterToStringQuote extends NwaTestFileWriter{

		public NwaTestFileWriterToStringQuote(NestedWordAutomaton<S,C> nwa) {
			super(nwa);
		}

		@Override
		protected Map<S, String> getAlphabetMapping(Collection<S> alphabet,
				String letter) {
			Map<S,String> alphabetMapping = new HashMap<S,String>();
			for (S symbol : alphabet) {
				alphabetMapping.put(symbol, quoteId(symbol.toString()) +
						(symbol.hashCode()/100000));
			}
			return alphabetMapping;
		}

		@Override
		protected Map<C, String> getStateMapping(
				Collection<C> states) {
			Map<C,String> stateMapping = 
											new HashMap<C,String>();
			for (C state : states) {
				stateMapping.put(state, quoteId(state.toString()) + 
						(state.hashCode()/100000));
			}
			return stateMapping;
		}
	}
	
	
	
	
	/**
	 * Constructor takes a PetriNet and writes it to a testfile.
	 */
	private class NetTestFileWriter {

		Map<S, String> alphabet;
		Map<Place<S,C>, String> placesMapping;

		public NetTestFileWriter(IPetriNet<S, C> net) {
			alphabet = getAlphabetMapping(net.getAlphabet());
			placesMapping = getPlacesMapping(net.getPlaces());

			m_printWriter.println("#Print net");
			m_printWriter.println("");
			m_printWriter.println("#net net := (");
			printAlphabet();
			printPlaces();
			printInternalTransitions(net.getTransitions());
			printInitialMarking(net.getInitialMarking());
			if (net instanceof PetriNetJulian) {
				printAcceptingPlaces(((PetriNetJulian) net).getAcceptingPlaces());
			}
			else {
				throw new IllegalArgumentException("unknown kinde of net");
			}
			m_printWriter.println(")");
			m_printWriter.close();
		}
		

		protected Map<S,String> getAlphabetMapping(Collection<S> alphabet) {
			Integer counter = 0;
			Map<S,String> alphabetMapping = new HashMap<S,String>();
			for (S symbol : alphabet) {
				alphabetMapping.put(symbol, "a" + counter.toString());
				counter++;
			}
			return alphabetMapping;
		}
		
		protected HashMap<Place<S, C>, String> getPlacesMapping(Collection<Place<S,C>> places) {
			Integer counter = 0;
			HashMap<Place<S, C>, String> placesMapping = new HashMap<Place<S,C>,String>();
			for (Place<S,C> place : places) {
				placesMapping.put(place, "p" + counter.toString());
				counter++;
			}
			return placesMapping;
		}
		
		private void printAlphabet() {
			m_printWriter.print('\t' + "#alphabet := {");
			printAlphabet(alphabet);
			m_printWriter.print("},\n");
		}

		private void printAlphabet(Map<S,String> alphabet) {
			for (S symbol : alphabet.keySet()) {
				m_printWriter.print(alphabet.get(symbol) + " ");		
			}
		}
		
		private void printPlaces() {
			m_printWriter.print('\t' + "#places := {");
			for (Place<S, C> place : placesMapping.keySet()) {
				m_printWriter.print(placesMapping.get(place) + " ");		
			}
			m_printWriter.print("},\n");
		}
		
		private void printInternalTransitions(
				Collection<ITransition<S, C>> transitions) {
			m_printWriter.println('\t' + "#transitions := {");
			for (ITransition<S,C> transition : transitions) {
				printTransition(transition);
			}
			m_printWriter.println("\t},");
		}

		private void printTransition(ITransition<S, C> transition) {
			m_printWriter.print("\t\t( " );
			printMarking(transition.getPredecessors());
			m_printWriter.print(" " );
			m_printWriter.print(alphabet.get(transition.getSymbol()));
			m_printWriter.print(" " );
			printMarking(transition.getSuccessors());
			m_printWriter.print(" )\n" );
		}
		
		private void printMarking(Marking<S,C> marking) {
			m_printWriter.print("{" );
			for (Place<S,C> place : marking) {
				m_printWriter.print(placesMapping.get(place) + " ");
			}
			m_printWriter.print("}" );
		}
		
		private void printMarking(Collection<Place<S,C>> marking) {
			m_printWriter.print("{" );
			for (Place<S,C> place : marking) {
				m_printWriter.print(placesMapping.get(place) + " ");
			}
			m_printWriter.print("}" );
		}


		private void printInitialMarking(Marking<S,C> initialMarking) {
			m_printWriter.print('\t' + "#initialMarking := ");
			printMarking(initialMarking);
			m_printWriter.print(",\n");
		}
		
		
		private void printAcceptingPlaces(Collection<Place<S,C>> acceptingPlaces) {
			m_printWriter.print('\t' + "#acceptingPlaces := ");
			printMarking(acceptingPlaces);
			m_printWriter.print("\n");
		}


		private void printAcceptingMarkings(
				Collection<Collection<Place<S, C>>> acceptingMarkings) {
			m_printWriter.println('\t' + "#acceptingMarkings := {");
			for (Collection<Place<S, C>> marking : acceptingMarkings) {
				m_printWriter.print("\t\t");
				printMarking(marking);
				m_printWriter.print("\n");
			}
			m_printWriter.println("\t}");
		}
	}
	
	private class NetTestFileWriterToString extends NetTestFileWriter{

		public NetTestFileWriterToString(IPetriNet<S, C> net) {
			super(net);

		}
		
		@Override
		protected Map<S, String> getAlphabetMapping(Collection<S> alphabet) {
			Map<S,String> alphabetMapping = new HashMap<S,String>();
			for (S symbol : alphabet) {
				alphabetMapping.put(symbol, "\"" + symbol.toString() + 
						(symbol.hashCode()/100000) + "\"");
			}
			return alphabetMapping;
		}
		
		@Override
		protected HashMap<Place<S, C>, String> getPlacesMapping(Collection<Place<S,C>> places) {
			Integer counter = 0;
			HashMap<Place<S, C>, String> placesMapping = new HashMap<Place<S,C>,String>();
			for (Place<S,C> place : places) {
				placesMapping.put(place, "\"" +place.toString() + (place.hashCode()/100000)+"\"");
				counter++;
			}
			return placesMapping;
		}
	}
	
	
	
	
	private class NetTestFileWriterToStringQuote extends NetTestFileWriter{

		public NetTestFileWriterToStringQuote(IPetriNet<S, C> net) {
			super(net);

		}
		
		@Override
		protected Map<S, String> getAlphabetMapping(Collection<S> alphabet) {
			Map<S,String> alphabetMapping = new HashMap<S,String>();
			for (S symbol : alphabet) {
				alphabetMapping.put(symbol, quoteId(symbol.toString()) +
						(symbol.hashCode()/100000));
			}
			return alphabetMapping;
		}
		
		@Override
		protected HashMap<Place<S, C>, String> getPlacesMapping(Collection<Place<S,C>> places) {
			Integer counter = 0;
			HashMap<Place<S, C>, String> placesMapping = new HashMap<Place<S,C>,String>();
			for (Place<S,C> place : places) {
				placesMapping.put(place, quoteId(place.toString()) + (place.hashCode()/100000));
				counter++;
			}
			return placesMapping;
		}
	}
	

}
