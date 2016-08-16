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
 * <p>if Labeling == TOSTRING
 * The String representation of LETTER and STATE is used.
 * if Labeling == QUOTED
 * The String representation of LETTER and STATE plus the hashcode() is used.
 * if Labeling == NUMERATE
 * The String representations of LETTER and STATE are ignored.
 * The TestFileWriter introduces new names, e.g. the letters of the alphabet are
 * a0, ..., an.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 * 
 * @param <LETTER> letter type
 * @param <STATE> state type
 */

public class AutomatonDefinitionPrinter<LETTER,STATE> {

	/**
	 * output format types
	 */
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
		 * The Hanoi Omega Automaton Format.
		 */
		HOA("hoa");
		
		private final String mFileEnding;
		
		private Format(final String fileEnding) {
			mFileEnding = fileEnding;
		}
		
		public String getFileEnding() {
			return mFileEnding;
		}
	}
	
	private final AutomataLibraryServices mServices;
	private final ILogger mLogger;
	
	/**
	 * Print hash modulo this number to get shorter identifiers.
	 */
	private static int sHashDivisor = 1;
	
	private PrintWriter mPrintWriter;
	
	private StringWriter mStringWriter;
	
	// enable writing automata, e.g., when an error occurs
	private static final boolean DUMP_AUTOMATON = false;
	
	private AutomatonDefinitionPrinter(final AutomataLibraryServices services) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
	}
	
	/**
	 * @param services Ultimate services
	 * @param automatonName automaton name
	 * @param fileName file name
	 * @param format output format
	 * @param message message
	 * @param automata sequence of automata to print
	 */
	public AutomatonDefinitionPrinter(
			final AutomataLibraryServices services,
			final String automatonName,
			final String fileName,
			final Format format,
			final String message,
			final IAutomaton<?, ?>... automata) {
		this(services);
		mLogger.warn("Dumping Testfile");
		initializePrintWriter(fileName, format);
		switch (format) {
		case ATS:
		case ATS_NUMERATE:
		case ATS_QUOTED:
			mPrintWriter.println("// Testfile dumped by Ultimate at "
					+ getDateTimeNice());
			mPrintWriter.println("//");
			mPrintWriter.println("// " + message);
			mPrintWriter.println("");
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
		for (int i = 0; i < automata.length; i++) {
			printAutomaton(automatonName + String.valueOf(i), automata[i], format);
		}
	}
	
	/**
	 * @param services Ultimate services
	 * @param automatonName automaton name
	 * @param format output format
	 * @param automaton automaton to print
	 */
	public AutomatonDefinitionPrinter(
			final AutomataLibraryServices services,
			final String automatonName,
			final Format format,
			final IAutomaton<?, ?> automaton) {
		this(services);
		mStringWriter = new StringWriter();
		mPrintWriter = new PrintWriter(mStringWriter);
		printAutomaton(automatonName, automaton, format);
	}

	/**
	 * Writes the passed automata to files if the option is enabled.
	 * Does nothing otherwise. <br>
	 * 
	 * <p>This method is intended to be used for dumping automata when an error
	 * occurs in an operation, e.g., when the <code>checkResult()</code> method
	 * fails.
	 * 
	 * @param services Ultimate services
	 * @param filenamePrefix prefix of the file name (e.g., operation name)
	 * @param message message to be printed in the file
	 * @param automata sequence of automata to be printed
	 * @param <LETTER> letter type
	 * @param <STATE> state type
	 */
	@SafeVarargs
	public static <LETTER, STATE> void writeToFileIfPreferred(
			final AutomataLibraryServices services,
			final String filenamePrefix,
			final String message,
			final IAutomaton<?, ?>... automata) {
		if (! DUMP_AUTOMATON) {
			return;
		}
		final String workingDirectory = System.getProperty("user.dir");
		final String filename = workingDirectory + File.separator
				+ filenamePrefix + getDateTimeFileName() + ".ats";
		new AutomatonDefinitionPrinter<LETTER, STATE>(services, filenamePrefix,
				filename, Format.ATS_NUMERATE, message, automata);
	}
	
	private void initializePrintWriter(final String filename, final Format format) {
		final File testfile = new File(filename + '.' + format.getFileEnding());
		try {
			final FileWriter fileWriter = new FileWriter(testfile);
			mPrintWriter = new PrintWriter(fileWriter);
		} catch (final IOException e) {
			e.printStackTrace();
		} 
	}
	
	public String getDefinitionAsString() {
		if (mStringWriter == null) {
			throw new AssertionError("only available with different constructor");
		}
		mStringWriter.flush();
		return mStringWriter.toString();
	}
	
	
	private void printAutomaton(
			final String name,
			final IAutomaton<?, ?> automaton,
			final Format format) {
		if (automaton instanceof INestedWordAutomatonSimple) {
			INestedWordAutomaton<LETTER,STATE> nwa;
			if (automaton instanceof INestedWordAutomaton) {
				nwa = (INestedWordAutomaton<LETTER, STATE>) automaton;
			} else {
				try {
					nwa = new NestedWordAutomatonReachableStates<LETTER, STATE>(
							mServices, (INestedWordAutomatonSimple<LETTER, STATE>) automaton);
				} catch (final AutomataLibraryException e) {
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
		} else if (automaton instanceof IPetriNet) {
			final IPetriNet<LETTER,STATE> net = (IPetriNet<LETTER,STATE>) automaton;
			if (format == Format.ATS) {
				new NetTestFileWriterToString(net);
			} else if (format == Format.ATS_QUOTED) {
				new NetTestFileWriterToStringWithUniqueNumber(net);
			
			} else if (format == Format.ATS_NUMERATE) {
				new NetTestFileWriter(net);
			} else {
				throw new AssertionError("unsupported labeling");
			}
		} else if (automaton instanceof AlternatingAutomaton) {
			final AlternatingAutomaton<LETTER,STATE> aa =
					(AlternatingAutomaton<LETTER,STATE>) automaton;
			new AATestFileWriter(aa);
		}
		mPrintWriter.close();
	}
	
	/**
	 * @return date/time string used inside files
	 */
	private String getDateTimeNice() {
	    return getDateTimeFromFormat("yyyy/MM/dd HH:mm:ss");
	}
	
	/**
	 * @return date/time string used for file names (no special characters)
	 */
	private static String getDateTimeFileName() {
		return getDateTimeFromFormat("yyyyMMddHHmmss");
	}
    
	private static String getDateTimeFromFormat(final String format) {
		final DateFormat dateFormat = new SimpleDateFormat(format);
		final Date date = new Date();
		return dateFormat.format(date);
	}
    
	/**
	 * common methods of test file writers
	 * 
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	private abstract class ATestFileWriterCommon {
		protected void printValues(final Map<?, String> alphabet) {
			printCollection(alphabet.values());
		}
		
		protected void printCollection(final Collection<String> collection) {
			for (final String string : collection) {
				printElement(string);
			}
		}
		
		protected void printElement(final String elem) {
			mPrintWriter.print(elem + ' ');
		}
		
		protected void println(final String string) {
			mPrintWriter.println(string);
		}
		
		protected void print(final String string) {
			mPrintWriter.print(string);
		}
	}
	    
 
	/**
	 * Constructor takes a NestedWordAutomaton and writes it to testfile.
	 */
	private class NwaTestFileWriter extends ATestFileWriterCommon {

		private final INestedWordAutomaton<LETTER,STATE> mNwa;
		private final Map<LETTER, String> mInternalAlphabet;
		private final Map<LETTER, String> mCallAlphabet;
		private final Map<LETTER, String> mReturnAlphabet;
		private final Map<STATE, String> mStateMapping;

		public NwaTestFileWriter(final String name,
				final INestedWordAutomaton<LETTER,STATE> nwa) {
			mNwa = nwa;
			mInternalAlphabet = getAlphabetMapping(nwa.getInternalAlphabet(), "a");
			mCallAlphabet = getAlphabetMapping(nwa.getCallAlphabet(), "c");
			mReturnAlphabet = getAlphabetMapping(nwa.getReturnAlphabet(), "r");
			mStateMapping = getStateMapping(mNwa.getStates());

			println("NestedWordAutomaton " + name + " = (");
			printAlphabets();
			printStates();
			printInitialStates(mNwa.getInitialStates());
			printFinalStates(mNwa.getStates());
			printCallTransitions(mNwa.getStates());
			printInternalTransitions(mNwa.getStates());
			printReturnTransitions(mNwa.getStates());
			println(");");
			mPrintWriter.close();
		}

		protected Map<LETTER,String> getAlphabetMapping(final Collection<LETTER> alphabet,
				final String symbol) {
			Integer counter = 0;
			final Map<LETTER,String> alphabetMapping = new HashMap<LETTER,String>();
			for (final LETTER letter : alphabet) {
				alphabetMapping.put(letter, symbol + counter.toString());
				counter++;
			}
			return alphabetMapping;
		}

		protected Map<STATE,String> getStateMapping(final Collection<STATE> states) {
			Integer counter = 0;
			final Map<STATE,String> stateMapping = new HashMap<STATE,String>();
			for (final STATE state : states) {
				stateMapping.put(state, 's' + counter.toString());
				counter++;
			}
			return stateMapping;
		}

		private void printAlphabets() {
			print('\t' + "callAlphabet = {");
			printValues(mCallAlphabet);
			print("},\n");

			print('\t' + "internalAlphabet = {");
			printValues(mInternalAlphabet);
			print("},\n");

			print('\t' + "returnAlphabet = {");
			printValues(mReturnAlphabet);
			print("},\n");
		}

		private void printStates() {
			print('\t' + "states = {");
			printValues(mStateMapping);
			print("},\n");
		}

		private void printInitialStates(final Collection<STATE> initialStates) {
			print('\t' + "initialStates = {");
			for (final STATE state : initialStates) {
				printElement(mStateMapping.get(state));
			}
			print("},\n");
		}

		private void printFinalStates(final Collection<STATE> allStates) {
			print('\t' + "finalStates = {");
			for (final STATE state : allStates) {
				if (mNwa.isFinal(state)) {
					printElement(mStateMapping.get(state));
				}
			}
			print("},\n");
		}

		private void printCallTransitions(final Collection<STATE> allStates) {
			println('\t' + "callTransitions = {");
			for (final STATE state : allStates) {
				for (final OutgoingCallTransition<LETTER, STATE> outTrans : mNwa.callSuccessors(state)) {
					printCallTransition(state, outTrans);
				}
			}
			println("\t},");
		}

		private void printInternalTransitions(final Collection<STATE> allStates) {
			println('\t' + "internalTransitions = {");
			for (final STATE state : allStates) {
				for (final OutgoingInternalTransition<LETTER, STATE> outTrans : mNwa.internalSuccessors(state)) {
					printInternalTransition(state, outTrans);
				}
			}
			println("\t},");
		}

		private void printReturnTransitions(final Collection<STATE> allStates) {
			println('\t' + "returnTransitions = {");
			for (final STATE state : allStates) {
				for (final OutgoingReturnTransition<LETTER, STATE> outTrans : mNwa.returnSuccessors(state)) {
					printReturnTransition(state, outTrans);
				}
			}
			println("\t}");
		}


		private void printCallTransition(
				final STATE state,
				final OutgoingCallTransition<LETTER, STATE> callTrans) {
			println("\t\t (" +
					mStateMapping.get(state) + ' ' +
					mCallAlphabet.get(callTrans.getLetter()) + ' ' +
					mStateMapping.get(callTrans.getSucc()) + ')'
			);
		}

		private void printInternalTransition(
				final STATE state,
				final OutgoingInternalTransition<LETTER, STATE> internalTrans) {
			println("\t\t (" +
					mStateMapping.get(state) + ' ' +
					mInternalAlphabet.get(internalTrans.getLetter()) + ' ' +
					mStateMapping.get(internalTrans.getSucc()) + ')'
			);
		}

		private void printReturnTransition(
				final STATE state,
				final OutgoingReturnTransition<LETTER, STATE> returnTrans) {
			println("\t\t (" +
					mStateMapping.get(state) + ' ' +
					mStateMapping.get(returnTrans.getHierPred()) + ' ' +
					mReturnAlphabet.get(returnTrans.getLetter()) + ' ' +
					mStateMapping.get(returnTrans.getSucc()) + ')'
			);		
		}
	}
	
	/**
	 * Takes NestedWordAutomaton writes it to testfile. In this version
	 * letters and states are represented by their toString method.
	 */
	private class NwaTestFileWriterToString extends NwaTestFileWriter {

		public NwaTestFileWriterToString(final String name,
				final INestedWordAutomaton<LETTER,STATE> nwa) {
			super(name, nwa);
		}

		@Override
		protected Map<LETTER, String> getAlphabetMapping(
				final Collection<LETTER> alphabet,
				final String symbol) {
			final Map<LETTER,String> alphabetMapping = new HashMap<LETTER,String>();
			for (final LETTER letter : alphabet) {
				alphabetMapping.put(letter, '\"' +
						letter.toString().replaceAll("\"", "\\\"") + '\"');
			}
			return alphabetMapping;
		}

		@Override
		protected Map<STATE, String> getStateMapping(
				final Collection<STATE> states) {
			final Map<STATE,String> stateMapping = new HashMap<STATE,String>();
			for (final STATE state : states) {
				stateMapping.put(state, '\"' +
						state.toString().replaceAll("\"", "\\\"") + '\"');
			}
			return stateMapping;
		}
	}
	
	
	/**
	 * Takes NestedWordAutomaton writes it to testfile. In this version
	 * letters and states are represented by their toString method.
	 */
	private class NwaTestFileWriterToStringWithHash extends NwaTestFileWriter {

		public NwaTestFileWriterToStringWithHash(
				final String name,
				final INestedWordAutomaton<LETTER,STATE> nwa) {
			super(name, nwa);
		}

		@Override
		protected Map<LETTER, String> getAlphabetMapping(
				final Collection<LETTER> alphabet,
				final String symbol) {
			final Map<LETTER,String> alphabetMapping = new HashMap<LETTER,String>();
			for (final LETTER letter : alphabet) {
				alphabetMapping.put(letter,
						'\"' + letter.toString().replaceAll("\"", "\\\"")
						+ (letter.hashCode() / sHashDivisor) + '\"');
			}
			return alphabetMapping;
		}

		@Override
		protected Map<STATE, String> getStateMapping(
				final Collection<STATE> states) {
			final Map<STATE,String> stateMapping = new HashMap<STATE,String>();
			for (final STATE state : states) {
				stateMapping.put(state, '\"' + state.toString().replaceAll("\"", "\\\"") +
						(state.hashCode() / sHashDivisor) + '\"');
			}
			return stateMapping;
		}
	}
	
	
	/**
	 * Constructor takes a PetriNet and writes it to a testfile.
	 */
	private class NetTestFileWriter extends ATestFileWriterCommon {

		private final Map<LETTER, String> mAlphabet;
		private final Map<Place<LETTER,STATE>, String> mPlacesMapping;

		public NetTestFileWriter(final IPetriNet<LETTER,STATE> net) {
			mAlphabet = getAlphabetMapping(net.getAlphabet());
			mPlacesMapping = getPlacesMapping(net.getPlaces());

			println("PetriNet net = (");
			printAlphabet();
			printPlaces();
			printInternalTransitions(net.getTransitions());
			printInitialMarking(net.getInitialMarking());
			if (net instanceof PetriNetJulian) {
				printAcceptingPlaces(((PetriNetJulian<LETTER,STATE>) net).getAcceptingPlaces());
			} else {
				throw new IllegalArgumentException("unknown kinde of net");
			}
			println(")");
			mPrintWriter.close();
		}
		

		protected Map<LETTER,String> getAlphabetMapping(final Collection<LETTER> alphabet) {
			Integer counter = 0;
			final Map<LETTER,String> alphabetMapping = new HashMap<LETTER,String>();
			for (final LETTER letter : alphabet) {
				alphabetMapping.put(letter, 'a' + counter.toString());
				counter++;
			}
			return alphabetMapping;
		}
		
		protected Map<Place<LETTER, STATE>, String> getPlacesMapping(
				final Collection<Place<LETTER,STATE>> places) {
			Integer counter = 0;
			final HashMap<Place<LETTER,STATE>, String> placesMapping =
					new HashMap<>();
			for (final Place<LETTER,STATE> place : places) {
				placesMapping.put(place, 'p' + counter.toString());
				counter++;
			}
			return placesMapping;
		}
		
		private void printAlphabet() {
			print('\t' + "alphabet = {");
			printValues(mAlphabet);
			print("},\n");
		}
		
		private void printPlaces() {
			print('\t' + "places = {");
			printValues(mPlacesMapping);
			print("},\n");
		}
		
		private void printInternalTransitions(
				final Collection<ITransition<LETTER,STATE>> transitions) {
			println('\t' + "transitions = {");
			for (final ITransition<LETTER,STATE> transition : transitions) {
				printTransition(transition);
			}
			println("\t},");
		}

		private void printTransition(final ITransition<LETTER,STATE> transition) {
			print("\t\t( ");
			printMarking(transition.getPredecessors());
			print(" ");
			print(mAlphabet.get(transition.getSymbol()));
			print(" ");
			printMarking(transition.getSuccessors());
			print(" )\n");
		}
		
		private void printMarking(final Marking<LETTER,STATE> marking) {
			printMarkingIterable(marking);
		}
		
		private void printMarking(final Collection<Place<LETTER,STATE>> marking) {
			printMarkingIterable(marking);
		}
		
		private void printMarkingIterable(final Iterable<Place<LETTER,STATE>> marking) {
			print("{");
			for (final Place<LETTER,STATE> place : marking) {
				printElement(mPlacesMapping.get(place));
			}
			print("}");
		}

		private void printInitialMarking(final Marking<LETTER,STATE> initialMarking) {
			print('\t' + "initialMarking = ");
			printMarking(initialMarking);
			print(",\n");
		}
		
		private void printAcceptingPlaces(final Collection<Place<LETTER,STATE>> acceptingPlaces) {
			print('\t' + "acceptingPlaces = ");
			printMarking(acceptingPlaces);
			print("\n");
		}
	}
	
	private class NetTestFileWriterToString extends NetTestFileWriter {

		public NetTestFileWriterToString(final IPetriNet<LETTER,STATE> net) {
			super(net);

		}
		
		@Override
		protected Map<LETTER, String> getAlphabetMapping(final Collection<LETTER> alphabet) {
			final Map<LETTER,String> alphabetMapping = new HashMap<LETTER,String>();
			for (final LETTER letter : alphabet) {
				alphabetMapping.put(letter, '\"' + letter.toString().replaceAll("\"", "\\\"") + '\"');
			}
			return alphabetMapping;
		}
		
		@Override
		protected Map<Place<LETTER,STATE>, String> getPlacesMapping(
				final Collection<Place<LETTER,STATE>> places) {
			Integer counter = 0;
			final HashMap<Place<LETTER,STATE>, String> placesMapping =
					new HashMap<>();
			for (final Place<LETTER,STATE> place : places) {
				placesMapping.put(place, '\"' +
						place.toString().replaceAll("\"", "\\\"") + '\"');
				counter++;
			}
			return placesMapping;
		}
	}
	
	private class NetTestFileWriterToStringWithUniqueNumber extends NetTestFileWriter {

		public NetTestFileWriterToStringWithUniqueNumber(final IPetriNet<LETTER,STATE> net) {
			super(net);

		}
		
		@Override
		protected Map<LETTER, String> getAlphabetMapping(final Collection<LETTER> alphabet) {
			int counter = 0;
			final Map<LETTER,String> alphabetMapping = new HashMap<LETTER,String>();
			for (final LETTER letter : alphabet) {
				alphabetMapping.put(letter, '\"' +
			letter.toString().replaceAll("\"", "\\\"") + (counter++));
			}
			return alphabetMapping;
		}
		
		@Override
		protected Map<Place<LETTER,STATE>, String> getPlacesMapping(
				final Collection<Place<LETTER,STATE>> places) {
			int counter = 0;
			final HashMap<Place<LETTER,STATE>, String> placesMapping =
					new HashMap<>();
			for (final Place<LETTER,STATE> place : places) {
				placesMapping.put(place, '\"' +
						place.toString().replaceAll("\"", "\\\"") + (counter++));
			}
			return placesMapping;
		}
	}
	
	/**
	 * Constructor takes a AlternatingAutomaton and writes it to a testfile.
	 */
	private class AATestFileWriter {
		
		private final AlternatingAutomaton<LETTER, STATE> mAa;

		public AATestFileWriter(final AlternatingAutomaton<LETTER,STATE> aa) {
			
			mAa = aa;

			mPrintWriter.println("Alternating Automaton aa = (");
			mPrintWriter.println(mAa.toString());
//			printAlphabet(mAa.getAlphabet());
//			printExistentialStates(mAa.getExistentialStates());
//			printUniversalStates(mAa.getUniversalStates());
//			printInitialStates(mAa.getInitialStates());
//			printFinalStates(mAa.getFinalStates());
//			printInternalTransitions(mAa.getTransitionsMap());
			

			mPrintWriter.println(')');
			mPrintWriter.close();
		}
		
//		private void printAlphabet(Set<LETTER> set) {
//			mprintWriter.print('\t' + "alphabet = { ");
//			for (LETTER letter : set) {
//				mprintWriter.print(letter + ' ');
//			}
//			mprintWriter.print("},\n");
//		}
//		
//		private void printExistentialStates(Set<STATE> set) {
//			mprintWriter.print('\t' + "existentialStates = { ");
//			for (STATE state : set) {
//				mprintWriter.print(state + ' ');
//			}
//			mprintWriter.print("},\n");
//		}
//		
//		private void printUniversalStates(Set<STATE> set) {
//			mprintWriter.print('\t' + "universalStates = { ");
//			for (STATE state : set) {
//				mprintWriter.print(state + ' ');
//			}
//			mprintWriter.print("},\n");
//		}
//		
//		private void printInitialStates(Set<STATE> set) {
//			mprintWriter.print('\t' + "initialStates = { ");
//			for (STATE state : set) {
//				mprintWriter.print(state + ' ');
//			}
//			mprintWriter.print("},\n");
//		}
//		
//		private void printFinalStates(Set<STATE> set) {
//			mprintWriter.print('\t' + "finalStates = { ");
//			for (STATE state : set) {
//				mprintWriter.print(state + ' ');
//			}
//			mprintWriter.print("},\n");
//		}
//		
//		private void printInternalTransitions(Map<STATE, Map<LETTER, Set<STATE>>> map) {
//			mprintWriter.println('\t' + "internalTransitions = {");
//			for (Entry<STATE, Map<LETTER, Set<STATE>>> entry : map.entrySet()) {
//			    STATE pre = entry.getKey();
//			    Map<LETTER, Set<STATE>> transitionsMap = entry.getValue();
//			    if (transitionsMap != null) {// state has no outgoing transitions, so nothing has to be printed
//			    	for (Entry<LETTER, Set<STATE>> entry1 : transitionsMap.entrySet()) {
//				        LETTER letter = entry1.getKey();
//				        Set<STATE> succStates = entry1.getValue();
//				        for (STATE succ : succStates) {
//				        	printInternalTransition(pre, letter, succ);
//				        }
//				        
//				        
//				    }
//			    }
//			    
//			}
//			mprintWriter.println("\t},");
//		}
//		
//		private void printInternalTransition(STATE pre, LETTER letter,
//				STATE succ) {
//			mprintWriter.println("\t\t (" +
//					pre + ' ' +
//					letter + ' ' +
//					succ + ')'
//			);
//		}

	}
	
	private class AbstractWriter {
		
		protected final Map<LETTER, String> mAlphabetMapping;
		protected final Map<STATE, String> mStateMapping;
		protected final INestedWordAutomaton<LETTER, STATE> mNwa;

		public AbstractWriter(final INestedWordAutomaton<LETTER, STATE> nwa) {
			mAlphabetMapping = computeAlphabetMapping(nwa.getInternalAlphabet());
			mStateMapping = computeStateMapping(nwa.getStates());
			mNwa = nwa;
		}
		
		private Map<LETTER,String> computeAlphabetMapping(final Collection<LETTER> alphabet) {
			Integer counter = 0;
			final Map<LETTER,String> alphabetMapping = new HashMap<>();
			for (final LETTER letter : alphabet) {
				alphabetMapping.put(letter, counter.toString());
				counter++;
			}
			return alphabetMapping;
		}

		private Map<STATE,String> computeStateMapping(final Collection<STATE> states) {
			Integer counter = 0;
			final Map<STATE,String> stateMapping = new HashMap<STATE,String>();
			for (final STATE state : states) {
				stateMapping.put(state, counter.toString());
				counter++;
			}
			return stateMapping;
		}
		
	}
	
	private class BaFormatWriter extends AbstractWriter {

		public BaFormatWriter(final INestedWordAutomaton<LETTER, STATE> nwa) {
			super(nwa);
			doPrint();
		}

		protected void doPrint() {
			final StringBuilder initStateSb = computeStateString(mNwa.getInitialStates(), mStateMapping);
			final StringBuilder transSb = computeTransitionString(mNwa, mStateMapping, mAlphabetMapping);
			final StringBuilder finalStateSb = computeStateString(mNwa.getFinalStates(), mStateMapping);
			mPrintWriter.print(initStateSb);
			mPrintWriter.print(transSb);
			mPrintWriter.print(finalStateSb);
		}

		private StringBuilder computeStateString(
				final Collection<STATE> initialStates,
				final Map<STATE, String> stateMapping) {
			final StringBuilder result = new StringBuilder();
			for (final STATE state : initialStates) {
				result.append('[' + stateMapping.get(state) + ']' + System.lineSeparator());
			}
			return result;
		}
		
		private StringBuilder computeTransitionString(
				final INestedWordAutomaton<LETTER, STATE> nwa,
				final Map<STATE, String> stateMapping,
				final Map<LETTER, String> alphabetMapping) {
			final StringBuilder result = new StringBuilder();
			for (final STATE state : nwa.getStates()) {
				for (final OutgoingInternalTransition<LETTER, STATE> outTrans : nwa.internalSuccessors(state)) {
					result.append(
							alphabetMapping.get(outTrans.getLetter()) + 
							',' + 
							'[' + stateMapping.get(state) + ']' + 
							"->" +
							'[' + stateMapping.get(outTrans.getSucc()) + ']' +
							System.lineSeparator());
				}
			}
			return result;
		}
	}
	
	
	private class HanoiFormatWriter extends AbstractWriter {
		
		private static final boolean USE_LABELS = false;
		private final IConverter<LETTER> mLetterConverterAP;

		public HanoiFormatWriter(final INestedWordAutomaton<LETTER, STATE> nwa) {
			super(nwa);
			if (USE_LABELS) {
				mLetterConverterAP = new ToStringConverter<LETTER>();
			} else {
				mLetterConverterAP = new MapBasedConverter<LETTER, String>(mAlphabetMapping, "");
			}
			doPrint();
		}

		protected void doPrint() {
			final String header = constructHeader();
			mPrintWriter.print(header);
			final String bodyToken = "--BODY--";
			mPrintWriter.print(bodyToken);
			mPrintWriter.print(System.lineSeparator());
			final String body = constructBody();
			mPrintWriter.print(body);
			final String endToken = "--END--";
			mPrintWriter.print(endToken);
		}

		private String constructHeader() {
			final StringBuilder sb = new StringBuilder();
			sb.append("HOA: v1");
			sb.append(System.lineSeparator());
			
			sb.append("States: " + mNwa.getStates().size());
			sb.append(System.lineSeparator());
			
			for (final STATE state : mNwa.getInitialStates()) {
				sb.append("Start: " + mStateMapping.get(state));
				sb.append(System.lineSeparator());
			}
			
			sb.append("AP: " + mNwa.getInternalAlphabet().size());
			for (final LETTER letter : mNwa.getInternalAlphabet()) {
				sb.append(" \"p" + mLetterConverterAP.convert(letter) + '\"');
			}
			sb.append(System.lineSeparator());
			
			for (final LETTER letter : mNwa.getInternalAlphabet()) {
				sb.append("Alias: @");
				sb.append(mAlphabetMapping.get(letter));
				boolean firstOther = true;
				for (final LETTER otherLetter : mNwa.getInternalAlphabet()) {
					if (firstOther) {
						firstOther = false;
					} else {
						sb.append(" &");
					}
					if (otherLetter == letter) {
						sb.append(' ');
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
			final StringBuilder sb = new StringBuilder();

			final String accSig = "{0}";
			for (final STATE state : mNwa.getStates()) {
				sb.append("State: " + mStateMapping.get(state));
				if (USE_LABELS) {
					sb.append(" \"");
					sb.append(state);
					sb.append(" \"");
				}
				if (mNwa.isFinal(state)) {
					sb.append(' ' + accSig);
				}
				sb.append(System.lineSeparator());
				for (final LETTER letter : mNwa.lettersInternal(state)) {
					for (final OutgoingInternalTransition<LETTER, STATE> tes : mNwa.internalSuccessors(state, letter)) {
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
		
		private final IConverter<LETTER> mLetterConverter;
		private final IConverter<STATE> mStateConverter;

		public GoalFormatWriter(final INestedWordAutomaton<LETTER, STATE> nwa) {
			super(nwa);
			mLetterConverter = new MapBasedConverter<LETTER, String>(mAlphabetMapping, "");
			mStateConverter = new MapBasedConverter<STATE, String>(mStateMapping, "");
			doPrint();
		}

		protected void doPrint() {
			final StringBuilder sb = new StringBuilder();
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
			mPrintWriter.print(sb.toString());
		}
		
		private String constuctAlphabetSection() {
			final StringBuilder sb = new StringBuilder();
			sb.append("\t");
			sb.append("<Alphabet type=\"Classical\">");
			sb.append(System.lineSeparator());
			for (final LETTER letter : mNwa.getInternalAlphabet()) {
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
			final StringBuilder sb = new StringBuilder();
			sb.append("\t");
			sb.append("<StateSet>");
			sb.append(System.lineSeparator());
			for (final STATE state : mNwa.getStates()) {
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
			final StringBuilder sb = new StringBuilder();
			sb.append("\t");
			sb.append("<InitialStateSet>");
			sb.append(System.lineSeparator());
			for (final STATE state : mNwa.getInitialStates()) {
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
			final StringBuilder sb = new StringBuilder();
			sb.append("\t");
			sb.append("<TransitionSet complete=\"false\">");
			sb.append(System.lineSeparator());
			for (final STATE state : mNwa.getStates()) {
				for (final OutgoingInternalTransition<LETTER, STATE> trans : mNwa.internalSuccessors(state)) {
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
			final StringBuilder sb = new StringBuilder();
			sb.append("\t");
			sb.append("<Acc type=\"Buchi\">");
			sb.append(System.lineSeparator());
			for (final STATE state : mNwa.getFinalStates()) {
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
	
	private interface IConverter<E> {
		String convert(E elem);
	}
	
	private class ToStringConverter<E> implements IConverter<E> {

		@Override
		public String convert(final E elem) {
			return String.valueOf(elem);
		}
		
	}
	
	private class MapBasedConverter<E,V> implements IConverter<E> {
		
		private final Map<E,V> mMap;
		private final String mPrefix;
		
		public MapBasedConverter(final Map<E, V> map, final String prefix) {
			mPrefix = prefix;
			mMap = map;
		}

		@Override
		public String convert(final E elem) {
			final V value = mMap.get(elem);
			if (value == null) {
				throw new IllegalArgumentException("unknown element: " + elem);
			}
			return mPrefix + String.valueOf(value);
		}
		
	}
}
