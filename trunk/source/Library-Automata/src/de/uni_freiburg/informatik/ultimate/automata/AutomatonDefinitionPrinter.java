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
import java.util.LinkedHashMap;
import java.util.Locale;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.alternating.AlternatingAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Place;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.PetriNetJulian;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 * Writes the automaton definition for given automata.
 * Writing can either be to a string or to a file.
 * <p>
 * TODO Christian 2016-08-21: The classes for writing the concrete automata should be moved to the respective package to
 * reduce the complexity of this class.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 * @see Format available output modes
 */
public class AutomatonDefinitionPrinter<LETTER, STATE> {
	private static final int ONE = 1;
	private static final String UNSUPPORTED_LABELING = "Unsupported labeling.";
	private static final String ATS_EXTENSION = "ats";
	private static final char QUOTE = '\"';
	
	/**
	 * Output format types.
	 */
	public enum Format {
		/**
		 * Automata script.<br>
		 * The {@link #toString()} representation of {@link LETTER} and {@link STATE} is used.
		 */
		ATS(ATS_EXTENSION),
		/**
		 * Automata script.<br>
		 * The {@link #toString()} representations of {@link LETTER} and {@link STATE} are ignored.
		 * The {@link TestFileWriter} introduces new names, e.g. the letters of the alphabet are <tt>a0, ..., an</tt>.
		 */
		ATS_NUMERATE(ATS_EXTENSION),
		/**
		 * Automata script.<br>
		 * The {@link #toString()} representation of {@link LETTER} and {@link STATE} plus a number is used.
		 */
		ATS_QUOTED(ATS_EXTENSION),
		/**
		 * The <tt>BA</tt> format which is also used by some tools of Yu-Fang Chen.
		 */
		BA("ba"),
		/**
		 * (GOAL File Format) - The XML file format used by <tt>GOAL</tt>.
		 */
		GFF("gff"),
		/**
		 * The <tt>Hanoi Omega Automaton</tt> format.
		 */
		HOA("hoa");
		
		private final String mFileEnding;
		
		Format(final String fileEnding) {
			mFileEnding = fileEnding;
		}
		
		public String getFileEnding() {
			return mFileEnding;
		}
	}
	
	private final AutomataLibraryServices mServices;
	private final ILogger mLogger;
	
	private static final String NEW_LINE = System.lineSeparator();
	
	/**
	 * Print hash modulo this number to get shorter identifiers.
	 */
	private static int sHashDivisor = 1;
	
	private PrintWriter mPrintWriter;
	
	private StringWriter mStringWriter;
	
	// enable writing automata, e.g., when an error occurs
	private static final boolean DUMP_AUTOMATON = false;
	
	/**
	 * Base constructor.
	 * 
	 * @param services
	 *            Ultimate services
	 */
	private AutomatonDefinitionPrinter(final AutomataLibraryServices services) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		mPrintWriter = null;
		mStringWriter = null;
	}
	
	/**
	 * Constructor for printing multiple {@link IAutomaton} objects to a file.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param automatonName
	 *            automaton name
	 * @param fileName
	 *            file name
	 * @param format
	 *            output format
	 * @param message
	 *            message
	 * @param automata
	 *            sequence of automata to print
	 */
	public AutomatonDefinitionPrinter(
			final AutomataLibraryServices services,
			final String automatonName,
			final String fileName,
			final Format format,
			final String message,
			final IAutomaton<?, ?>... automata) {
		this(services);
		final FileWriter fileWriter = getFileWriter(fileName, format);
		if (fileWriter != null) {
			if (mLogger.isWarnEnabled()) {
				mLogger.warn("Dumping automata.");
			}
			mPrintWriter = new PrintWriter(fileWriter);
			printAutomataToFileWriter(automatonName, format, message, automata);
		}
	}
	
	/**
	 * Constructor for printing a single {@link IAutomaton} to a {@link StringWriter}.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param automatonName
	 *            automaton name
	 * @param format
	 *            output format
	 * @param automaton
	 *            automaton to print
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
	 * Writes the passed {@link IAutomaton} objects to files if the option is enabled.
	 * Does nothing otherwise.
	 * <p>
	 * This method is intended to be used for dumping automata when an error
	 * occurs in an {@link IOperation}, e.g., when the {@link IOperation#checkResult()} method
	 * fails.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param fileNamePrefix
	 *            prefix of the file name (e.g., operation name)
	 * @param message
	 *            message to be printed in the file
	 * @param automata
	 *            sequence of automata to be printed
	 * @param <LETTER>
	 *            letter type
	 * @param <STATE>
	 *            state type
	 */
	@SafeVarargs
	@SuppressWarnings("squid:S1848")
	public static <LETTER, STATE> void writeToFileIfPreferred(
			final AutomataLibraryServices services,
			final String fileNamePrefix,
			final String message,
			final IAutomaton<?, ?>... automata) {
		if (!DUMP_AUTOMATON) {
			return;
		}
		final String workingDirectory = System.getProperty("user.dir");
		final String fileName = workingDirectory + File.separator + fileNamePrefix + getDateTimeFileName();
		new AutomatonDefinitionPrinter<LETTER, STATE>(services,
				fileNamePrefix, fileName, Format.ATS_NUMERATE, message, automata);
	}
	
	/**
	 * This method is only available if the
	 * {@link #AutomatonDefinitionPrinter(AutomataLibraryServices, String, Format, IAutomaton)} constructor was used.
	 * 
	 * @return The definition as string.
	 */
	public String getDefinitionAsString() {
		if (mStringWriter == null) {
			throw new AssertionError("only available with different constructor");
		}
		return mStringWriter.toString();
	}
	
	private FileWriter getFileWriter(final String fileName, final Format format) {
		final File testfile = new File(fileName + '.' + format.getFileEnding());
		try {
			return new FileWriter(testfile);
		} catch (final IOException e) {
			if (mLogger.isErrorEnabled()) {
				mLogger.error("Creating FileWriter did not work.", e);
			}
			return null;
		}
	}
	
	/**
	 * Date/time string used inside files.
	 * 
	 * @return date/time string
	 */
	private static String getDateTimeNice() {
		return getDateTimeFromFormat("yyyy/MM/dd HH:mm:ss");
	}
	
	/**
	 * Date/time string used for file names (no special characters).
	 * 
	 * @return date/time string
	 */
	private static String getDateTimeFileName() {
		return getDateTimeFromFormat("yyyyMMddHHmmss");
	}
	
	private static String getDateTimeFromFormat(final String format) {
		final DateFormat dateFormat = new SimpleDateFormat(format, Locale.ENGLISH);
		final Date date = new Date();
		return dateFormat.format(date);
	}
	
	private void printAutomataToFileWriter(final String automatonName, final Format format, final String message,
			final IAutomaton<?, ?>... automata) throws AssertionError {
		switch (format) {
			case ATS:
			case ATS_NUMERATE:
			case ATS_QUOTED:
				mPrintWriter.println("// Testfile dumped by Ultimate at " + getDateTimeNice()
						+ NEW_LINE + "//" + NEW_LINE + "// " + message + NEW_LINE);
				break;
			case BA:
			case HOA:
			case GFF:
				// add nothing
				break;
			default:
				throw new IllegalArgumentException(UNSUPPORTED_LABELING);
		}
		if (automata.length == ONE) {
			printAutomaton(automatonName, automata[0], format);
		}
		for (int i = 0; i < automata.length; i++) {
			printAutomaton(automatonName + i, automata[i], format);
		}
	}
	
	/**
	 * Determines the input automaton type and calls the respective print method.
	 * 
	 * @param name
	 *            name of the automaton in the output
	 * @param automaton
	 *            automaton object
	 * @param format
	 *            output format
	 */
	@SuppressWarnings("unchecked")
	private void printAutomaton(final String name, final IAutomaton<?, ?> automaton, final Format format) {
		if (automaton instanceof INestedWordAutomatonSimple) {
			printNestedWordAutomaton(name, (INestedWordAutomatonSimple<LETTER, STATE>) automaton, format);
		} else if (automaton instanceof IPetriNet) {
			printPetriNet(name, (IPetriNet<LETTER, STATE>) automaton, format);
		} else if (automaton instanceof AlternatingAutomaton) {
			printAlternatingAutomaton(name, (AlternatingAutomaton<LETTER, STATE>) automaton, format);
		}
		mPrintWriter.close();
	}
	
	private void printValues(final Map<?, String> alphabet) {
		printCollection(alphabet.values());
	}
	
	private void printCollection(final Collection<String> collection) {
		for (final String string : collection) {
			printElement(string);
		}
	}
	
	private void printElement(final String elem) {
		mPrintWriter.print(elem + ' ');
	}
	
	private void println(final String string) {
		mPrintWriter.println(string);
	}
	
	private void println(final char character) {
		mPrintWriter.println(character);
	}
	
	private void print(final String string) {
		mPrintWriter.print(string);
	}
	
	private void print(final char character) {
		mPrintWriter.print(character);
	}
	
	private void print(final StringBuilder builder) {
		mPrintWriter.print(builder);
	}
	
	private void printAutomatonPrefix() {
		println(" = (");
	}
	
	private void printAutomatonSuffix() {
		println(");");
	}
	
	private static String getCollectionPrefix(final String string) {
		return String.format("\t%s = {", string);
	}
	
	private void printCollectionPrefix(final String string) {
		print(getCollectionPrefix(string));
	}
	
	private void printlnCollectionPrefix(final String string) {
		println(getCollectionPrefix(string));
	}
	
	private void printElementPrefix(final String string) {
		print(String.format("\t%s = ", string));
	}
	
	private void printCollectionSuffix() {
		println("},");
	}
	
	private void printOneTransitionPrefix() {
		print("\t\t(");
	}
	
	private void printOneTransitionSuffix() {
		println(')');
	}
	
	private void printTransitionsSuffix() {
		println("\t},");
	}
	
	private void printLastTransitionsSuffix() {
		println("\t}");
	}
	
	// --- nested word automaton writers ---
	
	@SuppressWarnings({ "squid:S1166", "squid:S1848" })
	private void printNestedWordAutomaton(final String name, final INestedWordAutomatonSimple<LETTER, STATE> automaton,
			final Format format) throws AssertionError {
		INestedWordAutomaton<LETTER, STATE> nwa;
		if (automaton instanceof INestedWordAutomaton) {
			nwa = (INestedWordAutomaton<LETTER, STATE>) automaton;
		} else {
			try {
				nwa = new NestedWordAutomatonReachableStates<>(mServices, automaton);
			} catch (final AutomataLibraryException e) {
				throw new AssertionError("Timeout while preparing automaton for printing.");
			}
		}
		
		switch (format) {
			case ATS:
				new NwaWriterToString(name, nwa);
				break;
			case ATS_QUOTED:
				new NwaWriterToStringWithHash(name, nwa);
				break;
			case ATS_NUMERATE:
				new NwaWriterUniqueId(name, nwa);
				break;
			case BA:
				new BaFormatWriter(nwa);
				break;
			case HOA:
				new HanoiFormatWriter(nwa);
				break;
			case GFF:
				new GoalFormatWriter(nwa);
				break;
			default:
				throw new AssertionError(UNSUPPORTED_LABELING);
		}
	}
	
	private static String replaceBackslashes(final Object input) {
		return input.toString().replaceAll("\"", "\\\"");
	}
	
	private static String quoteAndReplaceBackslashes(final Object input) {
		return QUOTE + replaceBackslashes(input) + QUOTE;
	}
	
	private static String quoteAndReplaceBackslashes(final Object input, final String suffix) {
		return QUOTE + replaceBackslashes(input) + suffix + QUOTE;
	}
	
	/**
	 * Prints an {@link INestedWordAutomaton}.
	 */
	private abstract class NwaTestFileWriter {
		
		private final INestedWordAutomaton<LETTER, STATE> mNwa;
		private final Map<LETTER, String> mInternalAlphabet;
		private final Map<LETTER, String> mCallAlphabet;
		private final Map<LETTER, String> mReturnAlphabet;
		private final Map<STATE, String> mStateMapping;
		
		public NwaTestFileWriter(final String name, final INestedWordAutomaton<LETTER, STATE> nwa) {
			mNwa = nwa;
			mInternalAlphabet = getAlphabetMapping(mNwa.getInternalAlphabet(), 'a');
			mCallAlphabet = getAlphabetMapping(mNwa.getCallAlphabet(), 'c');
			mReturnAlphabet = getAlphabetMapping(mNwa.getReturnAlphabet(), 'r');
			mStateMapping = getStateMapping(mNwa.getStates());
			
			// automata script format for NestedWordAutomaton
			print("NestedWordAutomaton ");
			print(name);
			printAutomatonPrefix();
			printAlphabets();
			printStates();
			printInitialStates(mNwa.getInitialStates());
			printFinalStates(mNwa.getStates());
			printCallTransitions(mNwa.getStates());
			printInternalTransitions(mNwa.getStates());
			printReturnTransitions(mNwa.getStates());
			printAutomatonSuffix();
		}
		
		/**
		 * Constructs the new alphabet.
		 * 
		 * @param alphabet
		 *            old alphabet
		 * @param symbol
		 *            default symbol
		 * @return mapping (old alphabet -> new alphabet)
		 */
		protected abstract Map<LETTER, String> getAlphabetMapping(final Collection<LETTER> alphabet, final char symbol);
		
		/**
		 * Constructs the new states.
		 * 
		 * @param states
		 *            old states
		 * @return new states
		 */
		protected abstract Map<STATE, String> getStateMapping(final Collection<STATE> states);
		
		private void printAlphabets() {
			printCollectionPrefix("callAlphabet");
			printValues(mCallAlphabet);
			printCollectionSuffix();
			
			printCollectionPrefix("internalAlphabet");
			printValues(mInternalAlphabet);
			printCollectionSuffix();
			
			printCollectionPrefix("returnAlphabet");
			printValues(mReturnAlphabet);
			printCollectionSuffix();
		}
		
		private void printStates() {
			printCollectionPrefix("states");
			printValues(mStateMapping);
			printCollectionSuffix();
		}
		
		private void printInitialStates(final Collection<STATE> initialStates) {
			printCollectionPrefix("initialStates");
			for (final STATE state : initialStates) {
				printElement(mStateMapping.get(state));
			}
			printCollectionSuffix();
		}
		
		private void printFinalStates(final Collection<STATE> allStates) {
			printCollectionPrefix("finalStates");
			for (final STATE state : allStates) {
				if (mNwa.isFinal(state)) {
					printElement(mStateMapping.get(state));
				}
			}
			printCollectionSuffix();
		}
		
		private void printCallTransitions(final Collection<STATE> allStates) {
			printlnCollectionPrefix("callTransitions");
			for (final STATE state : allStates) {
				for (final OutgoingCallTransition<LETTER, STATE> callTrans : mNwa.callSuccessors(state)) {
					printOneTransitionPrefix();
					print(mStateMapping.get(state));
					print(' ');
					print(mCallAlphabet.get(callTrans.getLetter()));
					print(' ');
					print(mStateMapping.get(callTrans.getSucc()));
					printOneTransitionSuffix();
				}
			}
			printTransitionsSuffix();
		}
		
		private void printInternalTransitions(final Collection<STATE> allStates) {
			printlnCollectionPrefix("internalTransitions");
			for (final STATE state : allStates) {
				for (final OutgoingInternalTransition<LETTER, STATE> internalTrans : mNwa.internalSuccessors(state)) {
					printOneTransitionPrefix();
					print(mStateMapping.get(state));
					print(' ');
					print(mInternalAlphabet.get(internalTrans.getLetter()));
					print(' ');
					print(mStateMapping.get(internalTrans.getSucc()));
					printOneTransitionSuffix();
				}
			}
			printTransitionsSuffix();
		}
		
		private void printReturnTransitions(final Collection<STATE> allStates) {
			printlnCollectionPrefix("returnTransitions");
			for (final STATE state : allStates) {
				for (final OutgoingReturnTransition<LETTER, STATE> returnTrans : mNwa.returnSuccessors(state)) {
					printOneTransitionPrefix();
					print(mStateMapping.get(state));
					print(' ');
					print(mStateMapping.get(returnTrans.getHierPred()));
					print(' ');
					print(mReturnAlphabet.get(returnTrans.getLetter()));
					print(' ');
					print(mStateMapping.get(returnTrans.getSucc()));
					printOneTransitionSuffix();
				}
			}
			printLastTransitionsSuffix();
		}
	}
	
	/**
	 * Prints an {@link INestedWordAutomaton}.
	 * In this version letters and states are represented by a default symbol and a unique ID.
	 */
	private final class NwaWriterUniqueId extends NwaTestFileWriter {
		
		public NwaWriterUniqueId(final String name, final INestedWordAutomaton<LETTER, STATE> nwa) {
			super(name, nwa);
		}
		
		@Override
		protected Map<LETTER, String> getAlphabetMapping(final Collection<LETTER> alphabet, final char symbol) {
			int counter = 0;
			final Map<LETTER, String> alphabetMapping = new LinkedHashMap<>();
			for (final LETTER letter : alphabet) {
				alphabetMapping.put(letter, symbol + Integer.toString(counter));
				counter++;
			}
			return alphabetMapping;
		}
		
		@Override
		protected Map<STATE, String> getStateMapping(final Collection<STATE> states) {
			int counter = 0;
			final Map<STATE, String> stateMapping = new LinkedHashMap<>();
			for (final STATE state : states) {
				stateMapping.put(state, 's' + Integer.toString(counter));
				counter++;
			}
			return stateMapping;
		}
	}
	
	/**
	 * Prints an {@link INestedWordAutomaton}.
	 * In this version letters and states are represented by their {@link #toString()} method.
	 */
	private final class NwaWriterToString extends NwaTestFileWriter {
		
		public NwaWriterToString(final String name, final INestedWordAutomaton<LETTER, STATE> nwa) {
			super(name, nwa);
		}
		
		@Override
		protected Map<LETTER, String> getAlphabetMapping(final Collection<LETTER> alphabet, final char symbol) {
			final Map<LETTER, String> alphabetMapping = new HashMap<>();
			for (final LETTER letter : alphabet) {
				alphabetMapping.put(letter, quoteAndReplaceBackslashes(letter));
			}
			return alphabetMapping;
		}
		
		@Override
		protected Map<STATE, String> getStateMapping(final Collection<STATE> states) {
			final Map<STATE, String> stateMapping = new HashMap<>();
			for (final STATE state : states) {
				stateMapping.put(state, quoteAndReplaceBackslashes(state));
			}
			return stateMapping;
		}
	}
	
	/**
	 * Prints an {@link INestedWordAutomaton}.
	 * In this version letters and states are represented by their {@link #toString()} and {@link #hashCode()} methods.
	 */
	private final class NwaWriterToStringWithHash extends NwaTestFileWriter {
		
		public NwaWriterToStringWithHash(final String name, final INestedWordAutomaton<LETTER, STATE> nwa) {
			super(name, nwa);
		}
		
		@Override
		protected Map<LETTER, String> getAlphabetMapping(final Collection<LETTER> alphabet, final char symbol) {
			final Map<LETTER, String> alphabetMapping = new HashMap<>();
			for (final LETTER letter : alphabet) {
				alphabetMapping.put(letter,
						quoteAndReplaceBackslashes(letter, Integer.toString(letter.hashCode() / sHashDivisor)));
			}
			return alphabetMapping;
		}
		
		@Override
		protected Map<STATE, String> getStateMapping(final Collection<STATE> states) {
			final Map<STATE, String> stateMapping = new HashMap<>();
			for (final STATE state : states) {
				stateMapping.put(state,
						quoteAndReplaceBackslashes(state, Integer.toString(state.hashCode() / sHashDivisor)));
			}
			return stateMapping;
		}
	}
	
	// --- Petri net writers ---
	
	@SuppressWarnings("squid:S1848")
	private void printPetriNet(final String name, final IPetriNet<LETTER, STATE> net, final Format format)
			throws AssertionError {
		if (!(net instanceof PetriNetJulian)) {
			throw new IllegalArgumentException("Unknown Petri net type. Only 'PetriNetJulian' is supported.");
		}
		
		final PetriNetJulian<LETTER, STATE> castNet = (PetriNetJulian<LETTER, STATE>) net;
		
		switch (format) {
			case ATS:
				new NetWriterToString(name, castNet);
				break;
			case ATS_QUOTED:
				new NetWriterToStringWithUniqueNumber(name, castNet);
				break;
			case ATS_NUMERATE:
				new NetWriterUniqueId(name, castNet);
				break;
			default:
				throw new AssertionError(UNSUPPORTED_LABELING);
		}
	}
	
	/**
	 * Prints a {@link PetriNetJulian}.
	 */
	private abstract class NetWriter {
		
		private final Map<LETTER, String> mAlphabet;
		private final Map<Place<LETTER, STATE>, String> mPlacesMapping;
		
		public NetWriter(final String name, final PetriNetJulian<LETTER, STATE> net) {
			mAlphabet = getAlphabetMapping(net.getAlphabet());
			mPlacesMapping = getPlacesMapping(net.getPlaces());
			
			print("PetriNet ");
			print(name);
			printAutomatonPrefix();
			printAlphabet();
			printPlaces();
			printTransitions(net.getTransitions());
			printInitialMarking(net.getInitialMarking());
			printAcceptingPlaces(net.getAcceptingPlaces());
			printAutomatonSuffix();
		}
		
		protected abstract Map<LETTER, String> getAlphabetMapping(final Collection<LETTER> alphabet);
		
		protected abstract Map<Place<LETTER, STATE>, String>
				getPlacesMapping(final Collection<Place<LETTER, STATE>> places);
				
		private void printAlphabet() {
			printCollectionPrefix("alphabet");
			printValues(mAlphabet);
			printCollectionSuffix();
		}
		
		private void printPlaces() {
			printCollectionPrefix("places");
			printValues(mPlacesMapping);
			printCollectionSuffix();
		}
		
		private void printTransitions(
				final Collection<ITransition<LETTER, STATE>> transitions) {
			printlnCollectionPrefix("transitions");
			for (final ITransition<LETTER, STATE> transition : transitions) {
				printTransition(transition);
			}
			printTransitionsSuffix();
		}
		
		private void printTransition(final ITransition<LETTER, STATE> transition) {
			printOneTransitionPrefix();
			printMarking(transition.getPredecessors());
			print(' ');
			print(mAlphabet.get(transition.getSymbol()));
			print(' ');
			printMarking(transition.getSuccessors());
			printOneTransitionSuffix();
		}
		
		private void printMarking(final Iterable<Place<LETTER, STATE>> marking) {
			print('{');
			for (final Place<LETTER, STATE> place : marking) {
				printElement(mPlacesMapping.get(place));
			}
			print('}');
		}
		
		private void printInitialMarking(final Marking<LETTER, STATE> initialMarking) {
			printElementPrefix("initialMarking");
			printMarking(initialMarking);
			println(',');
		}
		
		private void printAcceptingPlaces(final Collection<Place<LETTER, STATE>> acceptingPlaces) {
			printElementPrefix("acceptingPlaces");
			printMarking(acceptingPlaces);
			print(NEW_LINE);
		}
	}
	
	/**
	 * Prints a {@link PetriNetJulian}.
	 * In this version letters and places are represented by a default symbol and a unique ID.
	 */
	private final class NetWriterUniqueId extends NetWriter {
		
		public NetWriterUniqueId(final String name, final PetriNetJulian<LETTER, STATE> net) {
			super(name, net);
		}
		
		@Override
		protected Map<LETTER, String> getAlphabetMapping(final Collection<LETTER> alphabet) {
			int counter = 0;
			final Map<LETTER, String> alphabetMapping = new HashMap<>();
			for (final LETTER letter : alphabet) {
				alphabetMapping.put(letter, 'a' + Integer.toString(counter));
				counter++;
			}
			return alphabetMapping;
		}
		
		@Override
		protected Map<Place<LETTER, STATE>, String> getPlacesMapping(
				final Collection<Place<LETTER, STATE>> places) {
			int counter = 0;
			final HashMap<Place<LETTER, STATE>, String> placesMapping =
					new HashMap<>();
			for (final Place<LETTER, STATE> place : places) {
				placesMapping.put(place, 'p' + Integer.toString(counter));
				counter++;
			}
			return placesMapping;
		}
	}
	
	/**
	 * Prints a {@link PetriNetJulian}.
	 * In this version letters and places are represented by their {@link #toString()} method.
	 */
	private final class NetWriterToString extends NetWriter {
		
		public NetWriterToString(final String name, final PetriNetJulian<LETTER, STATE> net) {
			super(name, net);
		}
		
		@Override
		protected Map<LETTER, String> getAlphabetMapping(final Collection<LETTER> alphabet) {
			final Map<LETTER, String> alphabetMapping = new HashMap<>();
			for (final LETTER letter : alphabet) {
				alphabetMapping.put(letter, quoteAndReplaceBackslashes(letter));
			}
			return alphabetMapping;
		}
		
		@Override
		protected Map<Place<LETTER, STATE>, String> getPlacesMapping(
				final Collection<Place<LETTER, STATE>> places) {
			final HashMap<Place<LETTER, STATE>, String> placesMapping =
					new HashMap<>();
			for (final Place<LETTER, STATE> place : places) {
				placesMapping.put(place, quoteAndReplaceBackslashes(place));
			}
			return placesMapping;
		}
	}
	
	/**
	 * Prints a {@link PetriNetJulian}.
	 * In this version letters and places are represented by their {@link #toString()} method and a unique number.
	 */
	private final class NetWriterToStringWithUniqueNumber extends NetWriter {
		
		public NetWriterToStringWithUniqueNumber(final String name, final PetriNetJulian<LETTER, STATE> net) {
			super(name, net);
		}
		
		@Override
		protected Map<LETTER, String> getAlphabetMapping(final Collection<LETTER> alphabet) {
			int counter = 0;
			final Map<LETTER, String> alphabetMapping = new HashMap<>();
			for (final LETTER letter : alphabet) {
				alphabetMapping.put(letter, quoteAndReplaceBackslashes(letter, Integer.toString(counter)));
				counter++;
			}
			return alphabetMapping;
		}
		
		@Override
		protected Map<Place<LETTER, STATE>, String> getPlacesMapping(
				final Collection<Place<LETTER, STATE>> places) {
			int counter = 0;
			final HashMap<Place<LETTER, STATE>, String> placesMapping =
					new HashMap<>();
			for (final Place<LETTER, STATE> place : places) {
				placesMapping.put(place, quoteAndReplaceBackslashes(place, Integer.toString(counter)));
				counter++;
			}
			return placesMapping;
		}
	}
	
	// --- alternating automaton writers ---
	
	@SuppressWarnings({ "squid:S1848", "squid:S1301" })
	private void printAlternatingAutomaton(final String name, final AlternatingAutomaton<LETTER, STATE> alternating,
			final Format format) {
		switch (format) {
			case ATS:
				new AaWriter(name, alternating);
				break;
			default:
				throw new AssertionError(UNSUPPORTED_LABELING);
		}
	}
	
	/**
	 * Constructor takes a AlternatingAutomaton and writes it to a testfile.
	 */
	private class AaWriter {
		
		private final AlternatingAutomaton<LETTER, STATE> mAa;
		
		public AaWriter(final String name, final AlternatingAutomaton<LETTER, STATE> alternating) {
			
			mAa = alternating;
			
			print("AlternatingAutomaton ");
			print(name);
			printAutomatonPrefix();
			println(mAa.toString());
//			printAlphabet(mAa.getAlphabet());
//			printExistentialStates(mAa.getExistentialStates());
//			printUniversalStates(mAa.getUniversalStates());
//			printInitialStates(mAa.getInitialStates());
//			printFinalStates(mAa.getFinalStates());
//			printInternalTransitions(mAa.getTransitionsMap());
			printAutomatonSuffix();
		}
		
		/*
		private void printAlphabet(Set<LETTER> set) {
			mprintWriter.print(TAB + "alphabet = { ");
			for (LETTER letter : set) {
				mprintWriter.print(letter + ' ');
			}
			mprintWriter.print("},\n");
		}
		
		private void printExistentialStates(Set<STATE> set) {
			mprintWriter.print(TAB + "existentialStates = { ");
			for (STATE state : set) {
				mprintWriter.print(state + ' ');
			}
			mprintWriter.print("},\n");
		}
		
		private void printUniversalStates(Set<STATE> set) {
			mprintWriter.print(TAB + "universalStates = { ");
			for (STATE state : set) {
				mprintWriter.print(state + ' ');
			}
			mprintWriter.print("},\n");
		}
		
		private void printInitialStates(Set<STATE> set) {
			mprintWriter.print(TAB + "initialStates = { ");
			for (STATE state : set) {
				mprintWriter.print(state + ' ');
			}
			mprintWriter.print("},\n");
		}
		
		private void printFinalStates(Set<STATE> set) {
			mprintWriter.print(TAB + "finalStates = { ");
			for (STATE state : set) {
				mprintWriter.print(state + ' ');
			}
			mprintWriter.print("},\n");
		}
		
		private void printInternalTransitions(Map<STATE, Map<LETTER, Set<STATE>>> map) {
			mprintWriter.println(TAB + "internalTransitions = {");
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
			mprintWriter.println("\t},");
		}
		
		private void printInternalTransition(STATE pre, LETTER letter,
				STATE succ) {
			mprintWriter.println("\t\t (" +
					pre + ' ' +
					letter + ' ' +
					succ + ')'
			);
		}
		*/
	}
	
	// --- external tool writers ---
	
	/**
	 * Common methods for writers of external formats.
	 */
	private class CommonExternalFormatWriter {
		
		protected final Map<LETTER, String> mAlphabetMapping;
		protected final Map<STATE, String> mStateMapping;
		protected final INestedWordAutomaton<LETTER, STATE> mNwa;
		
		public CommonExternalFormatWriter(final INestedWordAutomaton<LETTER, STATE> nwa) {
			mAlphabetMapping = getAlphabetMapping(nwa.getInternalAlphabet());
			mStateMapping = getStateMapping(nwa.getStates());
			mNwa = nwa;
		}
		
		private Map<LETTER, String> getAlphabetMapping(final Collection<LETTER> alphabet) {
			int counter = 0;
			final Map<LETTER, String> alphabetMapping = new LinkedHashMap<>();
			for (final LETTER letter : alphabet) {
				alphabetMapping.put(letter, Integer.toString(counter));
				counter++;
			}
			return alphabetMapping;
		}
		
		private Map<STATE, String> getStateMapping(final Collection<STATE> states) {
			int counter = 0;
			final Map<STATE, String> stateMapping = new HashMap<>();
			for (final STATE state : states) {
				stateMapping.put(state, Integer.toString(counter));
				counter++;
			}
			return stateMapping;
		}
	}
	
	/**
	 * <tt>BA</tt> format writer.
	 */
	private class BaFormatWriter extends CommonExternalFormatWriter {
		
		private static final int MINIMUM_STATE_SIZE = 4;
		private static final int MINIMUM_TRANSITION_SIZE = 11;
		
		public BaFormatWriter(final INestedWordAutomaton<LETTER, STATE> nwa) {
			super(nwa);
			doPrint();
		}
		
		protected void doPrint() {
			final StringBuilder initStateSb = getStateString(mNwa.getInitialStates(), mStateMapping);
			final StringBuilder transSb = getTransitionString(mNwa, mStateMapping, mAlphabetMapping);
			final StringBuilder finalStateSb = getStateString(mNwa.getFinalStates(), mStateMapping);
			print(initStateSb);
			print(transSb);
			print(finalStateSb);
		}
		
		private StringBuilder getStateString(
				final Collection<STATE> initialStates,
				final Map<STATE, String> stateMapping) {
			final StringBuilder result = new StringBuilder(MINIMUM_STATE_SIZE * initialStates.size());
			for (final STATE state : initialStates) {
				// @formatter:off
				result.append('[')
						.append(stateMapping.get(state))
						.append(']')
						.append(NEW_LINE);
				// @formatter:on
			}
			return result;
		}
		
		private StringBuilder getTransitionString(
				final INestedWordAutomaton<LETTER, STATE> nwa,
				final Map<STATE, String> stateMapping,
				final Map<LETTER, String> alphabetMapping) {
			final StringBuilder result = new StringBuilder(MINIMUM_TRANSITION_SIZE * nwa.size());
			for (final STATE state : nwa.getStates()) {
				for (final OutgoingInternalTransition<LETTER, STATE> outTrans : nwa.internalSuccessors(state)) {
					// @formatter:off
					result.append(alphabetMapping.get(outTrans.getLetter()))
							.append(",[")
							.append(stateMapping.get(state))
							.append("]->[")
							.append(stateMapping.get(outTrans.getSucc()))
							.append(']')
							.append(NEW_LINE);
					// @formatter:on
				}
			}
			return result;
		}
	}
	
	/**
	 * <tt>Hanoi</tt> format writer.
	 */
	@SuppressWarnings("squid:S1698")
	private class HanoiFormatWriter extends CommonExternalFormatWriter {
		
		private static final int MINIMUM_HEADER_SIZE = 137;
		private static final int MINIMUM_STATE_SIZE = 15;
		
		private static final boolean USE_LABELS = false;
		private final IConverter<LETTER> mLetterConverter;
		
		public HanoiFormatWriter(final INestedWordAutomaton<LETTER, STATE> nwa) {
			super(nwa);
			if (USE_LABELS) {
				mLetterConverter = new ToStringConverter<>();
			} else {
				mLetterConverter = new MapBasedConverter<>(mAlphabetMapping, "");
			}
			doPrint();
		}
		
		protected void doPrint() {
			final StringBuilder header = constructHeader();
			print(header);
			final String bodyToken = "--BODY--";
			print(bodyToken);
			print(NEW_LINE);
			final StringBuilder body = constructBody();
			print(body);
			final String endToken = "--END--";
			print(endToken);
		}
		
		private StringBuilder constructHeader() {
			final StringBuilder builder = new StringBuilder(MINIMUM_HEADER_SIZE);
			// @formatter:off
			builder.append("HOA: v1")
					.append(NEW_LINE)
					//
					.append("States: ")
					.append(mNwa.getStates().size())
					.append(NEW_LINE);
					
			for (final STATE state : mNwa.getInitialStates()) {
				builder.append("Start: ")
						.append(mStateMapping.get(state))
						.append(NEW_LINE);
			}
			
			builder.append("AP: ")
					.append(mNwa.getInternalAlphabet().size());
			for (final LETTER letter : mNwa.getInternalAlphabet()) {
				builder.append(" \"p")
						.append(mLetterConverter.convert(letter) + QUOTE);
			}
			builder.append(NEW_LINE);
			
			for (final LETTER letter : mNwa.getInternalAlphabet()) {
				builder.append("Alias: @")
						.append(mAlphabetMapping.get(letter));
				boolean firstOther = true;
				for (final LETTER otherLetter : mNwa.getInternalAlphabet()) {
					if (firstOther) {
						firstOther = false;
					} else {
						builder.append(" &");
					}
					// comparison with '==' is fine here as the letters come from a set
					if (otherLetter == letter) {
						builder.append(' ')
								.append(mAlphabetMapping.get(otherLetter));
					} else {
						builder.append(" !")
								.append(mAlphabetMapping.get(otherLetter));
					}
				}
				builder.append(NEW_LINE);
			}
			
			builder.append("Acceptance: 1 Inf(0)")
					.append(NEW_LINE)
					//
					.append("acc-name: Buchi")
					.append(NEW_LINE)
					//
					.append("tool: \"Ultimate Automata Library\"")
					.append(NEW_LINE);
			// @formatter:on
			
			return builder;
		}
		
		private StringBuilder constructBody() {
			final StringBuilder builder = new StringBuilder(MINIMUM_STATE_SIZE * mNwa.size());
			
			for (final STATE state : mNwa.getStates()) {
				// @formatter:off
				builder.append("State: ")
						.append(mStateMapping.get(state));
				if (USE_LABELS) {
					builder.append(" \"")
							.append(state)
							.append(QUOTE);
				}
				if (mNwa.isFinal(state)) {
					builder.append(" {0}");
				}
				builder.append(NEW_LINE);
				for (final LETTER letter : mNwa.lettersInternal(state)) {
					for (final OutgoingInternalTransition<LETTER, STATE> tes : mNwa.internalSuccessors(state, letter)) {
						builder.append("[@")
								.append(mAlphabetMapping.get(tes.getLetter()))
								.append("] ")
								.append(mStateMapping.get(tes.getSucc()))
								.append(NEW_LINE);
					}
				}
				// @formatter:on
			}
			return builder;
		}
	}
	
	/**
	 * <tt>GOAL</tt> format writer.
	 */
	private class GoalFormatWriter extends CommonExternalFormatWriter {
		
		private static final int MINIMUM_SKELETON_SIZE = 130;
		private static final String STATE_ID_CLOSE = "</StateID>";
		private static final String STATE_ID_OPEN = "<StateID>";
		private final IConverter<LETTER> mLetterConverter;
		private final IConverter<STATE> mStateConverter;
		
		private static final char TAB = '\t';
		
		public GoalFormatWriter(final INestedWordAutomaton<LETTER, STATE> nwa) {
			super(nwa);
			mLetterConverter = new MapBasedConverter<>(mAlphabetMapping, "");
			mStateConverter = new MapBasedConverter<>(mStateMapping, "");
			doPrint();
		}
		
		protected void doPrint() {
			final StringBuilder builder = new StringBuilder(MINIMUM_SKELETON_SIZE);
			// @formatter:off
			builder.append("<?xml version=\"1.0\" encoding=\"UTF-8\" standalone=\"no\"?>")
					.append(NEW_LINE)
					.append("<Structure label-on=\"Transition\" type=\"FiniteStateAutomaton\">")
					.append(NEW_LINE);
			// @formatter:on
			constructAlphabetSection(builder);
			constructStateSection(builder);
			constructInitialStateSection(builder);
			constructTransitionSection(builder);
			constructAcceptingStateSection(builder);
			// @formatter:off
			builder.append("</Structure>")
					.append(NEW_LINE);
			// @formatter:on
			
			print(builder);
		}
		
		private void constructAlphabetSection(final StringBuilder builder) {
			// @formatter:off
			builder.append(TAB)
					.append("<Alphabet type=\"Classical\">")
					.append(NEW_LINE);
			for (final LETTER letter : mNwa.getInternalAlphabet()) {
				builder.append(TAB)
						.append(TAB)
						.append("<Symbol>")
						.append(mLetterConverter.convert(letter))
						.append("</Symbol>")
						.append(NEW_LINE);
			}
			builder.append(TAB)
					.append("</Alphabet>")
					.append(NEW_LINE);
			// @formatter:on
		}
		
		private void constructStateSection(final StringBuilder builder) {
			// @formatter:off
			builder.append(TAB)
					.append("<StateSet>")
					.append(NEW_LINE);
			for (final STATE state : mNwa.getStates()) {
				builder.append(TAB)
						.append(TAB)
						.append("<State sid=\"")
						.append(mStateConverter.convert(state))
						.append("\" />")
						.append(NEW_LINE);
			}
			builder.append(TAB)
					.append("</StateSet>")
					.append(NEW_LINE);
			// @formatter:on
		}
		
		private void constructInitialStateSection(final StringBuilder builder) {
			// @formatter:off
			builder.append(TAB)
					.append("<InitialStateSet>")
					.append(NEW_LINE);
			for (final STATE state : mNwa.getInitialStates()) {
				builder.append(TAB)
						.append(TAB)
						.append(STATE_ID_OPEN)
						.append(mStateConverter.convert(state))
						.append(STATE_ID_CLOSE)
						.append(NEW_LINE);
			}
			builder.append(TAB)
					.append("</InitialStateSet>")
					.append(NEW_LINE);
			// @formatter:on
		}
		
		private void constructTransitionSection(final StringBuilder builder) {
			int tid = 0;
			// @formatter:off
			builder.append(TAB)
					.append("<TransitionSet complete=\"false\">")
					.append(NEW_LINE);
			for (final STATE state : mNwa.getStates()) {
				for (final OutgoingInternalTransition<LETTER, STATE> trans : mNwa.internalSuccessors(state)) {
					builder.append(TAB)
							.append(TAB)
							.append("<Transition tid=\"")
							.append(tid)
							.append("\"><From>")
							.append(mStateConverter.convert(state))
							.append("</From><To>")
							.append(mStateConverter.convert(trans.getSucc()))
							.append("</To><Label>")
							.append(mLetterConverter.convert(trans.getLetter()))
							.append("</Label></Transition>")
							.append(NEW_LINE);
					tid++;
				}
			}
			builder.append(TAB)
					.append("</TransitionSet>")
					.append(NEW_LINE);
			// @formatter:on
		}
		
		private void constructAcceptingStateSection(final StringBuilder builder) {
			// @formatter:off
			builder.append(TAB)
					.append("<Acc type=\"Buchi\">")
					.append(NEW_LINE);
			for (final STATE state : mNwa.getFinalStates()) {
				builder.append(TAB)
						.append(TAB)
						.append(STATE_ID_OPEN)
						.append(mStateConverter.convert(state))
						.append(STATE_ID_CLOSE)
						.append(NEW_LINE);
			}
			builder.append(TAB)
					.append("</Acc>")
					.append(NEW_LINE);
			// @formatter:on
		}
	}
	
	/**
	 * Converts a parametric object to a {@link String}.
	 *
	 * @param <E>
	 *            type of object to print
	 */
	@FunctionalInterface
	private interface IConverter<E> {
		String convert(E elem);
	}
	
	/**
	 * Uses the {@link String#valueOf(Object)} method for printing.
	 * 
	 * @param <E>
	 *            type of object to print
	 */
	private static class ToStringConverter<E> implements IConverter<E> {
		@Override
		public String convert(final E elem) {
			return elem.toString();
		}
	}
	
	/**
	 * Uses the {@link String#valueOf(Object)} method and a prefix map for printing.
	 * <p>
	 * TODO Christian 2016-08-21: The field {@code mPrefix} is empty in all calls to the constructor. It could be
	 * removed.
	 * 
	 * @param <E>
	 *            type of object to print
	 * @param <V>
	 *            type of mapped object
	 */
	private static class MapBasedConverter<E, V> implements IConverter<E> {
		
		private final Map<E, V> mMap;
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
			return mPrefix + value;
		}
	}
}
