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
import java.util.Date;
import java.util.Locale;
import java.util.Objects;
import java.util.function.Supplier;

import de.uni_freiburg.informatik.ultimate.automata.alternating.AlternatingAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.counting.CountingAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.counting.datastructures.CountingAutomatonDataStructure;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.visualization.BaFormatWriter;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.visualization.GoalFormatWriter;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.visualization.HanoiFormatWriter;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.tree.IRankedLetter;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 * Writes the automaton definition for given automata. Writing can either be to a string or to a file.
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
	private static final String UNSUPPORTED_LABELING = "Unsupported labeling.";
	private static final int ONE = 1;

	// enable writing automata, e.g., when an error occurs
	private static final boolean DUMP_AUTOMATON = false;

	/**
	 * Output format types.
	 */
	public enum Format {
		/**
		 * Automata script.<br>
		 * The {@link #toString()} representation of {@link LETTER} and {@link STATE} is used.
		 */
		ATS(AtsFormat::new),
		/**
		 * Automata script.<br>
		 * The {@link #toString()} representations of {@link LETTER} and {@link STATE} are ignored. The
		 * {@link TestFileWriter} introduces new names, e.g. the letters of the alphabet are <tt>a0, ..., an</tt>.
		 */
		ATS_NUMERATE(AtsFormat.AtsNumerateFormat::new),
		/**
		 * Automata script.<br>
		 * The {@link #toString()} representation of {@link LETTER} and {@link STATE} plus a number is used.
		 */
		ATS_QUOTED(AtsFormat.AtsQuotedFormat::new),
		/**
		 * The <tt>BA</tt> format which is also used by some tools of Yu-Fang Chen.
		 */
		BA(BaFormat::new),
		/**
		 * (GOAL File Format) - The XML file format used by <tt>GOAL</tt>.
		 */
		GFF(GffFormat::new),
		/**
		 * The <tt>Hanoi Omega Automaton</tt> format.
		 */
		HOA(HoaFormat::new);

		private final Supplier<IFormat> mFormatSupplier;

		Format(final Supplier<IFormat> formatSupplier) {
			mFormatSupplier = formatSupplier;
		}

		public IFormat getFormat() {
			return mFormatSupplier.get();
		}
	}

	private final AutomataLibraryServices mServices;
	private final ILogger mLogger;

	/**
	 * Base constructor.
	 *
	 * @param services
	 *            Ultimate services
	 */
	private AutomatonDefinitionPrinter(final AutomataLibraryServices services) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
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
	 * @param append
	 *            whether the automata should be added at the end of the file (true) or replace the content of the file
	 *            (false)
	 */
	public AutomatonDefinitionPrinter(final AutomataLibraryServices services, final String automatonName,
			final String fileName, final IFormat format, final String message, final boolean append,
			final IAutomaton<?, ?>... automata) {
		this(services);
		final FileWriter fileWriter = getFileWriterWithOptionalAppend(fileName, format, append);
		if (fileWriter != null) {
			if (mLogger.isWarnEnabled()) {
				mLogger.warn(String.format("Dumping automata %s to %s", automatonName, fileName));
			}
			final PrintWriter printWriter = new PrintWriter(fileWriter);
			printAutomataToFileWriter(mServices, printWriter, automatonName, format, message, automata);
		}
	}

	public AutomatonDefinitionPrinter(final AutomataLibraryServices services, final String automatonName,
			final String fileName, final Format format, final String message, final boolean append,
			final IAutomaton<?, ?>... automata) {
		this(services, automatonName, fileName, format.getFormat(), message, append, automata);
	}

	public AutomatonDefinitionPrinter(final AutomataLibraryServices services, final String automatonName,
			final String fileName, final IFormat format, final String message, final IAutomaton<?, ?>... automata) {
		this(services, automatonName, fileName, format, message, false, automata);
	}

	public AutomatonDefinitionPrinter(final AutomataLibraryServices services, final String automatonName,
			final String fileName, final Format format, final String message, final IAutomaton<?, ?>... automata) {
		this(services, automatonName, fileName, format.getFormat(), message, automata);
	}

	public static String toString(final AutomataLibraryServices services, final String automatonName,
			final IAutomaton<?, ?> automaton) {
		final StringWriter stringWriter = new StringWriter();
		final PrintWriter printWriter = new PrintWriter(stringWriter);
		printAutomaton(services, new NamedAutomaton<>(automatonName, automaton), Format.ATS.getFormat(), printWriter);
		return stringWriter.toString();
	}

	public static void writeAutomatonToFile(final AutomataLibraryServices services, final String fileName,
			final Format format, final String atsHeaderMessage, final String atsCommands,
			final NamedAutomaton<?, ?>... nas) {
		writeAutomatonToFile(services, fileName, format.getFormat(), atsHeaderMessage, atsCommands, nas);
	}

	public static void writeAutomatonToFile(final AutomataLibraryServices services, final String fileName,
			final IFormat format, final String atsHeaderMessage, final String atsCommands,
			final NamedAutomaton<?, ?>... nas) {
		final File file = new File(fileName + '.' + format.getFileEnding());
		final FileWriter fileWriter;
		try {
			fileWriter = new FileWriter(file);
		} catch (final IOException e) {
			throw new AssertionError("Unable to create file writer for " + fileName);
		}
		final PrintWriter printWriter = new PrintWriter(fileWriter);
		try {
			format.printHeader(printWriter, atsHeaderMessage);
			printWriter.println();
			printWriter.println(atsCommands);
			printWriter.println();
			for (final NamedAutomaton<?, ?> na : nas) {
				printAutomaton(services, na, format, printWriter);
			}
		} finally {
			printWriter.close();
			try {
				fileWriter.close();
			} catch (final IOException e) {
				throw new AssertionError("failed to close file writer");
			}
		}
	}

	/**
	 * Writes the passed {@link IAutomaton} objects to files if the option is enabled. Does nothing otherwise.
	 * <p>
	 * This method is intended to be used for dumping automata when an error occurs e.g., when the
	 * {@link IOperation#checkResult()} method fails.
	 *
	 * @param services
	 *            Ultimate services
	 * @param fileNamePrefix
	 *            prefix of the file name (e.g., operation name)
	 * @param message
	 *            message to be printed in the file
	 * @param automata
	 *            sequence of automata to be printed
	 */
	@SafeVarargs
	@SuppressWarnings({ "findbugs:UC_USELESS_VOID_METHOD" })
	public static void writeToFileIfPreferred(final AutomataLibraryServices services, final String fileNamePrefix,
			final String message, final IAutomaton<?, ?>... automata) {
		if (!DUMP_AUTOMATON) {
			return;
		}
		final String workingDirectory = System.getProperty("user.dir");
		final String fileName = workingDirectory + File.separator + fileNamePrefix + getDateTimeFileName();
		new AutomatonDefinitionPrinter<>(services, fileNamePrefix, fileName, Format.ATS_NUMERATE, message, automata);
	}

	/**
	 * @param append
	 *
	 */
	private FileWriter getFileWriterWithOptionalAppend(final String fileName, final IFormat format,
			final boolean append) {
		final File testfile = new File(fileName + '.' + format.getFileEnding());
		try {
			return new FileWriter(testfile, append);
		} catch (final IOException e) {
			if (mLogger.isErrorEnabled()) {
				mLogger.error("Creating FileWriter did not work.", e);
			}
			return null;
		}
	}

	/**
	 * Date/time string used for file names (no special characters).
	 *
	 * @return date/time string
	 */
	private static String getDateTimeFileName() {
		return getDateTimeFromFormat("yyyyMMddHHmmss");
	}

	static String getDateTimeFromFormat(final String format) {
		final DateFormat dateFormat = new SimpleDateFormat(format, Locale.ENGLISH);
		final Date date = new Date();
		return dateFormat.format(date);
	}

	private static void printAutomataToFileWriter(final AutomataLibraryServices services, final PrintWriter printWriter,
			final String automatonName, final IFormat format, final String atsHeaderMessage,
			final IAutomaton<?, ?>... automata) {
		format.printHeader(printWriter, atsHeaderMessage);
		if (automata.length == ONE) {
			printAutomaton(services, new NamedAutomaton<>(automatonName, automata[0]), format, printWriter);
		} else {
			for (int i = 0; i < automata.length; i++) {
				printAutomaton(services, new NamedAutomaton<>(automatonName + i, automata[i]), format, printWriter);
			}
		}
		printWriter.close();
	}

	/**
	 * Determines the input automaton type and calls the respective print method.
	 *
	 * @param services
	 *
	 * @param name
	 *            name of the automaton in the output
	 * @param automaton
	 *            automaton object
	 * @param format
	 *            output format
	 * @param printWriter
	 */
	private static <LETTER, STATE> void printAutomaton(final AutomataLibraryServices services,
			final NamedAutomaton<LETTER, STATE> na, final IFormat format, final PrintWriter printWriter) {
		if (na.getAutomaton() instanceof INwaOutgoingLetterAndTransitionProvider) {
			printNestedWordAutomaton(services, na.getName(),
					(INwaOutgoingLetterAndTransitionProvider<LETTER, STATE>) na.getAutomaton(), format, printWriter);
		} else if (na.getAutomaton() instanceof IPetriNet) {
			printPetriNet(na.getName(), (IPetriNet<LETTER, STATE>) na.getAutomaton(), format, printWriter);
		} else if (na.getAutomaton() instanceof AlternatingAutomaton) {
			format.printAlternatingAutomaton(printWriter, na.getName(),
					(AlternatingAutomaton<LETTER, STATE>) na.getAutomaton());
		} else if (na.getAutomaton() instanceof TreeAutomatonBU<?, ?>) {
			format.printTreeAutomaton(printWriter, na.getName(), (TreeAutomatonBU<?, STATE>) na.getAutomaton());
		} else if (na.getAutomaton() instanceof BranchingProcess<?, ?>) {
			format.printBranchingProcess(printWriter, na.getName(),
					(BranchingProcess<LETTER, STATE>) na.getAutomaton());
		} else if (na.getAutomaton() instanceof CountingAutomaton) {
			format.printCountingAutomaton(printWriter, na.getName(),
					(CountingAutomaton<LETTER, STATE>) na.getAutomaton());
		} else if (na.getAutomaton() instanceof CountingAutomatonDataStructure) {
			format.printCountingAutomatonDataStructure(printWriter, na.getName(),
					(CountingAutomatonDataStructure<LETTER, STATE>) na.getAutomaton());
		} else {
			throw new AssertionError("unknown kind of automaton");
		}
	}

	private static <LETTER, STATE> void printNestedWordAutomaton(final AutomataLibraryServices services,
			final String name, final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> automaton,
			final IFormat format, final PrintWriter printWriter) throws AssertionError {
		INestedWordAutomaton<LETTER, STATE> nwa;
		if (automaton instanceof INestedWordAutomaton) {
			nwa = (INestedWordAutomaton<LETTER, STATE>) automaton;
		} else {
			try {
				nwa = new NestedWordAutomatonReachableStates<>(services, automaton);
			} catch (final AutomataOperationCanceledException e) {
				throw new AssertionError("Timeout while preparing automaton for printing.");
			}
		}
		format.printNestedWordAutomaton(printWriter, name, nwa);
	}

	private static <LETTER, STATE> void printPetriNet(final String name, final IPetriNet<LETTER, STATE> net,
			final IFormat format, final PrintWriter printWriter) throws AssertionError {
		if (!(net instanceof BoundedPetriNet)) {
			final String msg =
					"Unknown Petri net type. Only supported type is " + BoundedPetriNet.class.getSimpleName();
			throw new IllegalArgumentException(msg);
		}

		final BoundedPetriNet<LETTER, STATE> castNet = (BoundedPetriNet<LETTER, STATE>) net;
		format.printPetriNet(printWriter, name, castNet);
	}

	private static void ensureNoCallReturn(final IFormat format, final INestedWordAutomaton<?, ?> nwa) {
		if (!NestedWordAutomataUtils.isFiniteAutomaton(nwa)) {
			throw new UnsupportedOperationException(
					format.getClass().getSimpleName() + " does not support call transitions or return transitions");
		}
	}

	static void failUnsupported() {
		throw new AssertionError(UNSUPPORTED_LABELING);
	}

	public static class NamedAutomaton<LETTER, STATE> {
		private final String mName;
		private final IAutomaton<LETTER, STATE> mAutomaton;

		public NamedAutomaton(final String name, final IAutomaton<LETTER, STATE> automaton) {
			super();
			Objects.requireNonNull(name);
			Objects.requireNonNull(automaton);
			mName = name;
			mAutomaton = automaton;
		}

		public String getName() {
			return mName;
		}

		public IAutomaton<LETTER, STATE> getAutomaton() {
			return mAutomaton;
		}
	}

	/**
	 * Defines how various kinds of automata are printed as strings.
	 *
	 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
	 *
	 */
	public interface IFormat {
		String getFileEnding();

		default void printHeader(final PrintWriter pw, final String header) {
			// do nothing
		}

		<L, S> void printNestedWordAutomaton(final PrintWriter printWriter, final String name,
				INestedWordAutomaton<L, S> nwa);

		default <L, S> void printCountingAutomaton(final PrintWriter printWriter, final String name,
				final CountingAutomaton<L, S> automaton) {
			failUnsupported();
		}

		default <L, S> void printTreeAutomaton(final PrintWriter printWriter, final String name,
				final TreeAutomatonBU<? extends IRankedLetter, S> automaton) {
			failUnsupported();
		}

		default <L, S> void printCountingAutomatonDataStructure(final PrintWriter printWriter, final String name,
				final CountingAutomatonDataStructure<L, S> automaton) {
			failUnsupported();
		}

		default <L, S> void printPetriNet(final PrintWriter printWriter, final String name,
				final BoundedPetriNet<L, S> net) {
			failUnsupported();
		}

		default <L, S> void printAlternatingAutomaton(final PrintWriter printWriter, final String name,
				final AlternatingAutomaton<L, S> alternating) {
			failUnsupported();
		}

		default <L, S> void printBranchingProcess(final PrintWriter printWriter, final String name,
				final BranchingProcess<L, S> branchingProcess) {
			failUnsupported();
		}
	}

	private static class BaFormat implements IFormat {
		@Override
		public String getFileEnding() {
			return "ba";
		}

		@Override
		public <L, S> void printNestedWordAutomaton(final PrintWriter printWriter, final String name,
				final INestedWordAutomaton<L, S> nwa) {
			ensureNoCallReturn(this, nwa);
			new BaFormatWriter<>(printWriter, nwa);
		}
	}

	private static class GffFormat implements IFormat {
		@Override
		public String getFileEnding() {
			return "gff";
		}

		@Override
		public <L, S> void printNestedWordAutomaton(final PrintWriter printWriter, final String name,
				final INestedWordAutomaton<L, S> nwa) {
			ensureNoCallReturn(this, nwa);
			new GoalFormatWriter<>(printWriter, nwa);
		}
	}

	private static class HoaFormat implements IFormat {
		@Override
		public String getFileEnding() {
			return "hoa";
		}

		@Override
		public <L, S> void printNestedWordAutomaton(final PrintWriter printWriter, final String name,
				final INestedWordAutomaton<L, S> nwa) {
			ensureNoCallReturn(this, nwa);
			new HanoiFormatWriter<>(printWriter, nwa);
		}
	}
}
