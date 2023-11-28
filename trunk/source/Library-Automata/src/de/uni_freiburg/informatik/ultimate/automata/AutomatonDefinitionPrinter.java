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

import de.uni_freiburg.informatik.ultimate.automata.alternating.AlternatingAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.alternating.visualization.AlternatingAutomatonWriter;
import de.uni_freiburg.informatik.ultimate.automata.counting.CaWriter;
import de.uni_freiburg.informatik.ultimate.automata.counting.CountingAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.counting.datastructures.CaDatastructureWriter;
import de.uni_freiburg.informatik.ultimate.automata.counting.datastructures.CountingAutomatonDataStructure;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.visualization.BaFormatWriter;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.visualization.GoalFormatWriter;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.visualization.HanoiFormatWriter;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.visualization.INwaAtsFormatter;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.visualization.NwaWriter;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.visualization.BranchingProcessWriterToString;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.visualization.IPetriAtsFormatter;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.visualization.NetWriter;
import de.uni_freiburg.informatik.ultimate.automata.tree.IRankedLetter;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.visualization.TreeAutomatonWriter;
import de.uni_freiburg.informatik.ultimate.automata.tree.visualization.TreeAutomatonWriterUniqueId;
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
	private static final String ATS_EXTENSION = "ats";

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
		ATS(ATS_EXTENSION),
		/**
		 * Automata script.<br>
		 * The {@link #toString()} representations of {@link LETTER} and {@link STATE} are ignored. The
		 * {@link TestFileWriter} introduces new names, e.g. the letters of the alphabet are <tt>a0, ..., an</tt>.
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
			final String fileName, final Format format, final String message, final boolean append,
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
			final String fileName, final Format format, final String message, final IAutomaton<?, ?>... automata) {
		this(services, automatonName, fileName, format, message, false, automata);
	}

	public static String toString(final AutomataLibraryServices services, final String automatonName,
			final IAutomaton<?, ?> automaton) {
		final StringWriter stringWriter = new StringWriter();
		final PrintWriter printWriter = new PrintWriter(stringWriter);
		printAutomaton(services, new NamedAutomaton<>(automatonName, automaton), Format.ATS, printWriter);
		return stringWriter.toString();
	}

	public static void writeAutomatonToFile(final AutomataLibraryServices services, final String fileName,
			final Format format, final String atsHeaderMessage, final String atsCommands,
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
			printWriter.append(generateDefaultAtsHeader(atsHeaderMessage));
			printWriter.append(System.lineSeparator());
			printWriter.append(atsCommands);
			printWriter.append(System.lineSeparator());
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
	private FileWriter getFileWriterWithOptionalAppend(final String fileName, final Format format,
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

	private static void printAutomataToFileWriter(final AutomataLibraryServices services, final PrintWriter printWriter,
			final String automatonName, final Format format, final String atsHeaderMessage,
			final IAutomaton<?, ?>... automata) {
		switch (format) {
		case ATS:
		case ATS_NUMERATE:
		case ATS_QUOTED:
			printWriter.println(generateDefaultAtsHeader(atsHeaderMessage));
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
			printAutomaton(services, new NamedAutomaton<>(automatonName, automata[0]), format, printWriter);
		} else {
			for (int i = 0; i < automata.length; i++) {
				printAutomaton(services, new NamedAutomaton<>(automatonName + i, automata[i]), format, printWriter);
			}
		}
		printWriter.close();
	}

	private static String generateDefaultAtsHeader(final String atsHeaderMessage) {
		return "// Testfile dumped by Ultimate at " + getDateTimeNice() + System.lineSeparator() + "//"
				+ System.lineSeparator() + "// " + atsHeaderMessage + System.lineSeparator();
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
			final NamedAutomaton<LETTER, STATE> na, final Format format, final PrintWriter printWriter) {
		if (na.getAutomaton() instanceof INwaOutgoingLetterAndTransitionProvider) {
			printNestedWordAutomaton(services, na.getName(),
					(INwaOutgoingLetterAndTransitionProvider<LETTER, STATE>) na.getAutomaton(), format, printWriter);
		} else if (na.getAutomaton() instanceof IPetriNet) {
			printPetriNet(na.getName(), (IPetriNet<LETTER, STATE>) na.getAutomaton(), format, printWriter);
		} else if (na.getAutomaton() instanceof AlternatingAutomaton) {
			printAlternatingAutomaton(na.getName(), (AlternatingAutomaton<LETTER, STATE>) na.getAutomaton(), format,
					printWriter);
		} else if (na.getAutomaton() instanceof TreeAutomatonBU<?, ?>) {
			printTreeAutomaton(na.getName(), (TreeAutomatonBU<?, STATE>) na.getAutomaton(), format, printWriter);
		} else if (na.getAutomaton() instanceof BranchingProcess<?, ?>) {
			printBranchingProcess(na.getName(), (BranchingProcess<LETTER, STATE>) na.getAutomaton(), format,
					printWriter);
		} else if (na.getAutomaton() instanceof CountingAutomaton) {
			printCountingAutomaton(na.getName(), (CountingAutomaton<LETTER, STATE>) na.getAutomaton(), format, printWriter);
		} else if (na.getAutomaton() instanceof CountingAutomatonDataStructure) {
			printCountingAutomatonDataStructure(na.getName(),
					(CountingAutomatonDataStructure<LETTER, STATE>) na.getAutomaton(), format, printWriter);
		} else {
			throw new AssertionError("unknown kind of automaton");
		}
	}

	private static <LETTER, STATE> void printTreeAutomaton(final String name,
			final TreeAutomatonBU<? extends IRankedLetter, STATE> automaton, final Format format,
			final PrintWriter printWriter) {
		switch (format) {
		case ATS:
			new TreeAutomatonWriter<>(printWriter, name, automaton);
			break;
		case ATS_NUMERATE:
			new TreeAutomatonWriterUniqueId<>(printWriter, name, automaton);
			break;
		case ATS_QUOTED:
		case BA:
		case GFF:
		case HOA:
		default:
			throw new AssertionError(UNSUPPORTED_LABELING);
		}
	}

	private static <LETTER, STATE> void printNestedWordAutomaton(final AutomataLibraryServices services,
			final String name, final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> automaton,
			final Format format, final PrintWriter printWriter) throws AssertionError {
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
		switch (format) {
		case ATS:
			new NwaWriter<>(printWriter, name, nwa, new INwaAtsFormatter.ToString<>());
			break;
		case ATS_QUOTED:
			new NwaWriter<>(printWriter, name, nwa, new INwaAtsFormatter.ToStringWithHash<>());
			break;
		case ATS_NUMERATE:
			new NwaWriter<>(printWriter, name, nwa, new INwaAtsFormatter.UniqueId<>());
			break;
		case BA:
			if (!NestedWordAutomataUtils.isFiniteAutomaton(nwa)) {
				throw new UnsupportedOperationException(
						format + " format does not support call transitions or return transitions");
			}
			new BaFormatWriter<>(printWriter, nwa);
			break;
		case HOA:
			if (!NestedWordAutomataUtils.isFiniteAutomaton(nwa)) {
				throw new UnsupportedOperationException(
						format + " format does not support call transitions or return transitions");
			}
			new HanoiFormatWriter<>(printWriter, nwa);
			break;
		case GFF:
			if (!NestedWordAutomataUtils.isFiniteAutomaton(nwa)) {
				throw new UnsupportedOperationException(
						format + " format does not support call transitions or return transitions");
			}
			new GoalFormatWriter<>(printWriter, nwa);
			break;
		default:
			throw new AssertionError(UNSUPPORTED_LABELING);
		}
	}

	private static <LETTER, STATE> void printCountingAutomaton(final String name,
			final CountingAutomaton<LETTER, STATE> automaton, final Format format, final PrintWriter printWriter) {
		switch (format) {
		case ATS:
			new CaWriter<>(printWriter, name, automaton);
			break;
		case ATS_QUOTED:
		case ATS_NUMERATE:
		case BA:
		case HOA:
		case GFF:
		default:
			throw new AssertionError(UNSUPPORTED_LABELING);
		}
	}

	private static <LETTER, STATE> void printCountingAutomatonDataStructure(final String name,
			final CountingAutomatonDataStructure<LETTER, STATE> automaton, final Format format, final PrintWriter printWriter) {
		switch (format) {
		case ATS:
			new CaDatastructureWriter<>(printWriter, name, automaton);
			break;
		case ATS_QUOTED:
		case ATS_NUMERATE:
		case BA:
		case HOA:
		case GFF:
		default:
			throw new AssertionError(UNSUPPORTED_LABELING);
		}
	}

	private static <LETTER, STATE> void printPetriNet(final String name, final IPetriNet<LETTER, STATE> net,
			final Format format, final PrintWriter printWriter) throws AssertionError {
		if (!(net instanceof BoundedPetriNet)) {
			final String msg =
					"Unknown Petri net type. Only supported type is " + BoundedPetriNet.class.getSimpleName();
			throw new IllegalArgumentException(msg);
		}

		final BoundedPetriNet<LETTER, STATE> castNet = (BoundedPetriNet<LETTER, STATE>) net;

		switch (format) {
		case ATS:
			new NetWriter<>(printWriter, name, castNet, new IPetriAtsFormatter.ToString<>());
			break;
		case ATS_QUOTED:
			new NetWriter<>(printWriter, name, castNet, new IPetriAtsFormatter.ToStringWithUniqueNumber<>());
			break;
		case ATS_NUMERATE:
			new NetWriter<>(printWriter, name, castNet, new IPetriAtsFormatter.UniqueId<>());
			break;
		case BA:
		case GFF:
		case HOA:
		default:
			throw new AssertionError(UNSUPPORTED_LABELING);
		}
	}

	private static <LETTER, STATE> void printAlternatingAutomaton(final String name,
			final AlternatingAutomaton<LETTER, STATE> alternating, final Format format, final PrintWriter printWriter) {
		switch (format) {
		case ATS:
			new AlternatingAutomatonWriter<>(printWriter, name, alternating);
			break;
		case ATS_QUOTED:
		case ATS_NUMERATE:
		case BA:
		case GFF:
		case HOA:
		default:
			throw new AssertionError(UNSUPPORTED_LABELING);
		}
	}

	private static <LETTER, STATE> void printBranchingProcess(final String name,
			final BranchingProcess<LETTER, STATE> branchingProcess, final Format format, final PrintWriter printWriter)
			throws AssertionError {
		switch (format) {
		case ATS:
			new BranchingProcessWriterToString<>(printWriter, name, branchingProcess);
			break;
		case ATS_QUOTED:
		case ATS_NUMERATE:
		case BA:
		case GFF:
		case HOA:
		default:
			throw new AssertionError(UNSUPPORTED_LABELING);
		}
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
}
