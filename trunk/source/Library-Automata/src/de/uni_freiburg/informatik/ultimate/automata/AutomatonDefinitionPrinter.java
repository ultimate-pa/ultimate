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

import de.uni_freiburg.informatik.ultimate.automata.alternating.AlternatingAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.alternating.visualization.AlternatingAutomatonWriter;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.visualization.BaFormatWriter;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.visualization.GoalFormatWriter;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.visualization.HanoiFormatWriter;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.visualization.NwaWriterToString;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.visualization.NwaWriterToStringWithHash;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.visualization.NwaWriterUniqueId;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.visualization.NetWriterToString;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.visualization.NetWriterToStringWithUniqueNumber;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.visualization.NetWriterUniqueId;
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
	private PrintWriter mPrintWriter;
	private StringWriter mStringWriter;

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
	 * @param append
	 * 			  whether the automata should be added at the end of the file (true) or replace the content of the file (false)
	 */
	public AutomatonDefinitionPrinter(final AutomataLibraryServices services, final String automatonName,
			final String fileName, final Format format, final String message, final boolean append,
			final IAutomaton<?, ?>... automata) {
		this(services);
		final FileWriter fileWriter = getFileWriterWithOptionalAppend(fileName, format, append);
		if (fileWriter != null) {
			if (mLogger.isWarnEnabled()) {
				mLogger.warn("Dumping automata.");
			}
			mPrintWriter = new PrintWriter(fileWriter);
			printAutomataToFileWriter(automatonName, format, message, automata);
		}
	}

	public AutomatonDefinitionPrinter(final AutomataLibraryServices services, final String automatonName,
			final String fileName, final Format format, final String message, final IAutomaton<?, ?>... automata) {
		this(services, automatonName, fileName, format, message, false, automata);
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
	public AutomatonDefinitionPrinter(final AutomataLibraryServices services, final String automatonName,
			final Format format, final IAutomaton<?, ?> automaton) {
		this(services);
		mStringWriter = new StringWriter();
		mPrintWriter = new PrintWriter(mStringWriter);
		printAutomaton(automatonName, automaton, format);
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
	@SuppressWarnings({ "unused", "findbugs:UC_USELESS_VOID_METHOD" })
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

	/**
	 *  @param append
	 *
	 */
	private FileWriter getFileWriterWithOptionalAppend(final String fileName, final Format format, final boolean append) {
		final File testfile = new File(fileName + '.' + format.getFileEnding());
		try {
			return new FileWriter(testfile,append);
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
			final IAutomaton<?, ?>... automata) {
		switch (format) {
			case ATS:
			case ATS_NUMERATE:
			case ATS_QUOTED:
				mPrintWriter.println("// Testfile dumped by Ultimate at " + getDateTimeNice() + System.lineSeparator()
						+ "//" + System.lineSeparator() + "// " + message + System.lineSeparator());
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
		if (automaton instanceof INwaOutgoingLetterAndTransitionProvider) {
			printNestedWordAutomaton(name, (INwaOutgoingLetterAndTransitionProvider<LETTER, STATE>) automaton, format);
		} else if (automaton instanceof IPetriNet) {
			printPetriNet(name, (IPetriNet<LETTER, STATE>) automaton, format);
		} else if (automaton instanceof AlternatingAutomaton) {
			printAlternatingAutomaton(name, (AlternatingAutomaton<LETTER, STATE>) automaton, format);
		} else if (automaton instanceof TreeAutomatonBU<?, ?>) {
			printTreeAutomaton(name, (TreeAutomatonBU<?, STATE>) automaton, format);
		}
		mPrintWriter.close();
	}

	private void printTreeAutomaton(final String name, final TreeAutomatonBU<? extends IRankedLetter, STATE> automaton,
			final Format format) {
		switch (format) {
			case ATS:
				new TreeAutomatonWriter<>(mPrintWriter, name, automaton);
				break;
			case ATS_NUMERATE:
				new TreeAutomatonWriterUniqueId<>(mPrintWriter, name, automaton);
				break;
			case ATS_QUOTED:
			case BA:
			case GFF:
			case HOA:
			default:
				throw new AssertionError(UNSUPPORTED_LABELING);
		}
	}

	@SuppressWarnings("unused")
	private void printNestedWordAutomaton(final String name,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> automaton, final Format format)
			throws AssertionError {
		INestedWordAutomaton<LETTER, STATE> nwa;
		if (automaton instanceof INestedWordAutomaton) {
			nwa = (INestedWordAutomaton<LETTER, STATE>) automaton;
		} else {
			try {
				nwa = new NestedWordAutomatonReachableStates<>(mServices, automaton);
			} catch (final AutomataOperationCanceledException e) {
				throw new AssertionError("Timeout while preparing automaton for printing.");
			}
		}

		switch (format) {
		case ATS:
			new NwaWriterToString<>(mPrintWriter, name, nwa);
			break;
		case ATS_QUOTED:
			new NwaWriterToStringWithHash<>(mPrintWriter, name, nwa);
			break;
		case ATS_NUMERATE:
			new NwaWriterUniqueId<>(mPrintWriter, name, nwa);
			break;
		case BA:
			if (!NestedWordAutomataUtils.isFiniteAutomaton(nwa)) {
				throw new UnsupportedOperationException(
						format + " format does not support call transitions or return transitions");
			}
			new BaFormatWriter<>(mPrintWriter, nwa);
			break;
		case HOA:
			if (!NestedWordAutomataUtils.isFiniteAutomaton(nwa)) {
				throw new UnsupportedOperationException(
						format + " format does not support call transitions or return transitions");
			}
			new HanoiFormatWriter<>(mPrintWriter, nwa);
			break;
		case GFF:
			if (!NestedWordAutomataUtils.isFiniteAutomaton(nwa)) {
				throw new UnsupportedOperationException(
						format + " format does not support call transitions or return transitions");
			}
			new GoalFormatWriter<>(mPrintWriter, nwa);
			break;
		default:
			throw new AssertionError(UNSUPPORTED_LABELING);
		}
	}

	@SuppressWarnings("unused")
	private void printPetriNet(final String name, final IPetriNet<LETTER, STATE> net, final Format format)
			throws AssertionError {
		if (!(net instanceof BoundedPetriNet)) {
			final String msg = "Unknown Petri net type. Only supported type is " + BoundedPetriNet.class.getSimpleName();
			throw new IllegalArgumentException(msg);
		}

		final BoundedPetriNet<LETTER, STATE> castNet = (BoundedPetriNet<LETTER, STATE>) net;

		switch (format) {
			case ATS:
				new NetWriterToString<>(mPrintWriter, name, castNet);
				break;
			case ATS_QUOTED:
				new NetWriterToStringWithUniqueNumber<>(mPrintWriter, name, castNet);
				break;
			case ATS_NUMERATE:
				new NetWriterUniqueId<>(mPrintWriter, name, castNet);
				break;
			case BA:
			case GFF:
			case HOA:
			default:
				throw new AssertionError(UNSUPPORTED_LABELING);
		}
	}

	@SuppressWarnings("unused")
	private void printAlternatingAutomaton(final String name, final AlternatingAutomaton<LETTER, STATE> alternating,
			final Format format) {
		switch (format) {
			case ATS:
				new AlternatingAutomatonWriter<>(mPrintWriter, name, alternating);
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
}
