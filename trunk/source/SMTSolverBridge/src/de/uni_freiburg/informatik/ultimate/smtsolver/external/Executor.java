/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Oday Jubran
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE SMTSolverBridge.
 *
 * The ULTIMATE SMTSolverBridge is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE SMTSolverBridge is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE SMTSolverBridge. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE SMTSolverBridge, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE SMTSolverBridge grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.smtsolver.external;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import org.apache.commons.io.output.TeeOutputStream;

import com.github.jhoenicke.javacup.runtime.SimpleSymbolFactory;
import com.github.jhoenicke.javacup.runtime.Symbol;

import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.lib.util.MonitoredProcess;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Assignments;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * This class runs an external SMT solver. The main methods are <code>input</code>, which gives an input to the SMT
 * solver, and the <code>parse...</code> methods, which parse the output from the SMT solver.
 *
 * @author Oday Jubran
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Matthias Heizmann
 */
public class Executor {

	private MonitoredProcess mProcess;
	private Lexer mLexer;

	private BufferedWriter mWriter;
	private InputStream mStdErr;

	private final Script mScript;
	private final Parser mParser;
	private final String mSolverCmd;
	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private final String mName;
	private final String mFullPathOfDumpedFile;
	private final String mSetupCommand;
	private final String mExitCommand;
	private final long mTimeout;

	private static final String EOF_ERROR_MSG = "Received EOF on stdin.";

	// Whether a check-sat is running. An interrupt is only sent then: a solver that waits for input may die of it.
	private final Object mQueryLock = new Object();
	private boolean mQueryRunning;
	private boolean mInterrupted;
	private boolean mKilled;
	// Counts the check-sats, so that an interrupt never outlives the query it was meant for.
	private long mQueryCount;

	/**
	 *
	 * @param solverCommand
	 *            The command to execute an external process with all parameters
	 * @param script
	 *            The {@link Script} that represents the API by which this executor is accessed
	 * @param logger
	 *            A logger
	 * @param services
	 *            The global services
	 * @param solverName
	 *            The internal name of the external process
	 * @param fullPathOfDumpedFile
	 *            Path to a file to which all solver output will be written or null to disable logging.
	 * @throws IOException
	 */
	Executor(final String solverCommand, final Script script, final ILogger logger,
			final IUltimateServiceProvider services, final String solverName, final String fullPathOfDumpedFile)
			throws IOException {
		this(solverCommand, script, logger, services, solverName, fullPathOfDumpedFile,
				"(set-option :print-success true)", "(exit)", -1L);
	}

	public Executor(final String solverCommand, final Script script, final ILogger logger,
			final IUltimateServiceProvider services, final String solverName, final String fullPathOfDumpedFile,
			final String setupCommand, final String exitCommand, final long timeout) throws IOException {
		mServices = services;
		mSolverCmd = solverCommand;
		mScript = script;
		mLogger = logger;
		mName = solverName;
		mFullPathOfDumpedFile = fullPathOfDumpedFile;
		mSetupCommand = setupCommand;
		mExitCommand = exitCommand;
		mTimeout = timeout;
		mParser = new Parser();
		mParser.setScript(mScript);
		createProcess();
	}

	private void createProcess() throws IOException {
		mProcess = MonitoredProcess.exec(mSolverCmd, mExitCommand, mServices);
		if (mProcess == null) {
			final String errorMsg = getLogStringPrefix() + " Could not create process, terminating... ";
			mLogger.fatal(errorMsg);
			throw new IllegalStateException(errorMsg);
		}

		final OutputStream stdin = mProcess.getOutputStream();
		final InputStream stdout = mProcess.getInputStream();

		if (mTimeout > 0) {
			mProcess.setCountdownToTermination(mTimeout);
		} else {
			mProcess.setTerminationAfterTimeout(1000);
		}

		mStdErr = mProcess.getErrorStream();

		final SimpleSymbolFactory symfactory = new SimpleSymbolFactory();
		mLexer = new Lexer(new InputStreamReader(stdout));
		mLexer.setSymbolFactory(symfactory);

		final OutputStream underlying;
		if (mFullPathOfDumpedFile != null) {
			final File logFile = new File(mFullPathOfDumpedFile);
			final FileOutputStream fos = new FileOutputStream(logFile);
			underlying = new TeeOutputStream(stdin, fos);
		} else {
			underlying = stdin;
		}

		mWriter = new BufferedWriter(new OutputStreamWriter(underlying));

		if (mSetupCommand != null) {
			input(mSetupCommand);
			parseSuccess();
		}
	}

	public void input(final String in) {
		if (mLogger.isDebugEnabled()) {
			mLogger.debug(getLogStringPrefix() + " " + in);
		}
		try {
			// FIXME 2019-04-27 Matthias: Workaround for CVC4.
			// It seems like CVC4 needs two line breaks after some set-info
			// commands
			mWriter.write(in + System.lineSeparator() + System.lineSeparator());
			mWriter.flush();
		} catch (final IOException e) {
			throw convertIOException(e);
		}
	}

	public void exit() {
		if (mProcess != null && mProcess.isRunning()) {
			input("(exit)");
			// 2015-11-12 Matthias: Do not parse "success" after exit.
			// Some solvers do return success (Barcelogic, CVC4, Z3) some solvers
			// don't do it (Princess, SMTInterpol).
			// parseSuccess();
			mProcess.forceShutdown();
		}
		mProcess = null;
	}

	public static List<Symbol> parseSexpr(final Lexer lexer) throws IOException {
		final ArrayList<Symbol> result = new ArrayList<>();
		int parenLevel = 0;
		do {
			final Symbol sym = lexer.next_token();
			if (sym.sym == LexerSymbols.LPAR) {
				parenLevel++;
			} else if (sym.sym == LexerSymbols.RPAR) {
				parenLevel--;
			} else if (sym.sym == LexerSymbols.EOF) {
				break;
			}
			result.add(sym);
		} while (parenLevel > 0);
		return result;
	}

	private List<Symbol> readAnswer() {
		try {
			final List<Symbol> result = parseSexpr(mLexer);
			if (mLogger.isDebugEnabled()) {
				for (final Symbol s : result) {
					mLogger.debug(s.toString());
				}
			}
			return result;
		} catch (final IOException e) {
			throw convertIOException(e);
		}
	}

	/**
	 * Marks the start of a check-sat, the only command {@link #interrupt()} may cancel.
	 */
	void beginQuery() {
		synchronized (mQueryLock) {
			mQueryRunning = true;
			mInterrupted = false;
			mKilled = false;
			mQueryCount++;
		}
	}

	/**
	 * Marks the end of a check-sat, however it ended.
	 */
	void endQuery() {
		synchronized (mQueryLock) {
			mQueryRunning = false;
			mQueryLock.notifyAll();
		}
	}

	/**
	 * Cancels the running check-sat by sending SIGINT to the solver, which then answers {@code unknown} and keeps its
	 * state; z3 does. Nothing is sent unless a check-sat is running. A solver that has answered just before the signal
	 * arrives may die of it, see {@link #isAlive()}.
	 * <p>
	 * A solver may take long to notice the signal, z3 did take minutes on nonlinear arithmetic. If the check-sat has not
	 * ended {@code graceMillis} after the signal, the solver is killed, and the check-sat fails; the caller has to be
	 * able to restart the solver.
	 *
	 * @param graceMillis
	 *            how long to wait for the check-sat to end before killing the solver, or negative to never kill it
	 * @return whether the signal was sent
	 */
	public boolean interrupt(final long graceMillis) {
		synchronized (mQueryLock) {
			if (!mQueryRunning || mProcess == null || !mProcess.isRunning()) {
				return false;
			}
			final long query = mQueryCount;
			if (System.getProperty("os.name").toLowerCase().startsWith("windows")) {
				throw new UnsupportedOperationException(
						getLogStringPrefix() + " cannot be interrupted: this needs SIGINT, which Windows does not have");
			}
			final int exitCode;
			try {
				exitCode = new ProcessBuilder("kill", "-INT", Long.toString(mProcess.pid())).redirectErrorStream(true)
						.start().waitFor();
			} catch (final IOException e) {
				throw new IllegalStateException(getLogStringPrefix() + " could not be interrupted", e);
			} catch (final InterruptedException e) {
				Thread.currentThread().interrupt();
				throw new IllegalStateException(getLogStringPrefix() + " was interrupted while interrupting", e);
			}
			if (exitCode != 0) {
				throw new IllegalStateException(
						getLogStringPrefix() + " could not be interrupted, kill -INT exited with " + exitCode);
			}
			mInterrupted = true;
			if (graceMillis < 0) {
				return true;
			}
			final long deadline = System.nanoTime() + graceMillis * 1_000_000;
			while (mQueryRunning && mQueryCount == query) {
				final long remainingMillis = (deadline - System.nanoTime()) / 1_000_000;
				if (remainingMillis <= 0) {
					break;
				}
				try {
					mQueryLock.wait(remainingMillis);
				} catch (final InterruptedException e) {
					Thread.currentThread().interrupt();
					break;
				}
			}
			if (mQueryRunning && mQueryCount == query) {
				mLogger.warn(getLogStringPrefix() + " did not answer within " + graceMillis
						+ " ms of the interrupt, killing it");
				mProcess.forceShutdown();
				mKilled = true;
			}
			return true;
		}
	}

	/**
	 * @return whether {@link #interrupt()} sent a signal during the last check-sat
	 */
	public boolean wasInterrupted() {
		synchronized (mQueryLock) {
			return mInterrupted;
		}
	}

	/**
	 * @return whether {@link #interrupt(long)} killed the solver during the last check-sat; it may still have answered
	 *         the interrupt before
	 */
	public boolean wasKilled() {
		synchronized (mQueryLock) {
			return mKilled;
		}
	}

	/**
	 * @return whether the solver process is still running
	 */
	public boolean isAlive() {
		return mProcess != null && mProcess.isRunning();
	}

	public void reset() throws IOException {
		try {
			mWriter.write("(exit)\n");
			mWriter.flush();
		} catch (final IOException e) {
			/* ignore */
		}
		mProcess.forceShutdown();
		createProcess();
	}

	public Symbol parse(final int what) {
		final List<Symbol> answer = readAnswer();
		String stderr = "";

		// clear the std error buffer as it blocks when it runs full
		try {
			if (mStdErr.available() > 0) {
				final StringBuilder sb = new StringBuilder();
				while (mStdErr.available() > 0) {
					final int i = mStdErr.read();
					final char c = (char) i;
					sb.append(c);
				}
				stderr = sb.toString();
				mLogger.warn(getLogStringPrefix() + " " + generateStderrMessage(stderr));
			}
		} catch (final IOException e) {
			// we don't care what happens on stdErr
		}

		answer.add(0, new Symbol(what));
		mParser.setAnswer(answer);
		try {
			return mParser.parse();
		} catch (final SMTLIBException ex) {
			if (mServices.getProgressMonitorService().continueProcessing()) {
				if (ex.getMessage().equals(Parser.s_EOF)) {
					throw new SMTLIBException(String.format("%s %s %s", getLogStringPrefix(), EOF_ERROR_MSG,
							generateStderrMessage(stderr)), ex);
				}
				throw ex;
			}
			throw new ToolchainCanceledException(getClass());
		} catch (final IOException e) {
			throw convertIOException(e);
		} catch (final Exception ex) {
			throw new SMTLIBException(String.format("%s %s %s", getLogStringPrefix(),
					"Unexpected Exception while parsing", generateStderrMessage(stderr)), ex);
		}
	}

	public void parseSuccess() {
		parse(LexerSymbols.SUCCESS);
	}

	public LBool parseCheckSatResult() {
		return (LBool) parse(LexerSymbols.CHECKSAT).value;
	}

	public Term[] parseGetAssertionsResult() {
		return (Term[]) parse(LexerSymbols.GETASSERTIONS).value;
	}

	public Term[] parseGetUnsatCoreResult() {
		return (Term[]) parse(LexerSymbols.GETUNSATCORE).value;
	}

	@SuppressWarnings("unchecked")
	public Map<Term, Term> parseGetValueResult() {
		return (Map<Term, Term>) parse(LexerSymbols.GETVALUE).value;
	}

	public Assignments parseGetAssignmentResult() {
		return (Assignments) parse(LexerSymbols.GETASSIGNMENT).value;
	}

	public Object[] parseGetInfoResult() {
		return (Object[]) parse(LexerSymbols.GETINFO).value;
	}

	public ModelDescription parseGetModelResult() {
		return (ModelDescription) parse(LexerSymbols.GETMODEL).value;
	}

	public Object parseGetOptionResult() {
		return parse(LexerSymbols.GETOPTION).value;
	}

	public Term[] parseInterpolants() {
		return (Term[]) parse(LexerSymbols.GETINTERPOLANTS).value;
	}

	public Term parseTerm() {
		return (Term) parse(LexerSymbols.GETTERM).value;
	}

	private String getLogStringPrefix() {
		if (mProcess != null) {
			return String.format("%s (%s)", mName, mProcess);
		}
		return String.format("%s (dormant, command %s)", mName, mSolverCmd);
	}

	private static String generateStderrMessage(final String stderr) {
		if (stderr.isEmpty()) {
			return "No stderr output.";
		}
		return "stderr output: " + stderr;
	}

	private RuntimeException convertIOException(final IOException ex) {
		if (mServices.getProgressMonitorService().continueProcessing()) {
			return new SMTLIBException(getLogStringPrefix() + " Connection to SMT solver broken", ex);
		}
		return new ToolchainCanceledException(getClass());
	}

}
