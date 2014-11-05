package de.uni_freiburg.informatik.ultimate.smtsolver.external;

import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import org.apache.log4j.Logger;

import java_cup.runtime.Symbol;
import de.uni_freiburg.informatik.ultimate.core.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.util.MonitoredProcess;
import de.uni_freiburg.informatik.ultimate.logic.Assignments;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * This class runs an external SMT solver. The main methods are
 * <code>input</code>, which gives an input to the SMT solver, and the
 * <code>parse...</code> methods, which parse the output from the SMT solver.
 * 
 * @author Oday Jubran
 */
class Executor {

	private MonitoredProcess mProcess;
	private Lexer mLexer;
	private BufferedWriter mWriter;
	private InputStream mStdErr;

	private final Script mScript;
	private final String mSolverCmd;
	private final Logger mLogger;
	private final IUltimateServiceProvider mServices;
	private final IToolchainStorage mStorage;

	Executor(String solverCommand, Script script, Logger logger, IUltimateServiceProvider services,
			IToolchainStorage storage) throws IOException {
		mServices = services;
		mStorage = storage;
		mSolverCmd = solverCommand;
		mScript = script;
		mLogger = logger;
		createProcess();
	}

	private void createProcess() throws IOException {
		// m_Logger = Logger.getRootLogger();
		mProcess = MonitoredProcess.exec(mSolverCmd, "(exit)", mServices, mStorage);

		if (mProcess == null) {
			String errorMsg = "Could not create process \"" + mSolverCmd + "\", terminating... ";
			mLogger.fatal(errorMsg);
			throw new IllegalStateException(errorMsg);
		}

		OutputStream stdin = mProcess.getOutputStream();
		InputStream stdout = mProcess.getInputStream();

		mStdErr = mProcess.getErrorStream();

		MySymbolFactory symfactory = new MySymbolFactory();
		mLexer = new Lexer(new InputStreamReader(stdout));
		mLexer.setSymbolFactory(symfactory);

		mWriter = new BufferedWriter(new OutputStreamWriter(stdin));

		input("(set-option :print-success true)");
		parseSuccess();
	}

	public void input(String in) {
		mLogger.debug(in + "\n");
		try {
			mWriter.write(in + "\n");
			mWriter.flush();
		} catch (IOException e) {
			throw new SMTLIBException("Connection to SMT solver broken", e);
		}
	}

	public void exit() {

		input("(exit)");
		parseSuccess();
		mProcess.forceShutdown();
		mProcess = null;

	}

	private List<Symbol> parseSexpr(Lexer lexer) throws IOException {
		ArrayList<Symbol> result = new ArrayList<Symbol>();
		int parenLevel = 0;
		do {
			Symbol sym = lexer.next_token();
			if (sym.sym == LexerSymbols.LPAR)
				parenLevel++;
			if (sym.sym == LexerSymbols.RPAR)
				parenLevel--;
			result.add(sym);
		} while (parenLevel > 0);
		return result;
	}

	private List<Symbol> readAnswer() {
		try {
			List<Symbol> result = parseSexpr(mLexer);
			for (Symbol s : result)
				mLogger.debug(s.toString() + "\n");
			return result;
		} catch (IOException e) {
			throw new SMTLIBException("Connection to SMT solver broken", e);
		}
	}

	public void reset() throws IOException {
		try {
			mWriter.write("(exit)\n");
			mWriter.flush();
		} catch (IOException e) {
			/* ignore */
		}
		mProcess.forceShutdown();
		createProcess();
	}

	public Symbol parse(int what) {
		List<Symbol> answer = readAnswer();

		// clear the std error buffer as it blocks when it runs full
		try {
			while (mStdErr.available() > 0) {
				mStdErr.read();
			}
		} catch (IOException e) {
			// we don't care what happens on stdErr
		}

		Parser m_Parser = new Parser();
		m_Parser.setScript(mScript);
		answer.add(0, new Symbol(what));
		m_Parser.setAnswer(answer);
		try {
			return m_Parser.parse();
		} catch (SMTLIBException ex) {
			throw ex;
		} catch (UnsupportedOperationException ex) {
			throw ex;
		} catch (Exception ex) {
			throw new SMTLIBException("Unexpected Exception while parsing", ex);
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

	public Object parseGetOptionResult() {
		return (Object) parse(LexerSymbols.GETOPTION).value;
	}
}