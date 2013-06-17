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

import de.uni_freiburg.informatik.ultimate.logic.Assignments;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * This class runs an external SMT solver.  The main methods are 
 * <code>input</code>, which gives an input to the SMT solver, and the 
 * <code>parse...</code> methods, which parse the output from the SMT solver.
 * 
 * @author Oday Jubran
 */
public class Executor {

	private String m_Solver;
	private Process m_Process;
	private Lexer m_Lexer;
	private BufferedWriter m_Writer;
	private Logger m_Logger;
	private Script m_Script;
	
	public Executor(String solverCommand, Script script, Logger logger)
	{
		m_Solver = solverCommand;
		m_Script = script;
		m_Logger = logger;
		createProcess();
	}
	
	public void createProcess()
	{
//		m_Logger = Logger.getRootLogger();
		try {
			m_Process = Runtime.getRuntime().exec(m_Solver);
		} catch (IOException e) {
			e.printStackTrace();
		}

		OutputStream stdin = m_Process.getOutputStream();
		InputStream stdout = m_Process.getInputStream();
		
		MySymbolFactory symfactory = new MySymbolFactory();
		m_Lexer = new Lexer(new InputStreamReader(stdout));
		m_Lexer.setSymbolFactory(symfactory);
		m_Writer = new BufferedWriter(new OutputStreamWriter(stdin));
		
		input("(set-option :print-success true)");
		parseSuccess();
	}

	public void input(String in)
	{
		m_Logger.debug(in + "\n");
		try {
			m_Writer.write(in + "\n");
			m_Writer.flush();
		} catch (IOException e) {
			throw new SMTLIBException("Connection to SMT solver broken", e);
		}
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

	private List<Symbol> readAnswer()
	{
		try {
			List<Symbol> result = parseSexpr(m_Lexer);
			for (Symbol s: result)
				m_Logger.debug(s.toString() + "\n");
			return result;
		} catch (IOException e) {
			throw new SMTLIBException("Connection to SMT solver broken", e);
		}
	}


	public void reset() {
		try {
			m_Writer.write("(exit)\n");
			m_Writer.flush();
		} catch (IOException e) {
			/* ignore */
		}
		m_Process.destroy();
		createProcess();	
	}
	
	public Symbol parse(int what) {
		List<Symbol> answer = readAnswer();
		Parser m_Parser = new Parser();
		m_Parser.setScript(m_Script);
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
	public Map<Term,Term> parseGetValueResult() {
		return (Map<Term,Term>) parse(LexerSymbols.GETVALUE).value;
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