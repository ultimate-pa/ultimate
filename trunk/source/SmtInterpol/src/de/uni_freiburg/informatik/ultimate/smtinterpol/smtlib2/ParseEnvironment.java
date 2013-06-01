/*
 * Copyright (C) 2009-2012 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.io.Reader;
import java.util.ArrayDeque;
import java.util.Deque;
import java.util.Locale;
import java.util.Map;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.PrintTerm;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.Config;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.MySymbolFactory;

public class ParseEnvironment {
	Script      m_Script;
	private PrintWriter m_Out = new PrintWriter(System.out);
	private boolean m_PrintSuccess = true;
	private boolean m_PrintTermCSE = true;
	private File m_Cwd = null;
	// What to do when script exits
	private ExitHook m_ExitHook;
	// Initialize this lazily.
	private Deque<Long> m_Timing;// = new ArrayDeque<Long>();
	private boolean m_ContinueOnError = true;
	
	public ParseEnvironment(Script script) {
		this(script, null);
	}
	
	public ParseEnvironment(Script script, ExitHook exit) {
		m_Script = script;
		m_ExitHook = exit;
	}
	
	public Script getScript() {
		return m_Script;
	}

	static boolean convertSexp(StringBuilder sb, Object o, int level) {
        if (o instanceof Object[]) {
        	if (Config.RESULTS_ONE_PER_LINE && level > 0) {
        		sb.append(System.getProperty("line.separator"));
        		for (int i = 0; i < level; ++i)
        			sb.append(' ');
        	}
            sb.append("(");
            Object[] array = (Object[])o;
            boolean subarray = false;
            String sep = "";
            for (Object el : array) {
                    sb.append(sep);
                    subarray |= convertSexp(sb, el, level + Config.INDENTATION);
                    sep = " ";
            }
            if (subarray && Config.RESULTS_ONE_PER_LINE) {
        		sb.append(System.getProperty("line.separator"));
        		for (int i = 0; i < level; ++i)
        			sb.append(' ');
        	}
            sb.append(")");
            return true;
        } else
            sb.append(o);
        return false;
	}
	
	public void parseScript(String filename) throws SMTLIBException {
		File oldcwd = m_Cwd;
		Reader reader;
		try {
			if (filename.equals("<stdin>")) {
				reader = new InputStreamReader(System.in);
			} else {
				File script = new File(filename);
				if (!script.isAbsolute())
					script = new File(m_Cwd, filename);
				m_Cwd = script.getParentFile();
				try {
					reader = new FileReader(script);
				} catch (FileNotFoundException ex) {
					throw new SMTLIBException("File not found: "+script);
				}
			}
			parseStream(reader, filename);
		} finally {
			m_Cwd = oldcwd;
		}
	}
	
	public void parseStream(Reader reader, String streamname)
	throws SMTLIBException {
		MySymbolFactory symfactory = new MySymbolFactory();
		Lexer lexer = new Lexer(reader);
		lexer.setSymbolFactory(symfactory);
		Parser parser = new Parser(lexer, symfactory);
		parser.setFileName(streamname);
		parser.setParseEnvironment(this);
		try {
			parser.parse();
		} catch (Exception ex) {
			Logger.getRootLogger().error("Unexpected Exception", ex);
			throw new SMTLIBException(ex);
		}
	}
	
	public void include(String filename) throws SMTLIBException {
		ExitHook oldexit = m_ExitHook;
		m_ExitHook = new ExitHook() {
			@Override
			public void exitHook() {
				/* ignore exit */
			}
		};
		File oldcwd = m_Cwd;
		parseScript(filename);
		m_Cwd = oldcwd;
		m_ExitHook = oldexit;
	}
	
	public void printSuccess() {
		if (m_PrintSuccess) {
			m_Out.println("success");
			m_Out.flush();
		}
	}
	
	public void printError(String message) {
		m_Out.print("(error \"");
		m_Out.print(message);
		m_Out.println("\")");
		m_Out.flush();
		if (!m_ContinueOnError)
			System.exit(1);
	}
	
	public void printValues(Map<Term, Term> values) {
		PrintTerm pt = new PrintTerm();
		m_Out.print('(');
		String sep = "";
		String itemSep = Config.RESULTS_ONE_PER_LINE ? 
				System.getProperty("line.separator") + " " : " "; 
		for (Map.Entry<Term, Term> me : values.entrySet()) {
			m_Out.print(sep);
			m_Out.print('(');
			pt.append(m_Out, me.getKey());
			m_Out.print(' ');
			pt.append(m_Out, me.getValue());
			m_Out.print(')');
			sep = itemSep;
		}
		m_Out.println(')');
		m_Out.flush();
	}
	
	public void printResponse(Object response) {
		if (!m_PrintTermCSE) {
			if (response instanceof Term) {
				new PrintTerm().append(m_Out, (Term) response);
				m_Out.println();
				m_Out.flush();
				return;
			} else if (response instanceof Term[]) {
				printTermResponse((Term[])response);
				m_Out.flush();
				return;
			}
		}
		if (response instanceof Object[]) {
			StringBuilder sb = new StringBuilder();
			convertSexp(sb, response, 0);
			m_Out.println(sb.toString());
		} else if (response instanceof Iterable) {
			Iterable<?> it = (Iterable<?>) response;
			m_Out.print("(");
			for (Object o : it)
				printResponse(o);
			m_Out.println(")");
		} else
			m_Out.println(response.toString());
		m_Out.flush();
	}
	
	public void printInfoResponse(String info, Object response) {
		StringBuilder sb = new StringBuilder();
		sb.append('(').append(info).append(' ');
		convertSexp(sb, response, 0);
		m_Out.println(sb.append(')').toString());
		m_Out.flush();
	}
	
	/**
	 * Direct printing of a term array response.  This function is introduced to
	 * satisfy the requirement of the SMTLIB standard for the get-assertions
	 * command.  We have to print the terms "as they are asserted", i.e.,
	 * without introducing let terms via cse.
	 * @param response The response to print.
	 */
	public void printTermResponse(Term[] response) {
		StringBuilder sb = new StringBuilder();
		PrintTerm pt = new PrintTerm();
		sb.append("(");
        String sep = "";
        String itemSep = Config.RESULTS_ONE_PER_LINE ? 
        		System.getProperty("line.separator") + " " : " ";
        for (Term t : response) {
                sb.append(sep);
                pt.append(sb, t);
                sep = itemSep;
        }
        sb.append(")");
		m_Out.println(sb.toString());
		m_Out.flush();
	}

	public void exit() {
		if (m_ExitHook != null)
			m_ExitHook.exitHook();
		else {
			m_Script.exit();
			Runtime.getRuntime().exit(0);
		}
	}
	
	public PrintWriter createChannel(String file) throws IOException {
		if (file.equals("stdout"))
			return new PrintWriter(System.out);
		else if (file.equals("stderr"))
			return new PrintWriter(System.err);
		else
			return new PrintWriter(new FileWriter(file));
	}
	
	public void setOption(String opt, Object value) throws SMTLIBException {
		if (opt.equals(":regular-output-channel")) {
			try {
				m_Out = new PrintWriter(createChannel((String) value));
			} catch (IOException ex) {
				throw new SMTLIBException(ex);
			}
		} else if (opt.equals(":print-success")) {
			if (value instanceof Boolean)
				m_PrintSuccess = (Boolean) value;
			else if (value instanceof String)
				m_PrintSuccess = Boolean.valueOf((String) value);
		} else if (opt.equals(":print-terms-cse")) {
			if (value instanceof Boolean)
				m_PrintTermCSE = (Boolean) value;
			else if (value instanceof String)
				m_PrintTermCSE = Boolean.valueOf((String) value);
		}
		m_Script.setOption(opt, value);
	}
	
	public void setInfo(String info, Object value) {
		if (info.equals(":error-behavior")) {
			if ("immediate-exit".equals(value))
				m_ContinueOnError = false;
			else if ("continued-execution".equals(value))
				m_ContinueOnError = true;
		}
		m_Script.setInfo(info, value);
	}
	
	public Object getInfo(String info) {
		if (info.equals(":error-behavior"))
			return m_ContinueOnError ? "continued-execution" : "immediate-exit";
		return m_Script.getInfo(info);
	}

	public void setOutStream(PrintWriter stream) {
		m_Out = stream;
	}
	
	public void startTiming() {
		if (m_Timing == null)
			m_Timing = new ArrayDeque<Long>();
		m_Out.print('(');
		m_Timing.push(System.nanoTime());
	}
	
	public void endTiming() {
		long old = m_Timing.pop();
		long duration = System.nanoTime() - old;
		double secs = duration / 1000000000.0;
		m_Out.printf((Locale) null, " :time %.3f)", secs);
		m_Out.println();
		m_Out.flush();
	}
	
	public boolean isContinueOnError() {
		return m_ContinueOnError;
	}
}
