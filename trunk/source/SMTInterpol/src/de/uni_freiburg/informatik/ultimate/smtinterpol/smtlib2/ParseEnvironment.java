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

import de.uni_freiburg.informatik.ultimate.logic.IRAConstantFormatter;
import de.uni_freiburg.informatik.ultimate.logic.PrintTerm;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.Config;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.MySymbolFactory;

public class ParseEnvironment {
	final Script      mScript;
	private PrintWriter mOut = new PrintWriter(System.out);
	private boolean mPrintSuccess = true;
	private boolean mPrintTermCSE = true;
	private File mCwd = null;
	// What to do when script exits
	private ExitHook mExitHook;
	// Initialize this lazily.
	private Deque<Long> mTiming;
	private boolean mContinueOnError = !Config.COMPETITION;
	
	public ParseEnvironment(Script script) {
		this(script, null);
	}
	
	public ParseEnvironment(Script script, ExitHook exit) {
		mScript = script;
		mExitHook = exit;
	}
	
	public Script getScript() {
		return mScript;
	}

	static boolean convertSexp(StringBuilder sb, Object o, int level) {
        if (o instanceof Object[]) {
        	if (Config.RESULTS_ONE_PER_LINE && level > 0) {
        		sb.append(System.getProperty("line.separator"));
        		for (int i = 0; i < level; ++i)
        			sb.append(' ');
        	}
            sb.append('(');
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
            sb.append(')');
            return true;
        } else
            sb.append(o);
        return false;
	}
	
	public void parseScript(String filename) throws SMTLIBException {
		File oldcwd = mCwd;
		Reader reader = null;
		boolean closeReader = false;
		try {
			if (filename.equals("<stdin>")) {
				reader = new InputStreamReader(System.in);
			} else {
				File script = new File(filename);
				if (!script.isAbsolute())
					script = new File(mCwd, filename);
				mCwd = script.getParentFile();
				try {
					reader = new FileReader(script);
					closeReader = true;
				} catch (FileNotFoundException ex) {
					throw new SMTLIBException("File not found: " + filename);
				}
			}
			parseStream(reader, filename);
		} finally {
			mCwd = oldcwd;
			if (closeReader) {
				try {
					reader.close();
				} catch (IOException ex) {
					
				}
			}
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
		ExitHook oldexit = mExitHook;
		mExitHook = new ExitHook() {
			@Override
			public void exitHook() {
				/* ignore exit */
			}
		};
		File oldcwd = mCwd;
		parseScript(filename);
		mCwd = oldcwd;
		mExitHook = oldexit;
	}
	
	public void printSuccess() {
		if (mPrintSuccess) {
			mOut.println("success");
			mOut.flush();
		}
	}
	
	public void printError(String message) {
		mOut.print("(error \"");
		mOut.print(message);
		mOut.println("\")");
		mOut.flush();
		if (!mContinueOnError)
			System.exit(1);
	}
	
	public void printValues(Map<Term, Term> values) {
		PrintTerm pt = new PrintTerm();
		mOut.print('(');
		String sep = "";
		String itemSep = Config.RESULTS_ONE_PER_LINE 
				? System.getProperty("line.separator") + " " : " "; 
		for (Map.Entry<Term, Term> me : values.entrySet()) {
			mOut.print(sep);
			mOut.print('(');
			pt.append(mOut, me.getKey());
			mOut.print(' ');
			pt.append(mOut, me.getValue());
			mOut.print(')');
			sep = itemSep;
		}
		mOut.println(')');
		mOut.flush();
	}
	
	public void printResponse(Object response) {
		if (!mPrintTermCSE) {
			if (response instanceof Term) {
				new PrintTerm().append(mOut, (Term) response);
				mOut.println();
				mOut.flush();
				return;
			} else if (response instanceof Term[]) {
				printTermResponse((Term[])response);
				mOut.flush();
				return;
			}
		}
		if (response instanceof Object[]) {
			StringBuilder sb = new StringBuilder();
			convertSexp(sb, response, 0);
			mOut.println(sb.toString());
		} else if (response instanceof Iterable) {
			Iterable<?> it = (Iterable<?>) response;
			mOut.print("(");
			for (Object o : it)
				printResponse(o);
			mOut.println(")");
		} else
			mOut.println(response);
		mOut.flush();
	}
	
	public void printInfoResponse(String info, Object response) {
		StringBuilder sb = new StringBuilder();
		sb.append('(').append(info).append(' ');
		convertSexp(sb, response, 0);
		mOut.println(sb.append(')').toString());
		mOut.flush();
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
		sb.append('(');
        String sep = "";
        String itemSep = Config.RESULTS_ONE_PER_LINE 
        		? System.getProperty("line.separator") + " " : " ";
        for (Term t : response) {
            sb.append(sep);
            pt.append(sb, t);
            sep = itemSep;
        }
        sb.append(')');
		mOut.println(sb.toString());
		mOut.flush();
	}

	public void exit() {
		if (mExitHook == null) {
			mScript.exit();
			Runtime.getRuntime().exit(0);
		} else
			mExitHook.exitHook();
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
				mOut = new PrintWriter(createChannel((String) value));
			} catch (IOException ex) {
				throw new SMTLIBException(ex);
			}
		} else if (opt.equals(":print-success")) {
			if (value instanceof Boolean)
				mPrintSuccess = (Boolean) value;
			else if (value instanceof String)
				mPrintSuccess = Boolean.valueOf((String) value);
		} else if (opt.equals(":print-terms-cse")) {
			if (value instanceof Boolean)
				mPrintTermCSE = (Boolean) value;
			else if (value instanceof String)
				mPrintTermCSE = Boolean.valueOf((String) value);
		}
		mScript.setOption(opt, value);
	}
	
	public void setInfo(String info, Object value) {
		if (info.equals(":error-behavior")) {
			if ("immediate-exit".equals(value))
				mContinueOnError = false;
			else if ("continued-execution".equals(value))
				mContinueOnError = true;
		}
		mScript.setInfo(info, value);
	}
	
	public Object getInfo(String info) {
		if (info.equals(":error-behavior"))
			return mContinueOnError ? "continued-execution" : "immediate-exit";
		return mScript.getInfo(info);
	}

	public void setOutStream(PrintWriter stream) {
		mOut = stream;
	}
	
	public void startTiming() {
		if (mTiming == null)
			mTiming = new ArrayDeque<Long>();
		mOut.print('(');
		mTiming.push(System.nanoTime());
	}
	
	public void endTiming() {
		long old = mTiming.pop();
		long duration = System.nanoTime() - old;
		double secs = duration / 1000000000.0; // NOCHECKSTYLE
		mOut.printf((Locale) null, " :time %.3f)", secs);
		mOut.println();
		mOut.flush();
	}
	
	public boolean isContinueOnError() {
		return mContinueOnError;
	}
}
