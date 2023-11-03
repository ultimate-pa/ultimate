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
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.io.Reader;
import java.util.ArrayDeque;
import java.util.Deque;
import java.util.zip.GZIPInputStream;

import com.github.jhoenicke.javacup.runtime.SimpleSymbolFactory;

import de.uni_freiburg.informatik.ultimate.logic.FormulaLet;
import de.uni_freiburg.informatik.ultimate.logic.PrintTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.FrontEndOptions;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.OptionMap;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofRules;

public class ParseEnvironment {
	final Script mScript;
	private File mCwd = null;
	// Initialize this lazily.
	private Deque<Long> mTiming;

	private final FrontEndOptions mOptions;

	private Lexer mLexer = null;
	private boolean mVersion25 = true;

	public ParseEnvironment(final Script script, final OptionMap options) {
		mScript = script;
		mOptions = options.getFrontEndOptions();
		if (!mOptions.isFrontEndActive()) {
			throw new IllegalArgumentException("Front End not active!");
		}
	}

	public boolean isSMTLIB25() {
		return mVersion25;
	}

	public Script getScript() {
		return mScript;
	}

	public void parseScript(final String filename) throws SMTLIBException {
		final File oldcwd = mCwd;
		Reader reader = null;
		boolean closeReader = false;
		try {
			if (filename.equals("<stdin>")) {
				reader = new InputStreamReader(System.in);
			} else {
				File script = new File(filename);
				if (!script.isAbsolute()) {
					script = new File(mCwd, filename);
				}
				mCwd = script.getParentFile();
				try {
					if (filename.endsWith(".gz")) {
						reader = new InputStreamReader(new GZIPInputStream(new FileInputStream(script)));
					} else {
						reader = new FileReader(script);
					}
					closeReader = true;
				} catch (final FileNotFoundException ex) {
					throw new SMTLIBException("File not found: " + filename, ex);
				} catch (final IOException ex) {
					throw new SMTLIBException("Cannot read file: " + filename, ex);
				}
			}
			parseStream(reader, filename);
		} finally {
			mCwd = oldcwd;
			if (closeReader) {
				try {
					reader.close();
				} catch (final IOException ex) {
				}
			}
		}
	}

	public void parseStream(final Reader reader, final String streamname) throws SMTLIBException {
		final SimpleSymbolFactory symfactory = new SimpleSymbolFactory();
		final Lexer last = mLexer;
		mLexer = new Lexer(reader);
		mLexer.setSymbolFactory(symfactory);
		final Parser parser = new Parser(mLexer, symfactory);
		parser.setFileName(streamname);
		parser.setParseEnvironment(this);
		try {
			parser.parse();
		} catch (final Exception ex) {
			System.err.println("Unexpected Exception: " + ex);
			throw new SMTLIBException(ex);
		} finally {
			mLexer = last;
		}
	}

	public void include(final String filename) throws SMTLIBException {
		parseScript(filename);
	}

	public void printSuccess() {
		if (mOptions.isPrintSuccess()) {
			printResponse("success");
		}
	}

	public void printError(final String message) {
		printResponse(new SExpression(new Object[] { "error", new QuotedObject(message, mVersion25) }));
		if (!mOptions.continueOnError()) {
			exitWithStatus(1);
		}
	}

	public void printUnsupported() {
		printResponse("unsupported");
		if (!mOptions.continueOnError()) {
			exitWithStatus(1);
		}
	}

	public void printResponse(final Object response) {
		final PrintWriter out = mOptions.getOutChannel();
		if (response instanceof Term && ProofRules.isProof((Term) response)) {
			Term proof = (Term) response;
			if (mOptions.isPrintTermsCSE()) {
				proof = new FormulaLet().let(proof);
			}
			ProofRules.printProof(out, proof);
			out.println();
			out.flush();
			return;
		}
		if (!mOptions.isPrintTermsCSE()) {
			if (response instanceof Term) {
				new PrintTerm().append(out, (Term) response);
				out.println();
				out.flush();
				return;
			} else if (response instanceof SExpression
					   && ((SExpression) response).getData() instanceof Term[]) {
				new PrintTerm().append(out, (Term[]) ((SExpression) response).getData());
				out.println();
				out.flush();
				return;
			}
		}
		out.println(response);
		out.flush();
	}

	public void exitWithStatus(final int statusCode) {
		System.exit(statusCode);
	}

	public void exit() {
		mScript.exit();
		exitWithStatus(0);
	}

	public void setInfo(final String info, final Object value) {
		if (info.equals(SMTLIBConstants.SMT_LIB_VERSION)) {
			final String svalue = String.valueOf(value);
			if ("2.5".equals(svalue) || "2.6".equals(svalue)) {
				mVersion25 = true;
				mLexer.setVersion25(true);
			} else if ("2.0".equals(svalue)) {
				mVersion25 = false;
				mLexer.setVersion25(false);
			} else {
				throw new SMTLIBException("Unknown SMT-LIB version");
			}
		} else if (info.equals(SMTLIBConstants.ERROR_BEHAVIOR)) {
			switch ((String) value) {
			case SMTLIBConstants.IMMEDIATE_EXIT:
				mScript.setOption(":continue-on-error", false);
				break;
			case SMTLIBConstants.CONTINUED_EXECUTION:
				mScript.setOption(":continue-on-error", true);
				break;
			default:
				throw new SMTLIBException("Value should be " + SMTLIBConstants.CONTINUED_EXECUTION
						+ " or " + SMTLIBConstants.IMMEDIATE_EXIT);
			}
		}
		mScript.setInfo(info, value);
	}

	public Object getInfo(final String info) {
		if (info.equals(SMTLIBConstants.ERROR_BEHAVIOR)) {
			return mOptions.continueOnError() ? SMTLIBConstants.CONTINUED_EXECUTION : SMTLIBConstants.IMMEDIATE_EXIT;
		}
		return mScript.getInfo(info);
	}

	public void startTiming() {
		if (mTiming == null) {
			mTiming = new ArrayDeque<>();
		}
		printResponse("(");
		mTiming.push(System.nanoTime());
	}

	public void endTiming() {
		final long old = mTiming.pop();
		final long duration = System.nanoTime() - old;
		final long msecs = duration / 1000000; // NOCHECKSTYLE
		printResponse(String.format(" :time %d.%03d)", msecs/1000, msecs % 1000));
	}

	public boolean isContinueOnError() {
		return mOptions.continueOnError();
	}
}
