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
package de.uni_freiburg.informatik.ultimate.smtinterpol.aiger;

import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet.UnletType;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Model;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.IParser;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.OptionMap;

public class AIGERFrontEnd implements IParser {
	
	private static final int BUFFER_SIZE = 4096;
	
	private final static boolean USE_DEFINITIONS = true;
	
	/**
	 * Token type "magic number".
	 */
	private static final int TT_MAGIC = 0;
	/**
	 * Token type "one space".
	 */
	private static final int TT_SPACE = 1;
	/**
	 * Token type "non-negative number".
	 */
	private static final int TT_NUMBER = 2;
	/**
	 * Token type "newline".
	 */
	private static final int TT_NEWLINE = 3;
	/**
	 * Token type "EOF".
	 */
	private static final int TT_EOF = 4;
	/**
	 * Token type "symbol type specifier".
	 */
	private static final int TT_STS = 5;
	/**
	 * Token type "string".
	 */
	private static final int TT_STRING = 6;
	/**
	 * Token type "comment start".
	 */
	private static final int TT_COMMENT = 7;
	/**
	 * Token type "binary number".
	 */
	private static final int TT_BNUMBER = 8;

	private int mLine;
	private int mCol;
	private String mFilename;
	private InputStream mInputStream;
	private Script mSolver;
	
	// The header data
	private BigInteger mNumAnds;
	private String[] mInputs;
	
	// Parsing data
	private byte[] mBuffer = new byte[BUFFER_SIZE];
	private int mBufpos = 0;
	private int mBufsize = -1;
	
	public AIGERFrontEnd() {
		mLine = 1;
		mCol = 0;
	}

	private void reportError(String msg) {
		System.err.print(mFilename);
		System.err.print(':');
		System.err.print(mLine);
		System.err.print(':');
		System.err.print(mCol);
		System.err.print(':');
		System.err.println(msg);
		System.exit(2);
	}

	private final int nextChar() throws IOException {
		if (mBufpos >= mBufsize) {
			mBufsize = mInputStream.read(mBuffer);
			if (mBufsize == -1)
			 {
				return -1; // EOF
			}
			mBufpos = 0;
		}
		++mCol;
		return mBuffer[mBufpos++] & 0xff;// NOCHECKSTYLE
	}
	
	private final void ungetLastChar() {
		assert(mBufpos > 0);
		--mCol;
		--mBufpos;
	}

	private Object nextToken(int expected) {
		try {
			int ch = nextChar();
			String result;
			switch (expected) {
			case TT_MAGIC: // magic: only "aig" supported
				if (ch != 'a') {
					return null;
				}
				ch = nextChar();
				if (ch != 'i') {
					return null;
				}
				ch = nextChar();
				if (ch != 'g') {
					return null;
				}
				return "aig";
			case TT_SPACE:
				if (ch == ' ') {
					return " ";
				} else {
					ungetLastChar();
					return null;
				}
			case TT_NUMBER:
			{
				final StringBuilder buffer = new StringBuilder();
				while (ch != -1 && Character.isDigit((char) ch)) {
					buffer.append((char) ch);
					ch = nextChar();
				}
				ungetLastChar();
				if (buffer.length() == 0) {
					return null;
				}
				result = buffer.toString();
				return result;
			}
			case TT_EOF:
				if (ch == -1)
				 {
					return "";// Result has to be non-null but isn't interesting
				}
				ungetLastChar();
				return null;
			case TT_NEWLINE:
				if (ch == '\n') {
					++mLine;
					mCol = 0;
					return "\n";
				}
				ungetLastChar();
				return null;
			case TT_STS:
				if (ch == 'i' || ch == 'l' || ch == 'o') {
					return Character.toString((char) ch);
				}
				ungetLastChar();
				return null;
			case TT_STRING:
			{
				final StringBuilder buffer = new StringBuilder();
				// Strings expand until the next newline
				// They may contain any ascii symbol
				while (ch != -1 && ch != '\n') {
					buffer.append((char) ch);
					ch = nextChar();
				}
				ungetLastChar();
				result = buffer.toString();
				return result;
			}
			case TT_COMMENT:
				if (ch == 'c') {
					return "c";
				}
				ungetLastChar();
				return null;
			case TT_BNUMBER: {
				BigInteger x = BigInteger.ZERO;
				int i = 0;
				while ((ch & 0x80) != 0) { // NOCHECKSTYLE
					BigInteger tmp = BigInteger.valueOf(ch & 0x7f);// NOCHECKSTYLE
					assert (7*i >= 0);// NOCHECKSTYLE
					tmp = tmp.shiftLeft(7 * i++);// NOCHECKSTYLE
					x = x.or(tmp);
					ch = nextChar();
					if (ch == -1) {
						System.err.println("File corrupted");
						System.exit(5);// NOCHECKSTYLE
					}
				}
				BigInteger tmp = BigInteger.valueOf(ch & 0x7f);// NOCHECKSTYLE
				assert (7*i >= 0);// NOCHECKSTYLE
				tmp = tmp.shiftLeft(7 * i);// NOCHECKSTYLE
				x = x.or(tmp);
				return x;
			}
			default:
				ungetLastChar();
				return null;
			}
		} catch (final IOException eioe) {
			System.err.println(eioe.getMessage());
			System.exit(1);
			// Unreachable, but Java does not detect this...
			return null;
		}
	}
	
	private final void getOneSpace() {
		if (nextToken(TT_SPACE) == null) {
			reportError("Expected one space");
		}
	}
	
	private final void getNewline() {
		if (nextToken(TT_NEWLINE) == null) {
			reportError("Expected newline");
		}
	}
	
	private final String getNumber() {
		final String res = (String) nextToken(TT_NUMBER);
		if (res == null) {
			reportError("Expected a number");
		}
		return res;
	}
	
	/**
	 * Parses the header of an AIGER file.  This file has to be in binary
	 * format.
	 */
	private void parseHeader() {
		if (nextToken(TT_MAGIC) == null) {
			reportError("Expected magic (\"aig\")");
		}
		getOneSpace();
		final BigInteger maxVarNum = new BigInteger(getNumber());
		getOneSpace();
		mInputs = new String[Integer.parseInt(getNumber())];
		getOneSpace();
		if (!getNumber().equals("0")) {
			System.err.println("No latches allowed for SAT checking");
			System.exit(3);// NOCHECKSTYLE
		}
		getOneSpace();
		if (!getNumber().equals("1")) {
			System.err.println("Only one output allowed for SAT checking");
			System.exit(3);// NOCHECKSTYLE
		}
		getOneSpace();
		mNumAnds = new BigInteger(getNumber());
		getNewline();
		// Do a consistency check...
		if (!maxVarNum.equals(
				mNumAnds.add(BigInteger.valueOf(mInputs.length)))) {
			System.err.println("File header corrupted!");
			System.exit(5);// NOCHECKSTYLE
		}
	}
	
	private void parseSymbolTable() {
		String sts;
		while ((sts = (String) nextToken(TT_STS)) != null) {
			final String num = getNumber();
			getOneSpace();
			final String name = (String) nextToken(TT_STRING);
			if (name == null) {
				reportError("Expected a string");
				System.exit(2);
			}
			getNewline();
			if (sts.equals("i")) {
				final int idx = Integer.parseInt(num);
				mInputs[idx] = name;
			}
			// I ignore a possible name for the output
		}
	}
	
	private void parseCommentSection() {
		if (nextToken(TT_COMMENT) != null) {
			while (true) {
				getNewline();
				if (nextToken(TT_STRING) == null)
				 {
					break; // Token is EOF;
				}
			}
		}
	}
	
	private Term toTerm(BigInteger lit) {
		if (lit.equals(BigInteger.ZERO)) {
			return mSolver.term("false");
		}
		if (lit.equals(BigInteger.ONE)) {
			return mSolver.term("true");
		}
		Term res = mSolver.term(lit.shiftRight(1).toString());
		if (lit.testBit(0)) {
			res = mSolver.term("not", res);
		}
		return res;
	}
	
	private void parse() {
		parseHeader();
		final Sort bool = mSolver.sort("Bool");
		final Sort[] empty = new Sort[0];
		for (int i = 0; i < mInputs.length; ++i) {
			mSolver.declareFun(Integer.toString(i + 1), empty, bool);
		}
		// No latches...
		final BigInteger output = new BigInteger(getNumber());
		getNewline();
		final TermVariable[] emptyVars = new TermVariable[0];
		BigInteger start = BigInteger.valueOf(mInputs.length);
		final BigInteger end = start.add(mNumAnds);
		for (start = start.add(BigInteger.ONE); start.compareTo(end) <= 0;
				start = start.add(BigInteger.ONE)) {
			final BigInteger delta0 = (BigInteger) nextToken(TT_BNUMBER);
			final BigInteger delta1 = (BigInteger) nextToken(TT_BNUMBER);
			final BigInteger rhs0 = start.shiftLeft(1).subtract(delta0);
			assert(start.shiftLeft(1).compareTo(rhs0) > 0);
			final Term[] args = new Term[2];
			args[0] = toTerm(rhs0);
			final BigInteger rhs1 = rhs0.subtract(delta1);
			assert (rhs0.compareTo(rhs1) >= 0);
			args[1] = toTerm(rhs1);
			if (USE_DEFINITIONS) {
				mSolver.defineFun(start.toString(), emptyVars, bool,
						mSolver.term("and", args));
			} else {
				final String name = start.toString();
				mSolver.declareFun(name, empty, bool);
				mSolver.assertTerm(mSolver.term("=",
						mSolver.term(name),
						mSolver.term("and", args)));
			}
		}
		parseSymbolTable();
		parseCommentSection();
		// Make some space for solving
		mBuffer = null;
		System.err.println("Finished parsing");
		final Term formula = toTerm(output);
		if (USE_DEFINITIONS) {
			final FormulaUnLet unlet = new FormulaUnLet(UnletType.EXPAND_DEFINITIONS);
			mSolver.assertTerm(unlet.unlet(formula));
		} else {
			mSolver.assertTerm(formula);
		}
		System.err.println("Asserted formula");
	}

	@Override
	public int run(Script solver, String filename, OptionMap options) {
		mSolver = solver;
		if (filename == null) {
			filename = "<stdin>";
			mInputStream = System.in;
		} else {
			try {
				mInputStream = new FileInputStream(filename);
			} catch (final FileNotFoundException efnfe) {
				System.err.println(efnfe.getMessage());
				return 4;// NOCHECKSTYLE
			}
		}
		mFilename = filename;
		mSolver.setOption(":produce-models", Boolean.TRUE);
		mSolver.setLogic(Logics.CORE);
		parse();
		final LBool isSat = mSolver.checkSat();
		System.out.println(isSat);
		if (isSat == LBool.SAT) {
			System.out.println("Stimuli:");
			final Model m = mSolver.getModel();
			final Term trueTerm = mSolver.term("true");
			for (int i = 0; i < mInputs.length; ++i) {
				final Term var = mSolver.term(Integer.toString(i));
				if (m.evaluate(var) != trueTerm) {
					System.out.print("not ");
				}
				// Variable 0 is reserved for false...
				System.out.println(mInputs[i] == null ? (i + 1) : mInputs[i]);
			}
		}
		return 0;
	}
}
