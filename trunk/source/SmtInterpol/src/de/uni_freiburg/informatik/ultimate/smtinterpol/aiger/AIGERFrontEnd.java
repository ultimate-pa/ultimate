/*
 * Copyright (C) 2009-2012 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.aiger;

import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.math.BigInteger;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet.UnletType;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Model;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.smtinterpol.IParser;

public class AIGERFrontEnd implements IParser {
	
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

	private int m_Line;
	private int m_Col;
	private String m_Filename;
	private StringBuilder m_Buffer;
	private InputStream m_InputStream;
	private Script m_Solver;
	
	// The header data
	private BigInteger m_NumAnds;
	private String[] m_Inputs;
	
	// Parsing data
	private byte[] buffer = new byte[4096];
	private int bufpos = 0;
	private int bufsize = -1;
	
	public AIGERFrontEnd() {
		m_Line = 1;
		m_Col = 0;
		m_Buffer = new StringBuilder();
	}

	private void reportError(String msg) {
		System.err.print(m_Filename);
		System.err.print(':');
		System.err.print(m_Line);
		System.err.print(':');
		System.err.print(m_Col);
		System.err.print(':');
		System.err.println(msg);
		System.exit(2);
	}

	private final int nextChar() throws IOException {
		if (bufpos >= bufsize) {
			bufsize = m_InputStream.read(buffer);
			if (bufsize == -1)
				return -1; // EOF
			bufpos = 0;
		}
		return buffer[bufpos++] & 0xff;
	}
	
	private final void ungetLastChar() {
		assert(bufpos > 0);
		--bufpos;
	}

	private Object nextToken(int expected) {
		try {
			int ch = nextChar();
			String result;
			switch (expected) {
			case TT_MAGIC: // magic: only "aig" supported
				if (ch != 'a')
					return null;
				ch = nextChar();
				if (ch != 'i')
					return null;
				ch = nextChar();
				if (ch != 'g')
					return null;
				return "aig";
			case TT_SPACE:
				if (ch == ' ')
					return " ";
				else {
					ungetLastChar();
					return null;
				}
			case TT_NUMBER:
				while (ch != -1 && Character.isDigit((char) ch)) {
					m_Buffer.append((char) ch);
					ch = nextChar();
				}
				ungetLastChar();
				if (m_Buffer.length() == 0)
					return null;
				result = m_Buffer.toString();
				m_Buffer.setLength(0);
				return result;
			case TT_EOF:
				if (ch == -1)
					return ""; // Result has to be non-null but isn't interesting
				ungetLastChar();
				return null;
			case TT_NEWLINE:
				if (ch == '\n') {
					++m_Line;
					return "\n";
				}
				ungetLastChar();
				return null;
			case TT_STS:
				if (ch == 'i' || ch == 'l' || ch == 'o')
					return "" + (char) ch;
				ungetLastChar();
				return null;
			case TT_STRING:
				// Strings expand until the next newline
				// They may contain any ascii symbol
				while (ch != -1 && ch != '\n') {
					m_Buffer.append((char) ch);
					ch = nextChar();
				}
				ungetLastChar();
				result = m_Buffer.toString();
				m_Buffer.setLength(0);
				return result;
			case TT_COMMENT:
				if (ch == 'c')
					return "c";
				ungetLastChar();
				return null;
			case TT_BNUMBER: {
				BigInteger x = BigInteger.ZERO;
				int i = 0;
				while ((ch & 0x80) != 0) {
					BigInteger tmp = BigInteger.valueOf(ch & 0x7f);
					assert (7*i >= 0);
					tmp = tmp.shiftLeft(7 * i++);
					x = x.or(tmp);
					ch = nextChar();
					if (ch == -1) {
						System.err.println("File corrupted");
						System.exit(5);
					}
				}
				BigInteger tmp = BigInteger.valueOf(ch & 0x7f);
				assert (7*i >= 0);
				tmp = tmp.shiftLeft(7 * i);
				x = x.or(tmp);
				return x;
			}
				default:
					ungetLastChar();
					return null;
			}
		} catch (IOException ioe) {
			System.err.println(ioe.getMessage());
			System.exit(1);
			// Unreachable, but Java does not detect this...
			return null;
		}
	}
	
	private final void getOneSpace() {
		if (nextToken(TT_SPACE) == null)
			reportError("Expected one space");
	}
	
	private final void getNewline() {
		if (nextToken(TT_NEWLINE) == null)
			reportError("Expected newline");
	}
	
	private final String getNumber() {
		String res = (String) nextToken(TT_NUMBER);
		if (res == null)
			reportError("Expected a number");
		return res;
	}
	
	/**
	 * Parses the header of an AIGER file.  This file has to be in binary
	 * format.
	 */
	private void parseHeader() {
		if (nextToken(TT_MAGIC) == null)
			reportError("Expected magic (\"aig\")");
		getOneSpace();
		BigInteger maxVarNum = new BigInteger(getNumber());
		getOneSpace();
		m_Inputs = new String[Integer.parseInt(getNumber())];
		getOneSpace();
		if (!getNumber().equals("0")) {
			System.err.println("No latches allowed for SAT checking");
			System.exit(3);
		}
		getOneSpace();
		if (!getNumber().equals("1")) {
			System.err.println("Only one output allowed for SAT checking");
			System.exit(3);
		}
		getOneSpace();
		m_NumAnds = new BigInteger(getNumber());
		getNewline();
		// Do a consistency check...
		if (!maxVarNum.equals(
				m_NumAnds.add(BigInteger.valueOf(m_Inputs.length)))) {
			System.err.println("File header corrupted!");
			System.exit(5);
		}
	}
	
	private void parseSymbolTable() {
		String sts;
		while ((sts = (String) nextToken(TT_STS)) != null) {
			String num = getNumber();
			getOneSpace();
			String name = (String) nextToken(TT_STRING);
			if (name == null) {
				reportError("Expected a string");
				System.exit(2);
			}
			getNewline();
			if (sts.equals("i")) {
				int idx = Integer.parseInt(num);
				m_Inputs[idx] = name;
			}
			// I ignore a possible name for the output
		}
	}
	
	private void parseCommentSection() {
		if (nextToken(TT_COMMENT) != null) {
			while (true) {
				getNewline();
				if (nextToken(TT_STRING) == null)
					break; // Token is EOF;
			}
		}
	}
	
	private Term toTerm(BigInteger lit) {
		if (lit.equals(BigInteger.ZERO))
			return m_Solver.term("false");
		if (lit.equals(BigInteger.ONE))
			return m_Solver.term("true");
		Term res = m_Solver.term("" + lit.shiftRight(1));
		if (lit.testBit(0))
			res = m_Solver.term("not", res);
		return res;
	}
	
	private void parse() {
		parseHeader();
		Sort bool = m_Solver.sort("Bool");
		Sort[] empty = new Sort[0];
		for (int i = 0; i < m_Inputs.length; ++i)
			m_Solver.declareFun("" + (i + 1), empty, bool);
		// No latches...
		BigInteger output = new BigInteger(getNumber());
		getNewline();
		TermVariable[] emptyVars = new TermVariable[0];
		BigInteger start = BigInteger.valueOf(m_Inputs.length);
		BigInteger end = start.add(m_NumAnds);
		for (start = start.add(BigInteger.ONE); start.compareTo(end) <= 0;
				start = start.add(BigInteger.ONE)) {
			BigInteger delta0 = (BigInteger) nextToken(TT_BNUMBER);
			BigInteger delta1 = (BigInteger) nextToken(TT_BNUMBER);
			BigInteger rhs0 = start.shiftLeft(1).subtract(delta0);
			assert(start.shiftLeft(1).compareTo(rhs0) > 0);
			Term[] args = new Term[2];
			args[0] = toTerm(rhs0);
			BigInteger rhs1 = rhs0.subtract(delta1);
			assert (rhs0.compareTo(rhs1) >= 0);
			args[1] = toTerm(rhs1);
			if (USE_DEFINITIONS)
				m_Solver.defineFun(start.toString(), emptyVars, bool,
						m_Solver.term("and", args));
			else {
				String name = start.toString();
				m_Solver.declareFun(name, empty, bool);
				m_Solver.assertTerm(m_Solver.term("=",
						m_Solver.term(name),
						m_Solver.term("and", args)));
			}
		}
		parseSymbolTable();
		parseCommentSection();
		// Make some space for solving
		buffer = null;
		Logger.getRootLogger().info("Finished parsing");
		Term formula = toTerm(output);
		if (USE_DEFINITIONS) {
			FormulaUnLet unlet = new FormulaUnLet(UnletType.EXPAND_DEFINITIONS);
			m_Solver.assertTerm(unlet.unlet(formula));
		} else
			m_Solver.assertTerm(formula);
		Logger.getRootLogger().info("Asserted formula");
	}

	@Override
	public int run(Script solver, String filename) {
		m_Solver = solver;
		if (filename != null) {
			try {
				m_InputStream = new FileInputStream(filename);
			} catch (FileNotFoundException fnfe) {
				System.err.println(fnfe.getMessage());
				return 4;
			}
		} else {
			filename = "<stdin>";
			m_InputStream = System.in;
		}
		m_Filename = filename;
		m_Solver.setOption(":produce-models", Boolean.TRUE);
		m_Solver.setLogic(Logics.CORE);
		parse();
		LBool isSat = m_Solver.checkSat();
		System.out.println(isSat);
		if (isSat == LBool.SAT) {
			System.out.println("Stimuli:");
			Model m = m_Solver.getModel();
			Term trueTerm = m_Solver.term("true");
			for (int i = 0; i < m_Inputs.length; ++i) {
				Term var = m_Solver.term("" + i);
				if (m.evaluate(var) != trueTerm)
					System.out.print("not ");
				// Variable 0 is reserved for false...
				System.out.println(m_Inputs[i] == null ? (i + 1) : m_Inputs[i]);
			}
		}
		return 0;
	}
}
