/*
 * Copyright (C) 2016 Jens Stimpfle <stimpflj@informatik.uni-freiburg.de>

 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it
 * and/or modify it under the terms of the GNU Lesser General Public License as
 * published by the Free Software Foundation, either version 3 of the License,
 * or (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be
 * useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU Lesser
 * General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see
 * <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7: If you modify the
 * ULTIMATE Automata Library, or any covered work, by linking or combining it
 * with Eclipse RCP (or a modified version of Eclipse RCP), containing parts
 * covered by the terms of the Eclipse Public License, the licensors of the
 * ULTIMATE Automata Library grant you additional permission to convey the
 * resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization.maxsat;

import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.Reader;
import java.io.StreamTokenizer;

/**
 * A few static parsing methods
 *
 * @author stimpflj
 *
 */
final class Scan {

	/**
	 * @param reader
	 *			  where to scan from
	 * @return parsed <code>NWA</code> or <code>null</code>
	 * @throws java.io.IOException
	 */
	static NWA scanNWA(Reader reader) throws IOException {
		int numStates;
		int numISyms;
		int numCSyms;
		int numRSyms;
		int numInitial;
		int numFinal;
		int numITrans;
		int numCTrans;
		int numRTrans;
		boolean[] isInitial;
		boolean[] isFinal;
		ITrans[] iTrans;
		CTrans[] cTrans;
		RTrans[] rTrans;

		final StreamTokenizer in = new StreamTokenizer(reader);
		in.eolIsSignificant(true);

		try {
			expectString(in, "numStates");
			numStates = parseInt(in);
			expectEOL(in);
			expectString(in, "numISyms");
			numISyms = parseInt(in);
			expectEOL(in);
			expectString(in, "numCSyms");
			numCSyms = parseInt(in);
			expectEOL(in);
			expectString(in, "numRSyms");
			numRSyms = parseInt(in);
			expectEOL(in);
			expectString(in, "numInitial");
			numInitial = parseInt(in);
			expectEOL(in);
			expectString(in, "numFinal");
			numFinal = parseInt(in);
			expectEOL(in);
			expectString(in, "numITrans");
			numITrans = parseInt(in);
			expectEOL(in);
			expectString(in, "numCTrans");
			numCTrans = parseInt(in);
			expectEOL(in);
			expectString(in, "numRTrans");
			numRTrans = parseInt(in);
			expectEOL(in);

			isInitial = new boolean[numStates];
			isFinal = new boolean[numStates];
			iTrans = new ITrans[numITrans];
			cTrans = new CTrans[numCTrans];
			rTrans = new RTrans[numRTrans];

			for (int i = 0; i < numInitial; i++) {
				expectString(in, "initial");
				final int x = parseInt(in, numStates);
				isInitial[x] = true;
				expectEOL(in);
			}

			for (int i = 0; i < numFinal; i++) {
				expectString(in, "final");
				final int x = parseInt(in, numStates);
				isFinal[x] = true;
				expectEOL(in);
			}

			for (int i = 0; i < numITrans; i++) {
				expectString(in, "iTrans");
				final int src = parseInt(in, numStates);
				final int sym = parseInt(in, numISyms);
				final int dst = parseInt(in, numStates);
				iTrans[i] = new ITrans(src, sym, dst);
				expectEOL(in);
			}

			for (int i = 0; i < numCTrans; i++) {
				expectString(in, "cTrans");
				final int src = parseInt(in, numStates);
				final int sym = parseInt(in, numCSyms);
				final int dst = parseInt(in, numStates);
				cTrans[i] = new CTrans(src, sym, dst);
				expectEOL(in);
			}

			for (int i = 0; i < numRTrans; i++) {
				expectString(in, "rTrans");
				final int src = parseInt(in, numStates);
				final int sym = parseInt(in, numRSyms);
				final int top = parseInt(in, numStates);
				final int dst = parseInt(in, numStates);
				rTrans[i] = new RTrans(src, sym, top, dst);
				expectEOL(in);
			}

			expectEOF(in);

		} catch (final ParseNWAException exc) {
			System.err.println(exc.problem);
			return null;
		}

		final NWA out = new NWA();
		out.numStates = numStates;
		out.numISyms = numISyms;
		out.numCSyms = numCSyms;
		out.numRSyms = numRSyms;
		out.isInitial = isInitial;
		out.isFinal = isFinal;
		out.iTrans = iTrans;
		out.cTrans = cTrans;
		out.rTrans = rTrans;

		if (!NWA.checkConsistency(out)) {
			System.err.println("ERROR: Parsed automaton is not consistent");
			return null;
		}

		return out;
	}

	/**
	 * Convenience method which calls <code>inputAsRelations(Reader)</code> with
	 * an <code>InputStreamReader</code> made from the <code>filepath</code>
	 * argument.
	 *
	 * @throws FileNotFoundException
	 */
	static NWA inputAsRelations(String filepath) throws FileNotFoundException, IOException {
		final InputStream inputStream = new FileInputStream(filepath);
		final Reader reader = new InputStreamReader(inputStream);
		return scanNWA(reader);
	}

	/* shitty helpers for inputAsRelations()
	 */

	@SuppressWarnings("serial")
	static final class ParseNWAException extends Exception {
		String problem;

		ParseNWAException(String problem) {
			this.problem = problem;
		}
	}

	private static void expectString(java.io.StreamTokenizer in, String x) throws java.io.IOException, ParseNWAException {
		in.nextToken();
		if (in.ttype != StreamTokenizer.TT_WORD ||!in.sval.equals(x)) {
			throw new ParseNWAException("expected " + x + ", but got " + in.sval);
		}
	}

	private static void expectEOL(java.io.StreamTokenizer in) throws java.io.IOException, ParseNWAException {
		in.nextToken();
		if (in.ttype != StreamTokenizer.TT_EOL) {
			throw new ParseNWAException("expected EOL");
		}
	}

	private static void expectEOF(java.io.StreamTokenizer in) throws java.io.IOException, ParseNWAException {
		in.nextToken();
		if (in.ttype != StreamTokenizer.TT_EOF) {
			throw new ParseNWAException("expected EOF");
		}
	}

	private static int parseInt(java.io.StreamTokenizer in) throws java.io.IOException, ParseNWAException {
		in.nextToken();
		if (in.ttype != StreamTokenizer.TT_NUMBER) {
			throw new ParseNWAException("expected number");
		}
		return (int) in.nval;
	}

	private static int parseInt(java.io.StreamTokenizer in, int max)throws java.io.IOException, ParseNWAException {
		in.nextToken();
		if (in.ttype != StreamTokenizer.TT_NUMBER) {
			throw new ParseNWAException("expected number");
		}
		final int n = (int) in.nval;
		if (n < 0 || n >= max) {
			throw new ParseNWAException(
					"expected number between 0 and " + Integer.toString(max)
					+ ", but got " + Integer.toString(n));
		}
		return n;
	}
}
