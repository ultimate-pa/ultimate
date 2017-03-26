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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.arrays;

import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.Reader;
import java.io.StreamTokenizer;

/**
 * A few static parsing methods
 *
 * @author stimpflj
 */
final class Scan {
	private Scan() {
		// no public constructor
	}

	/**
	 * @param reader
	 *            where to scan from
	 * @return parsed <code>NWA</code> or <code>null</code>
	 */
	static NwaWithArrays scanNwa(final Reader reader) throws IOException {
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
		ITrans[] inTrans;
		CTrans[] caTrans;
		RTrans[] reTrans;

		final StreamTokenizer in = new StreamTokenizer(reader);
		in.eolIsSignificant(true);

		try {
			expectString(in, "numStates");
			numStates = parseInt(in);
			expectEol(in);
			expectString(in, "numISyms");
			numISyms = parseInt(in);
			expectEol(in);
			expectString(in, "numCSyms");
			numCSyms = parseInt(in);
			expectEol(in);
			expectString(in, "numRSyms");
			numRSyms = parseInt(in);
			expectEol(in);
			expectString(in, "numInitial");
			numInitial = parseInt(in);
			expectEol(in);
			expectString(in, "numFinal");
			numFinal = parseInt(in);
			expectEol(in);
			expectString(in, "numITrans");
			numITrans = parseInt(in);
			expectEol(in);
			expectString(in, "numCTrans");
			numCTrans = parseInt(in);
			expectEol(in);
			expectString(in, "numRTrans");
			numRTrans = parseInt(in);
			expectEol(in);

			isInitial = new boolean[numStates];
			isFinal = new boolean[numStates];
			inTrans = new ITrans[numITrans];
			caTrans = new CTrans[numCTrans];
			reTrans = new RTrans[numRTrans];

			for (int i = 0; i < numInitial; i++) {
				expectString(in, "initial");
				final int x = parseInt(in, numStates);
				isInitial[x] = true;
				expectEol(in);
			}

			for (int i = 0; i < numFinal; i++) {
				expectString(in, "final");
				final int x = parseInt(in, numStates);
				isFinal[x] = true;
				expectEol(in);
			}

			for (int i = 0; i < numITrans; i++) {
				expectString(in, "iTrans");
				final int src = parseInt(in, numStates);
				final int sym = parseInt(in, numISyms);
				final int dst = parseInt(in, numStates);
				inTrans[i] = new ITrans(src, sym, dst);
				expectEol(in);
			}

			for (int i = 0; i < numCTrans; i++) {
				expectString(in, "cTrans");
				final int src = parseInt(in, numStates);
				final int sym = parseInt(in, numCSyms);
				final int dst = parseInt(in, numStates);
				caTrans[i] = new CTrans(src, sym, dst);
				expectEol(in);
			}

			for (int i = 0; i < numRTrans; i++) {
				expectString(in, "rTrans");
				final int src = parseInt(in, numStates);
				final int sym = parseInt(in, numRSyms);
				final int top = parseInt(in, numStates);
				final int dst = parseInt(in, numStates);
				reTrans[i] = new RTrans(src, sym, top, dst);
				expectEol(in);
			}

			expectEof(in);

		} catch (final ParseNwaException exc) {
			System.err.println(exc.mProblem);
			return null;
		}

		final NwaWithArrays out = new NwaWithArrays();
		out.mNumStates = numStates;
		out.mNumISyms = numISyms;
		out.mNumCSyms = numCSyms;
		out.mNumRSyms = numRSyms;
		out.mIsInitial = isInitial;
		out.mIsFinal = isFinal;
		out.mITrans = inTrans;
		out.mCTrans = caTrans;
		out.mRTrans = reTrans;

		if (!NwaWithArrays.checkConsistency(out)) {
			System.err.println("ERROR: Parsed automaton is not consistent");
			return null;
		}

		return out;
	}

	/**
	 * Convenience method which calls <code>inputAsRelations(Reader)</code> with an <code>InputStreamReader</code> made
	 * from the <code>filepath</code> argument.
	 */
	static NwaWithArrays inputAsRelations(final String filepath) throws IOException {
		final InputStream inputStream = new FileInputStream(filepath);
		final Reader reader = new InputStreamReader(inputStream);
		return scanNwa(reader);
	}

	/* shitty helpers for inputAsRelations()
	 */

	@SuppressWarnings("serial")
	static final class ParseNwaException extends Exception {
		public final String mProblem;

		ParseNwaException(final String problem) {
			mProblem = problem;
		}
	}

	private static void expectString(final StreamTokenizer in, final String x) throws IOException, ParseNwaException {
		in.nextToken();
		if (in.ttype != StreamTokenizer.TT_WORD || !in.sval.equals(x)) {
			throw new ParseNwaException("expected " + x + ", but got " + in.sval);
		}
	}

	private static void expectEol(final StreamTokenizer in) throws IOException, ParseNwaException {
		in.nextToken();
		if (in.ttype != StreamTokenizer.TT_EOL) {
			throw new ParseNwaException("expected EOL");
		}
	}

	private static void expectEof(final StreamTokenizer in) throws IOException, ParseNwaException {
		in.nextToken();
		if (in.ttype != StreamTokenizer.TT_EOF) {
			throw new ParseNwaException("expected EOF");
		}
	}

	private static int parseInt(final StreamTokenizer in) throws IOException, ParseNwaException {
		in.nextToken();
		if (in.ttype != StreamTokenizer.TT_NUMBER) {
			throw new ParseNwaException("expected number");
		}
		return (int) in.nval;
	}

	private static int parseInt(final StreamTokenizer in, final int max) throws IOException, ParseNwaException {
		in.nextToken();
		if (in.ttype != StreamTokenizer.TT_NUMBER) {
			throw new ParseNwaException("expected number");
		}
		final int n = (int) in.nval;
		if (n < 0 || n >= max) {
			throw new ParseNwaException(
					"expected number between 0 and " + Integer.toString(max) + ", but got " + Integer.toString(n));
		}
		return n;
	}
}
