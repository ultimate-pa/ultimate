/*
 * Copyright (C) 2022 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.proof.checker;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.Reader;
import java.util.zip.GZIPInputStream;

import com.github.jhoenicke.javacup.runtime.Scanner;
import com.github.jhoenicke.javacup.runtime.SimpleSymbolFactory;
import com.github.jhoenicke.javacup.runtime.Symbol;

import de.uni_freiburg.informatik.ultimate.logic.NoopScript;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.MinimalProofChecker;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.ScopedArrayList;

public class CheckingScript extends NoopScript {
	private final String mProofFile;
	private final LogProxy mLogger;
	private final ScopedArrayList<Term> mAssertions = new ScopedArrayList<>();
	final SimpleSymbolFactory mSymfactory = new SimpleSymbolFactory();

	private LBool mLastCheckSat;
	private SExprLexer mLexer;

	public class SExprLexer implements Scanner {
		private final Scanner mLexer;
		private Symbol mEOFSymbol;
		private int mParenLevel;

		public SExprLexer(final Scanner wrappedLexer) {
			mLexer = wrappedLexer;
			mEOFSymbol = null;
		}

		@Override
		public Symbol next_token() throws Exception {
			if (mEOFSymbol != null) {
				return mEOFSymbol;
			}
			final Symbol nextSymbol = mLexer.next_token();
			if (nextSymbol.sym == ProofSymbols.LPAR) {
				mParenLevel++;
			}
			if (nextSymbol.sym == ProofSymbols.RPAR) {
				mParenLevel--;
			}
			if (mParenLevel == 0) {
				// s-expression ends here
				mEOFSymbol = mSymfactory.newSymbol("", ProofSymbols.EOF, nextSymbol, nextSymbol);
			}
			return nextSymbol;
		}

		public void clearEOF() {
			mEOFSymbol = null;
		}
	}

	public CheckingScript(final LogProxy logger, final String proofFile) {
		mLogger = logger;
		mProofFile = proofFile;
		setProofReader(openProofReader(proofFile));
	}

	public CheckingScript(final LogProxy logger, final String proofFile, final Reader proofReader) {
		mLogger = logger;
		mProofFile = proofFile;
		setProofReader(proofReader);
	}

	public void setProofReader(final Reader proofReader) {
		final ProofLexer wrappedLexer = new ProofLexer(proofReader);
		wrappedLexer.setSymbolFactory(mSymfactory);
		mLexer = new SExprLexer(wrappedLexer);
	}

	@Override
	public LBool assertTerm(final Term assertion) {
		mAssertions.add(assertion);
		return LBool.UNKNOWN;
	}

	@Override
	public Term[] getAssertions() {
		return mAssertions.toArray(new Term[mAssertions.size()]);
	}

	@Override
	public void push(int n) throws SMTLIBException {
		super.push(n);
		while (n-- > 0) {
			mAssertions.beginScope();
		}
	}

	@Override
	public void pop(final int n) throws SMTLIBException {
		super.pop(n);
		int i = n;
		while (i-- > 0) {
			mAssertions.endScope();
		}
	}

	private Reader openProofReader(final String filename) {
		if (filename.equals("<stdin>")) {
			return new InputStreamReader(System.in);
		} else {
			final File proofFile = new File(filename);
			try {
				if (filename.endsWith(".gz")) {
					return new InputStreamReader(new GZIPInputStream(new FileInputStream(proofFile)));
				} else {
					return new FileReader(proofFile);
				}
			} catch (final FileNotFoundException ex) {
				throw new SMTLIBException("File not found: " + filename, ex);
			} catch (final IOException ex) {
				throw new SMTLIBException("Cannot read file: " + filename, ex);
			}
		}
	}

	public void printError(final String result) {
		mLogger.error(result);
	}

	public void printResult(final Object result) {
		System.out.println(result.toString());
	}

	@Override
	public LBool checkSat() {
		mLexer.clearEOF();
		final Symbol result, eof;
		try {
			result = mLexer.next_token();
			eof = mLexer.next_token();
		} catch (final Exception ex) {
			throw new RuntimeException("Unexpected exception", ex);
		}
		if (result.sym != ProofSymbols.SYMBOL) {
			mLastCheckSat = LBool.UNKNOWN;
		} else {
			assert result.sym == ProofSymbols.SYMBOL;
			assert eof.sym == ProofSymbols.EOF;
			try {
				mLastCheckSat = LBool.valueOf(((String) result.value).toUpperCase());
			} catch (final IllegalArgumentException ex) {
				mLastCheckSat = LBool.UNKNOWN;
			}
		}
		return mLastCheckSat;
	}

	@Override
	public Term getProof() {
		mLexer.clearEOF();
		if (mLastCheckSat == LBool.UNSAT) {
			final ProofParser proofParser = new ProofParser(mLexer, mSymfactory);
			proofParser.setFileName(mProofFile);
			proofParser.setScript(this);
			final Term proof;
			try {
				proof = (Term) proofParser.parse().value;
			} catch (final Exception ex) {
				throw new RuntimeException("Unexpected exception", ex);
			}
			final MinimalProofChecker checker = new MinimalProofChecker(this, mLogger);
			if (checker.check(proof)) {
				final int numberOfHoles = checker.getNumberOfHoles();
				printResult(numberOfHoles > 0 ? "holey" : "valid");
				printResult("holes=" + numberOfHoles);
				printResult("assertions=" + checker.getNumberOfAssertions());
				printResult("definefuns=" + checker.getNumberOfDefineFun());
				printResult("axioms=" + checker.getNumberOfAxioms());
				printResult("resolutions=" + checker.getNumberOfResolutions());
			} else {
				printResult("invalid");
			}
		} else {
			printResult(mLastCheckSat.toString());
			try {
				while (mLexer.next_token().sym != ProofSymbols.EOF) {
					// gobble tokens
				}
			} catch (final Exception ex) {
				throw new RuntimeException("Unexpected exception", ex);
			}
		}
		return null;
	}
}
