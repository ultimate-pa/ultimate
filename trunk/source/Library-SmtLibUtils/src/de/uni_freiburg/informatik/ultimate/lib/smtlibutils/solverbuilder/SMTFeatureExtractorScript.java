/*
 * Copyright (C) 2019 Julian Löffler (loefflju@informatik.uni-freiburg.de), Breee@github
 * Copyright (C) 2012-2019 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder;

import java.io.IOException;
import java.util.ArrayDeque;
import java.util.Deque;
import java.util.Iterator;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.WrapperScript;

public class SMTFeatureExtractorScript extends WrapperScript {

	private final SMTFeatureExtractor mFeatureExtractor;
	private final Deque<Term> mCurrentAssertionStack;
	private final ILogger mLogger;

	/**
	 * Create a new script which can extract properties of SMTterms and measure time of checkSat().
	 *
	 * @param script
	 *            The wrapped script.
	 */
	public SMTFeatureExtractorScript(final Script script, final ILogger logger, final String dumpPath) {
		super(script);
		mLogger = logger;
		mFeatureExtractor = new SMTFeatureExtractor(logger, dumpPath, true);
		mCurrentAssertionStack = new ArrayDeque<>();
	}

	@Override
	public LBool assertTerm(final Term term) throws SMTLIBException {
		// TODO Auto-generated method stub
		mCurrentAssertionStack.add(term);
		return super.assertTerm(term);
	}

	@Override
	public void push(final int levels) throws SMTLIBException {
		super.push(levels);
		for (int i = levels; i >= 0; i--) {
			mCurrentAssertionStack.add(StackMarker.INSTANCE);
		}
	}

	@Override
	public void pop(final int levels) throws SMTLIBException {
		super.pop(levels);
		final Iterator<Term> iter = mCurrentAssertionStack.descendingIterator();
		Term currentTerm = null;
		for (int i = levels; i >= 0; i--) {
			while (currentTerm != StackMarker.INSTANCE) {
				currentTerm = iter.next();
				iter.remove();
			}
		}
	}

	@Override
	public LBool checkSat() throws SMTLIBException {
		final double start = System.nanoTime();
		final LBool sat = super.mScript.checkSat();
		final double analysisTime = (System.nanoTime() - start) / 1000;
		try {
			mFeatureExtractor.extractFeature(
					mCurrentAssertionStack.stream().filter(a -> a != StackMarker.INSTANCE).collect(Collectors.toList()),
					analysisTime, sat.toString(), mScript.getInfo(":name").toString());
		} catch (IllegalAccessException | IOException e) {
			mLogger.error(e);
		}
		return sat;
	}

	private static final class StackMarker extends Term {

		private static final StackMarker INSTANCE = new StackMarker();

		protected StackMarker() {
			super(-1);
		}

		@Override
		public Sort getSort() {
			throw new UnsupportedOperationException();
		}

		@Override
		protected void toStringHelper(final ArrayDeque<Object> todo) {
			throw new UnsupportedOperationException();
		}
	}

}
