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

package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.WrapperScript;

public class SMTFeatureExtractorScript extends WrapperScript {

	private final SMTFeatureExtractor mFeatureExtractor;
	private List<Term> mCurrentAssertionStack;
	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;

	/**
	 * Create a new script which can extract properties of SMTterms and measure time of checkSat().
	 *
	 * @param script
	 *            The wrapped script.
	 */
	public SMTFeatureExtractorScript(final Script script, final ILogger logger, final IUltimateServiceProvider services,
			final String dump_path) {
		super(script);
		mLogger = logger;
		mServices = services;
		mFeatureExtractor = new SMTFeatureExtractor(logger, services, dump_path);
		mCurrentAssertionStack = new ArrayList<>();
	}

	@Override
	public LBool assertTerm(final Term term) throws SMTLIBException {
		// TODO Auto-generated method stub
		mLogger.warn("ASSERT: " + term.toStringDirect());
		mCurrentAssertionStack.add(term);
		return super.assertTerm(term);
	}

	@Override
	public void push(final int levels) throws SMTLIBException {
		// TODO Auto-generated method stub
		mLogger.warn("PUSH " + levels);
		super.push(levels);
	}

	@Override
	public void pop(final int levels) throws SMTLIBException {
		// TODO Auto-generated method stub
		mLogger.warn("POP " + levels);
		super.pop(levels);
	}

	@Override
	public LBool checkSat() throws SMTLIBException {
		mLogger.warn("CHECK SAT");
		final double start = System.nanoTime();
		final LBool sat = super.mScript.checkSat();
		final double analysisTime = (System.nanoTime() - start) / 1000;
		try {
			mFeatureExtractor.extractFeature(mCurrentAssertionStack, analysisTime, sat.toString());
			mCurrentAssertionStack = new ArrayList<>();
		} catch (IllegalAccessException | IOException e) {
			mLogger.error(e);
		}
		return sat;
	}

}
