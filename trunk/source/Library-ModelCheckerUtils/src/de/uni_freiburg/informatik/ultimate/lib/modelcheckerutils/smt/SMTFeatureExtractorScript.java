package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
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
		mCurrentAssertionStack = new ArrayList<Term>();
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
			mCurrentAssertionStack = new ArrayList<Term>();
		} catch (IllegalAccessException | IOException e) {
			mLogger.error(e);
		}
		return sat;
	}

}
