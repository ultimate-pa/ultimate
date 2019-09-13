package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt;

import java.io.IOException;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.WrapperScript;

public class SMTFeatureExtractorScript extends WrapperScript {

	private final SMTFeatureExtractor mFeatureExtractor;
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
	}

	@Override
	public LBool assertTerm(final Term term) throws SMTLIBException {
		// TODO Auto-generated method stub
		return super.assertTerm(term);
	}

	@Override
	public void push(final int levels) throws SMTLIBException {
		// TODO Auto-generated method stub
		super.push(levels);
	}

	@Override
	public void pop(final int levels) throws SMTLIBException {
		// TODO Auto-generated method stub
		super.pop(levels);
	}

	@Override
	public LBool checkSat() throws SMTLIBException {
		final double start = System.nanoTime();
		final LBool sat = super.mScript.checkSat();
		final double analysisTime = (System.nanoTime() - start) / 1000;
		final Term[] assertions = super.mScript.getAssertions();
		try {
			mFeatureExtractor.extractFeature(assertions, analysisTime, sat.toString());
		} catch (IllegalAccessException | IOException e) {
			mLogger.error(e);
		}
		return sat;
	}

}
