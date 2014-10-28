package de.uni_freiburg.informatik.ultimate.core.coreplugin.cexverifier;

import java.util.Collection;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.core.services.IBacktranslationService;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.util.Util;
import de.uni_freiburg.informatik.ultimate.result.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class CexVerifier {

	private final Logger mLogger;
	private final IUltimateServiceProvider mServices;

	public CexVerifier(Logger logger, IUltimateServiceProvider services) {
		mLogger = logger;
		mServices = services;
	}

	public void verify() {
		Collection<CounterExampleResult> cexResults = Util.filterResults(mServices.getResultService().getResults(),
				CounterExampleResult.class);

		IBacktranslationService backtrans = mServices.getBacktranslationService();

		for (CounterExampleResult cex : cexResults) {
			IProgramExecution pe = backtrans.translateProgramExecution(cex.getProgramExecution());
			String svcompWitness = pe.getSVCOMPWitnessString();
			if (svcompWitness == null) {
				// report something
			} else {
				boolean success = checkWitness(svcompWitness, cex.getLongDescription());
				//report even more
			}
		}
	}

	private boolean checkWitness(String svcompWitness, String longDescription) {
		UltimatePreferenceStore ups = new UltimatePreferenceStore(Activator.s_PLUGIN_ID);
		
		return false;
	}

}
