package de.uni_freiburg.informatik.ultimatetest.summary;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider.TestResult;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public interface IIncrementalLog extends ITestLogfile {

	void addEntryPreStart(UltimateRunDefinition urd);

	void addEntryPostCompletion(UltimateRunDefinition urd, TestResult result, String resultCategory,
			String resultMessage, IUltimateServiceProvider services);

}
