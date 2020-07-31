/*
 * Copyright (C) 2020 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
 *
 * This file is part of the ULTIMATE Test Library.
 *
 * The ULTIMATE Test Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Test Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Test Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Test Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Test Library grant you additional permission
 * to convey the resulting work.
 */
/**
 *
 */
package de.uni_freiburg.informatik.ultimate.ultimatetest.suites.buchiautomizer;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.LTLCheckerTestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.TermcompTestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.expectedresult.AbstractExpectedResultFinder;
import de.uni_freiburg.informatik.ultimate.test.decider.expectedresult.IExpectedResultFinder;
import de.uni_freiburg.informatik.ultimate.test.decider.overallresult.SafetyCheckerOverallResult;
import de.uni_freiburg.informatik.ultimate.test.util.UltimateRunDefinitionGenerator;

/**
 * @author klumpp@informatik.uni-freiburg.de
 *
 */
public class ClinicalGuidelinesTest extends AbstractBuchiAutomizerTestSuite {

	/**
	 * {@inheritDoc}
	 */
	@Override
	public long getTimeout() {
		return 60 * 1000;
	}

	/**
	 * List of path to setting files. Ultimate will run on each program with each
	 * setting that is defined here. The path are defined relative to the folder
	 * "trunk/examples/settings/", because we assume that all settings files are in
	 * this folder.
	 *
	 */
	private static final String[] mSettings = { "Bora_MA_ClinicalGuidelines.epf", };

	private static final Map<String, Boolean> mProperties = new HashMap<>();
	static {
		mProperties.put("AP(hasSymptoms)", false);
		mProperties.put("AP(hasSymptoms) ==> F AP(diagnos == NoCancer || (diagnos == HRC || (diagnos == MRC)) || (diagnos == LRC) || diagnos == CC)", true);
		mProperties.put("AP(!hasSymptoms)", false);
	}

	private static final String[] mCToolchains = { "LTLAutomizer.xml", };

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		for (final String setting : mSettings) {
			for (final String toolchain : mCToolchains) {
				UltimateRunDefinition urd = UltimateRunDefinitionGenerator.getRunDefinitionFromTrunk(
						"/../../Teaching/MasterThesis_Bora/Final_BoogieCode.bpl", setting, toolchain, getTimeout());

				for (final String property : mProperties.keySet()) {
					ITestResultDecider decider = new LTLCheckerTestResultDecider(urd, false) {
						@Override
						public IExpectedResultFinder<SafetyCheckerOverallResult> constructExpectedResultFinder() {
							return new ExpectedResultFinder(property);
						}
					};
					mTestCases
							.add(new UltimateTestCase(decider, urd, new ArrayList<>(), t -> setProperty(property, t), property));
				}
			}
		}
		return super.createTestCases();
	}

	private IUltimateServiceProvider setProperty(String property, IUltimateServiceProvider provider) {
		String pluginId = "de.uni_freiburg.informatik.ultimate.ltl2aut";
		String setting = "Property to check";

		IUltimateServiceProvider layer = provider.registerPreferenceLayer(ClinicalGuidelinesTest.class, pluginId);
		IPreferenceProvider prefProvider = layer.getPreferenceProvider(pluginId);
		prefProvider.put(setting, property);
		return layer;
	}


	private static class ExpectedResultFinder extends AbstractExpectedResultFinder<SafetyCheckerOverallResult> {

		private final String mProperty;

		public ExpectedResultFinder(String property) {
			mProperty = property;
		}

		@Override
		public void findExpectedResult(UltimateRunDefinition ultimateRunDefinition) {
			Boolean result = mProperties.get(mProperty);
			if (result == null) {
				mEvaluationStatus = ExpectedResultFinderStatus.ERROR;
				mExpectedResultEvaluation = "No non-null expected satisfaction stored for " + mProperty;
			} else {
				mEvaluationStatus = ExpectedResultFinderStatus.EXPECTED_RESULT_FOUND;
				mExpectedResult = result ? SafetyCheckerOverallResult.SAFE : SafetyCheckerOverallResult.UNSAFE;
				mExpectedResultEvaluation = "Expected result: " + mExpectedResult;
			}
		}

	}
}
