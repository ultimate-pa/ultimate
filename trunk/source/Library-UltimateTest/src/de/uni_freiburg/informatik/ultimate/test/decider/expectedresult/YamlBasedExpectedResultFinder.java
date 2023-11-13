/*
 * Copyright (C) 2019 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE UnitTest Library.
 *
 * The ULTIMATE UnitTest Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE UnitTest Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE UnitTest Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE UnitTest Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE UnitTest Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.test.decider.expectedresult;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.yaml.snakeyaml.Yaml;

import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

/**
 * Find the expected result for an SV-COMP benchmark. Starting from SV-COMP 2020 the expected results are given by YAML
 * files. This class does not use a proper YAML parser and is a hack that should work for the YAML files that are
 * currently in the competition repository. https://github.com/sosy-lab/sv-benchmarks/
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class YamlBasedExpectedResultFinder<OVERALL_RESULT> extends AbstractExpectedResultFinder<OVERALL_RESULT> {
	private final NestedMap2<String, String, OVERALL_RESULT> mResultMap;

	public YamlBasedExpectedResultFinder(final NestedMap2<String, String, OVERALL_RESULT> resultMap) {
		mResultMap = resultMap;
	}

	@Override
	public void findExpectedResult(final UltimateRunDefinition ultimateRunDefinition) {
		final File file = ultimateRunDefinition.selectPrimaryInputFile();
		final String[] basenameAndExtension = file.getAbsolutePath().split("\\.(?=[^\\.]+$)");
		final String yamlFilename = basenameAndExtension[0] + ".yml";
		final File yamlFile = new File(yamlFilename);
		final Set<OVERALL_RESULT> expectedResult = new HashSet<>();
		try {
			for (final String propertyFile : mResultMap.keySet()) {
				final OVERALL_RESULT resultForPropertyFile = extractResultForPropertyFile(yamlFile, propertyFile);
				if (resultForPropertyFile != null) {
					expectedResult.add(resultForPropertyFile);
				}
			}
		} catch (final UnsupportedOperationException uae) {
			super.mExpectedResult = null;
			super.mEvaluationStatus = ExpectedResultFinderStatus.ERROR;
			super.mExpectedResultEvaluation = uae.toString();
		} catch (final FileNotFoundException fnfe) {
			super.mExpectedResult = null;
			super.mEvaluationStatus = ExpectedResultFinderStatus.NO_EXPECTED_RESULT_FOUND;
			super.mExpectedResultEvaluation = "YAML file does not exist";
		} catch (final IOException e) {
			throw new AssertionError("unable to read file " + file);
		}
		if (expectedResult.isEmpty()) {
			super.mExpectedResult = null;
			super.mEvaluationStatus = ExpectedResultFinderStatus.NO_EXPECTED_RESULT_FOUND;
			super.mExpectedResultEvaluation =
					"Neither filename nor path nor first line contains a keyword that defines the expected result";
		} else if (expectedResult.size() == 1) {
			super.mExpectedResult = expectedResult.iterator().next();
			super.mEvaluationStatus = ExpectedResultFinderStatus.EXPECTED_RESULT_FOUND;
			super.mExpectedResultEvaluation = "Expected result: " + mExpectedResult;
		} else {
			super.mExpectedResult = null;
			super.mEvaluationStatus = ExpectedResultFinderStatus.ERROR;
			super.mExpectedResultEvaluation = "Error: annotation given by keywords is inconsistent";
		}
	}

	@SuppressWarnings("unchecked")
	private OVERALL_RESULT extractResultForPropertyFile(final File yamlFile, final String propertyFile)
			throws IOException {
		final Map<String, Object> rootMapping = new Yaml().load(new FileInputStream(yamlFile));
		final List<Map<String, Object>> properties = (List<Map<String, Object>>) rootMapping.get("properties");
		for (final Map<String, Object> property : properties) {
			final String test = (String) property.get("property_file");
			if (!test.endsWith(propertyFile)) {
				continue;
			}
			final Boolean expectedVerdict = (Boolean) property.get("expected_verdict");
			if (expectedVerdict == null) {
				throw new IllegalArgumentException("expected_verdict has to be either true or false");
			}
			if (expectedVerdict) {
				return mResultMap.get(propertyFile, String.valueOf(true));
			}
			assert !expectedVerdict;
			final Map<String, OVERALL_RESULT> map = mResultMap.get(propertyFile);
			if (map.containsKey(String.valueOf(false))) {
				// there are no subproperties for this property
				return mResultMap.get(propertyFile, String.valueOf(false));
			}
			final String subproperty = (String) property.get("subproperty");
			if (subproperty == null) {
				throw new UnsupportedOperationException("Cannot understand YAML file");
			}
			return mResultMap.get(propertyFile, subproperty);
		}
		return null;
	}
}
