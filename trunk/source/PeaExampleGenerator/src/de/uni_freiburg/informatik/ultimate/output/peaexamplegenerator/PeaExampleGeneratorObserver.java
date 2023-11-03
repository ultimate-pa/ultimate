/*
 * Copyright (C) 2020 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
 *
 * This file is part of the ULTIMATE PeaExampleGenerator plug-in.
 *
 * The ULTIMATE PeaExampleGenerator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE PeaExampleGenerator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE PeaExampleGenerator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE PeaExampleGenerator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE PeaExampleGenerator plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.output.peaexamplegenerator;

import java.io.BufferedWriter;
import java.io.File;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.util.Arrays;
import java.util.Collection;
import java.util.Formatter;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.core.lib.observers.BaseObserver;
import de.uni_freiburg.informatik.ultimate.core.lib.results.ResultUtil;
import de.uni_freiburg.informatik.ultimate.core.lib.util.MonitoredProcess;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.DeclarationPattern;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.output.peaexamplegenerator.preferences.PeaExampleGeneratorPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.pea2boogie.PatternContainer;
import de.uni_freiburg.informatik.ultimate.pea2boogie.testgen.ReqTestResultTest;
import de.uni_freiburg.informatik.ultimate.pea2boogie.testgen.TestStep;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;

/**
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Nico Hauff (hauffn@informatik.uni-freiburg.de)
 */
public class PeaExampleGeneratorObserver extends BaseObserver {
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final File mScriptFile;
	private final File mOutputDir;
	private final String mOutputFileExtension;
	private String mScopeName;
	private String mPatternName;

	public PeaExampleGeneratorObserver(final IUltimateServiceProvider services) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);

		mScriptFile = new File(mServices.getPreferenceProvider(Activator.PLUGIN_ID)
				.getString(PeaExampleGeneratorPreferenceInitializer.LABEL_PYTHON_SCRIPT));
		mOutputDir = new File(mServices.getPreferenceProvider(Activator.PLUGIN_ID)
				.getString(PeaExampleGeneratorPreferenceInitializer.LABEL_OUTPUT_DIRECTORY));
		mOutputFileExtension = mServices.getPreferenceProvider(Activator.PLUGIN_ID)
				.getString(PeaExampleGeneratorPreferenceInitializer.LABEL_OUTPUT_FILE_EXTENSION);

		if (!mScriptFile.exists()) {
			throw new RuntimeException("Unable to find file: '" + mScriptFile.getPath() + "'.");
		}

		if (!mOutputDir.exists()) {
			throw new RuntimeException("Unable to find directory: '" + mOutputDir.getPath() + "'.");
		}
	}

	@Override
	public boolean process(final IElement root) {
		final PatternContainer patternContainer = PatternContainer.getAnnotation(root);
		if (patternContainer == null) {
			throw new UnsupportedOperationException("Unable to extract pattern from model.");
		}

		final List<PatternType<?>> patterns = patternContainer.getPatterns();
		if (patterns == null || patterns.isEmpty()) {
			throw new UnsupportedOperationException("No pattern in: " + PatternContainer.class);
		}

		final List<PatternType<?>> nonInitPatterns =
				patterns.stream().filter(e -> !(e instanceof DeclarationPattern)).collect(Collectors.toList());

		if (nonInitPatterns.isEmpty()) {
			throw new UnsupportedOperationException("No non-init pattern in: " + PatternContainer.class + ", have "
					+ patterns.size() + " patterns: "
					+ patterns.stream().map(a -> a.getClass().getSimpleName()).collect(Collectors.joining(", ")));
		}
		if (nonInitPatterns.size() > 1) {
			throw new UnsupportedOperationException("Cannot handle more than one pattern, ask Nico to implement it.");
		}

		final PatternType<?> pattern = nonInitPatterns.iterator().next();
		mScopeName = pattern.getScope().getName();
		mPatternName = pattern.getName();

		return false;
	}

	@Override
	public void finish() {
		final Map<String, List<IResult>> results = mServices.getResultService().getResults();
		final HashSet<Map<String, String>> signals = new HashSet<>();
		int j = 0;
		final List<ReqTestResultTest> reqTestResultTests =
				(List<ReqTestResultTest>) ResultUtil.filterResults(results, ReqTestResultTest.class);

		if (reqTestResultTests.isEmpty()) {
			throw new RuntimeException("No test results found.");
		}

		for (int i = 0; i < reqTestResultTests.size(); i++) {
			final Map<String, String> observables = new HashMap<>();
			final List<TestStep> testSteps = reqTestResultTests.get(i).getTestSteps();

			final Set<String> identifiers = new HashSet<>();
			testSteps.forEach(e -> identifiers.addAll(e.getIdentifier()));

			for (final TestStep step : testSteps) {
				assert (step.getWaitTime().size() == 1);
				final int waitTime = Integer.parseInt(((RealLiteral) step.getWaitTime().iterator().next()).getValue());

				final Set<String> dontCares = new HashSet<>(identifiers);

				// Consider waitForAssignements as dont-cares, except for the last test step
				if (i != testSteps.size() - 1) {
					step.getInputAssignment().forEach((k, v) -> dontCares.remove(k.getIdentifier()));
					step.getOutputAssignment().forEach((k, v) -> dontCares.remove(k.getIdentifier()));
				} else {
					dontCares.removeAll(step.getIdentifier());
				}

				step.getInputAssignment()
						.forEach((k, v) -> parseAssignment(k.getIdentifier(), v, waitTime, observables));

				step.getOutputAssignment()
						.forEach((k, v) -> parseAssignment(k.getIdentifier(), v, waitTime, observables));

				// waitForAssignments only need to be dealt with in the last test step (as they are considered as output
				// assignments in the following test step)
				if (i == testSteps.size() - 1) {
					step.getWaitForAssignment()
							.forEach((k, v) -> parseWaitForAssignment(k.getIdentifier(), v, waitTime, observables));
					// In case there are waitForAssignments, the input must be prolonged by 1 time unit
					if (!step.getWaitForAssignment().isEmpty()) {
						step.getInputAssignment()
								.forEach((k, v) -> parseAssignment(k.getIdentifier(), v, 1, observables));
					}
				}

				dontCares.forEach(k -> parseAssignment(k, null, waitTime, observables));
			}

			// Do not generate duplicates.
			if (!signals.add(observables)) {
				continue;
			}

			try {
				final String[] command = new String[] { "python", mScriptFile.getPath(), "-o",
						mOutputDir.getPath() + "/" + mPatternName + "_" + mScopeName + "_" + j + mOutputFileExtension };

				final MonitoredProcess process = MonitoredProcess.exec(command, null, null, mServices);
				final BufferedWriter writer = new BufferedWriter(new OutputStreamWriter(process.getOutputStream()));
				writer.write(jsonString(mPatternName + "_" + mScopeName, observables));
				writer.close();

				final int returnCode = process.waitfor().getReturnCode();
				if (returnCode != 0) {
					throw new RuntimeException(String.format("%s did return %s. Stdout: %s Stderr: %s",
							Arrays.stream(command).collect(Collectors.joining(" ")), returnCode,
							CoreUtil.convertStreamToString(process.getInputStream()),
							CoreUtil.convertStreamToString(process.getErrorStream())));
				}
			} catch (final IOException | InterruptedException e) {
				throw new RuntimeException(e);
			}
			j++;
		}
	}

	private static void parseAssignment(final String identifier, final Collection<Expression> expression,
			final int waitTime, final Map<String, String> observables) {

		final String values = observables.computeIfAbsent(identifier, e -> new String());
		String value = "x";

		if (expression != null) {
			assert (expression.size() == 1);
			value = ((BooleanLiteral) expression.iterator().next()).getValue() ? "h" : "l";
		}
		value = values.endsWith(value) ? "." : value;

		for (int i = 0; i < waitTime - 1; i++) {
			value += ".";
		}
		observables.put(identifier, values + value);
	}

	private static void parseWaitForAssignment(final String identifier, final Collection<Expression> expression,
			final int waitTime, final Map<String, String> observables) {

		final String values = observables.computeIfAbsent(identifier, e -> new String());
		String value = "";
		String waitForValue = "x";

		for (int i = 0; i < waitTime; i++) {
			value += ".";
		}
		if (expression != null) {
			assert (expression.size() == 1);
			waitForValue = ((BooleanLiteral) expression.iterator().next()).getValue() ? "h" : "l";
		}
		value += waitForValue;

		observables.put(identifier, values + value);
	}

	private static String jsonString(final String name, final Map<String, String> signals) {
		final StringBuilder result = new StringBuilder();

		for (final Entry<String, String> signal : signals.entrySet()) {
			final Formatter fmt = new Formatter();
			fmt.format("{\"name\": \"%s\", \"wave\": \"%s\"}", signal.getKey(), signal.getValue());

			if (result.length() > 0) {
				result.append(", ");
			}
			result.append(fmt.toString());
			fmt.close();
		}

		result.insert(0, "{\"signal\": [");
		result.append("], ");
		result.append("\"head\": {\"text\": \"" + name + "\"}");
		result.append("}");

		System.out.println(result.toString());

		return result.toString();
	}
}
