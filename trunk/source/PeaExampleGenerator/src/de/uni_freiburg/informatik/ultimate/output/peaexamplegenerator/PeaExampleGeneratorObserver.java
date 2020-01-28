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
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.concurrent.atomic.AtomicInteger;

import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.core.lib.observers.BaseObserver;
import de.uni_freiburg.informatik.ultimate.core.lib.results.ResultUtil;
import de.uni_freiburg.informatik.ultimate.core.lib.util.MonitoredProcess;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.test.util.TestUtil;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_frieburg.informatik.ultimate.pea2boogie.testgen.ReqTestResultTest;
import de.uni_frieburg.informatik.ultimate.pea2boogie.testgen.TestStep;

/**
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Nico Hauff (hauffn@informatik.uni-freiburg.de)
 */
public class PeaExampleGeneratorObserver extends BaseObserver {
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;

	private static String PYTHON_SCRIPT =
			"/media/Daten/projects/ultimate/releaseScripts/default/adds/timing_diagram.py";
	// private static String PYTHON_SCRIPT = "releaseScripts/default/adds/timing_diagram.py";
	private static String OUTPUT_DIR = "examples/Requirements/failure-paths/";
	private static String FILE_EXT = ".svg";

	public PeaExampleGeneratorObserver(final IUltimateServiceProvider services) {
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mServices = services;
	}

	@Override
	public boolean process(final IElement root) {
		// We only operate on {@link IResult}s, so we do not need a model.
		return false;
	}

	@Override
	public void finish() {
		final Map<String, List<IResult>> results = mServices.getResultService().getResults();
		final Collection<ReqTestResultTest> reqTestResults = ResultUtil.filterResults(results, ReqTestResultTest.class);
		final String patternName = "BndDelayedResponsePatternUT_Globally";

		int i = 0;
		for (final Iterator<ReqTestResultTest> it = reqTestResults.iterator(); it.hasNext(); i++) {
			final Map<String, Pair<List<Integer>, List<Integer>>> observables = new HashMap<>();
			final AtomicInteger clock = new AtomicInteger();
			final List<TestStep> steps = it.next().getTestSteps();

			for (final TestStep step : steps) {
				step.getInputAssignment().forEach((k, v) -> parseAssignment(k, v, observables, clock.get()));
				step.getOutputAssignment().forEach((k, v) -> parseAssignment(k, v, observables, clock.get()));

				assert (step.getWaitTime().size() == 1);
				final RealLiteral waitTime = ((RealLiteral) step.getWaitTime().iterator().next());
				clock.getAndAdd(Integer.parseInt(waitTime.getValue()));
			}

			try {
				final String[] command = new String[] { "python3", PYTHON_SCRIPT, "-o",
						TestUtil.getPathFromTrunk(OUTPUT_DIR) + "/" + patternName + "_" + i + FILE_EXT, "-a", "1" };
				// final String[] command = new String[] { "python3", TestUtil.getPathFromTrunk(PYTHON_SCRIPT), "-o",
				// TestUtil.getPathFromTrunk(OUTPUT_DIR + "/" + patternName + "_" + i + FILE_EXT), "-a", "1" };
				final MonitoredProcess process = MonitoredProcess.exec(command, null, null, mServices);

				final BufferedWriter writer = new BufferedWriter(new OutputStreamWriter(process.getOutputStream()));
				writer.write(jsonString(patternName, observables));
				writer.close();

				process.waitfor();
			} catch (final IOException | InterruptedException e) {
				throw new RuntimeException(e.getMessage());
			}
		}
	}

	private static void parseAssignment(final IdentifierExpression identifier, final Collection<Expression> expressions,
			final Map<String, Pair<List<Integer>, List<Integer>>> observables, final int clock) {

		assert (expressions.size() == 1);
		final int value = ((BooleanLiteral) expressions.iterator().next()).getValue() ? 1 : 0;
		final Pair<List<Integer>, List<Integer>> values = observables.computeIfAbsent(identifier.getIdentifier(),
				e -> new Pair<>(new ArrayList<>(), new ArrayList<>()));

		values.getFirst().add(clock);
		values.getSecond().add(value);
	}

	private static String jsonString(final String id, final Map<String, Pair<List<Integer>, List<Integer>>> signals) {
		final StringBuilder result = new StringBuilder();

		for (final Entry<String, Pair<List<Integer>, List<Integer>>> signal : signals.entrySet()) {
			result.append("{");
			result.append("\"id\": \"" + signal.getKey() + "\", ");
			result.append("\"x\": " + signal.getValue().getFirst() + ", ");
			result.append("\"y\": " + signal.getValue().getSecond());
			result.append("}, ");
		}
		result.setLength(result.length() - 2);

		result.insert(0, "{\"id\": \"" + id + "\", \"signals\": [");
		result.append("]}");

		return result.toString();
	}
}
