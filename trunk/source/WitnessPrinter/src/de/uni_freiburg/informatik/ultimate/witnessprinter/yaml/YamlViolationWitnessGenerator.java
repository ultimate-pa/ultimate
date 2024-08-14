/*
 * Copyright (C) 2024 Helen Meyer (helen.anna.meyer@gmail.com)
 * Copyright (C) 2024 University of Freiburg
 *
 * This file is part of the ULTIMATE WitnessPrinter plug-in.
 *
 * The ULTIMATE WitnessPrinter plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE WitnessPrinter plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE WitnessPrinter plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE WitnessPrinter plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE WitnessPrinter plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.witnessprinter.yaml;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.UltimateCore;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement.StepInfo;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IBacktranslationValueProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution.ProgramState;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.FormatVersion;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.Location;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.Segment;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.ViolationSequence;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.WaypointBranching;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.WaypointFunctionEnter;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.WaypointFunctionReturn;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.WaypointTarget;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.Witness;
import de.uni_freiburg.informatik.ultimate.witnessprinter.ProgramStatePrinter;
import de.uni_freiburg.informatik.ultimate.witnessprinter.preferences.PreferenceInitializer;

/**
 * Generates a violation_sequence for an entry-based Violation Witness
 *
 * @author Helen Meyer (helen.anna.meyer@gmail.com)
 */
public class YamlViolationWitnessGenerator<TE, E> {
	private final IPreferenceProvider mPreferences;
	private final IBacktranslationValueProvider<TE, E> mStringProvider;
	private final IProgramExecution<TE, E> mExecution;
	private final ILogger mLogger;
	private final YamlWitnessWriter mWriter;
	private final ProgramStatePrinter<TE, E> mProgramStatePrinter;
	private final Map<String, String> mProgramHashes;

	public YamlViolationWitnessGenerator(final IProgramExecution<TE, E> execution, final ILogger logger,
			final IUltimateServiceProvider services) {
		mStringProvider = execution.getBacktranslationValueProvider();
		mProgramStatePrinter = new ProgramStatePrinter<>(mStringProvider);
		mLogger = logger;
		mExecution = execution;
		mPreferences = PreferenceInitializer.getPreferences(services);
		final String filename = mStringProvider.getFileNameFromStep(mExecution.getTraceElement(0).getStep());
		final String producer = mPreferences.getString(PreferenceInitializer.LABEL_GRAPH_DATA_PRODUCER);
		final String hash = mPreferences.getString(PreferenceInitializer.LABEL_GRAPH_DATA_PROGRAMHASH);
		final String spec = mPreferences.getString(PreferenceInitializer.LABEL_GRAPH_DATA_SPECIFICATION);
		final String arch = mPreferences.getString(PreferenceInitializer.LABEL_GRAPH_DATA_ARCHITECTURE);
		final FormatVersion formatVersion =
				FormatVersion.fromString(mPreferences.getString(PreferenceInitializer.LABEL_YAML_FORMAT_VERSION));
		final String version = new UltimateCore().getUltimateVersionString();
		mProgramHashes = Map.of(filename, hash);
		mWriter = YamlWitnessWriter.construct(formatVersion,
				new MetadataProvider(formatVersion, producer, version, mProgramHashes, spec, arch, "C"));
	}

	private Witness getWitness() {
		final List<Segment> segments = new ArrayList<>();
		for (int i = 0; i < mExecution.getLength(); i++) {
			final AtomicTraceElement<TE> currentATE = mExecution.getTraceElement(i);
			final TE currentStep = currentATE.getStep();
			final ProgramState<E> currentState = mExecution.getProgramState(i);
			final int startLine = mStringProvider.getLineNumberFromStep(currentStep, currentATE.getStepInfo());
			final int startColumn = mStringProvider.getColumnNumberFromStep(currentStep, currentATE.getStepInfo());
			final String function = mStringProvider.getFunctionFromStep(currentStep);
			final String filename = mStringProvider.getFileNameFromStep(currentStep);
			final Location currentLocation =
					new Location(filename, mProgramHashes.get(filename), startLine, startColumn, function);

			// TODO: Create valid assumption waypoints. We could create assumptions from currentState, but we have to
			// ensure that the location is valid in the witness. The location of assumption waypoint must point to a
			// statement or declaration.

			if (i == mExecution.getLength() - 1) {
				segments.add(new Segment(List.of(), new WaypointTarget(currentLocation)));
			}
			if (currentATE.hasStepInfo(StepInfo.CONDITION_EVAL_FALSE)) {
				segments.add(new Segment(List.of(), new WaypointBranching("false", currentLocation)));
			}
			if (currentATE.hasStepInfo(StepInfo.CONDITION_EVAL_TRUE)) {
				segments.add(new Segment(List.of(), new WaypointBranching("true", currentLocation)));
			}
			if (currentATE.hasStepInfo(StepInfo.PROC_CALL)) {
				segments.add(new Segment(List.of(), new WaypointFunctionEnter(currentLocation)));
			}
			if (currentATE.hasStepInfo(StepInfo.PROC_RETURN)) {
				segments.add(new Segment(List.of(), new WaypointFunctionReturn(
						mProgramStatePrinter.stateAsExpression(currentState, "\\result"::equals), currentLocation)));
			}
		}
		mLogger.info("Generated YAML witness of length %d.", segments.size());
		return new Witness(List.of(new ViolationSequence(segments)));
	}

	public String makeYamlString() {
		return mWriter.toString(getWitness());
	}
}
