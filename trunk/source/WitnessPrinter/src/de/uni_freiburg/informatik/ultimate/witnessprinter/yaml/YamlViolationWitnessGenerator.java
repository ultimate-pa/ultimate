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
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.UltimateCore;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement.StepInfo;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IBacktranslationValueProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.FormatVersion;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.Location;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.Segment;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.Segment.SegmentType;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.ViolationSequence;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.Waypoint;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.WaypointAssumption;
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
public class YamlViolationWitnessGenerator {
	private final IPreferenceProvider mPreferences;
	private final ILogger mLogger;
	private YamlWitnessWriter mWriter;
	private final FormatVersion mFormatVersion;
	private final boolean mAddThreadIds;
	private final List<Segment> mSegments = new ArrayList<>();

	// TODO: If when we produce assumptions, we should exclude them for the loop of termination witnesses
	private static final boolean PRODUCE_ASSUMPTIONS = false;

	public YamlViolationWitnessGenerator(final ILogger logger, final IUltimateServiceProvider services) {
		mLogger = logger;
		mPreferences = PreferenceInitializer.getPreferences(services);
		mFormatVersion =
				FormatVersion.fromString(mPreferences.getString(PreferenceInitializer.LABEL_YAML_FORMAT_VERSION));
		mAddThreadIds = mFormatVersion.compareTo(new FormatVersion(2, 2)) >= 0;
	}

	private YamlWitnessWriter createWriter(final String filename) {
		final String producer = mPreferences.getString(PreferenceInitializer.LABEL_GRAPH_DATA_PRODUCER);
		final String hash = mPreferences.getString(PreferenceInitializer.LABEL_GRAPH_DATA_PROGRAMHASH);
		final String spec = mPreferences.getString(PreferenceInitializer.LABEL_GRAPH_DATA_SPECIFICATION);
		final String arch = mPreferences.getString(PreferenceInitializer.LABEL_GRAPH_DATA_ARCHITECTURE);
		final String version = new UltimateCore().getUltimateVersionString();
		final Map<String, String> programHashes = Map.of(filename, hash);
		return YamlWitnessWriter.construct(mFormatVersion,
				new MetadataProvider(mFormatVersion, producer, version, programHashes, spec, arch, "C"));
	}

	public <TE, E> YamlViolationWitnessGenerator addSegments(final IProgramExecution<TE, E> execution,
			final SegmentType segmentType, final Set<Integer> targetIndices) {
		final IBacktranslationValueProvider<TE, E> stringProvider = execution.getBacktranslationValueProvider();
		if (mWriter == null && execution.getLength() > 0) {
			final String filename = stringProvider.getFileNameFromStep(execution.getTraceElement(0).getStep());
			mWriter = createWriter(filename);
		}
		final List<Waypoint> targetWaypoints = new ArrayList<>();
		final ProgramStatePrinter<TE, E> programStatePrinter = new ProgramStatePrinter<>(stringProvider);
		for (int i = 0; i < execution.getLength(); i++) {
			final AtomicTraceElement<TE> currentATE = execution.getTraceElement(i);

			if (PRODUCE_ASSUMPTIONS && stringProvider.isValidAssumptionLocation(currentATE.getStep())) {
				final String previousState = programStatePrinter.stateAsExpression(
						i == 0 ? null : execution.getProgramState(i - 1), ProgramStatePrinter::isValidCVariable);
				if (previousState != null) {
					mSegments.add(new Segment(new WaypointAssumption(previousState,
							getLocation(currentATE, false, stringProvider), getThreadId(currentATE)), segmentType));
				}
			}

			if (currentATE.hasAnyStepInfo(StepInfo.FORK) && currentATE.getForkedThreadId() == -1) {
				// Omit auxiliary forks from the witness
				continue;
			}

			if (targetIndices.contains(i)) {
				targetWaypoints.add(
						new WaypointTarget(getLocation(currentATE, true, stringProvider), getThreadId(currentATE)));
			}
			if (currentATE.hasStepInfo(StepInfo.CONDITION_EVAL_FALSE)) {
				mSegments.add(new Segment(new WaypointBranching("false", getLocation(currentATE, false, stringProvider),
						getThreadId(currentATE)), segmentType));
			}
			if (currentATE.hasStepInfo(StepInfo.CONDITION_EVAL_TRUE)) {
				mSegments.add(new Segment(new WaypointBranching("true", getLocation(currentATE, false, stringProvider),
						getThreadId(currentATE)), segmentType));
			}
			if (currentATE.hasStepInfo(StepInfo.PROC_CALL)) {
				mSegments.add(new Segment(new WaypointFunctionEnter(getLocation(currentATE, false, stringProvider),
						getThreadId(currentATE)), segmentType));
			}
			if (currentATE.hasStepInfo(StepInfo.PROC_RETURN)) {
				mSegments.add(new Segment(new WaypointFunctionReturn(
						programStatePrinter.stateAsExpression(execution.getProgramState(i), "\\result"::equals),
						getLocation(currentATE, false, stringProvider), getThreadId(currentATE)), segmentType));
			}
			if (currentATE.hasAnyStepInfo(StepInfo.FORK)) {
				mSegments.add(new Segment(new WaypointFunctionEnter(getLocation(currentATE, false, stringProvider),
						getThreadId(currentATE)), segmentType));
			}
		}
		if (!targetWaypoints.isEmpty()) {
			mSegments.add(new Segment(targetWaypoints, segmentType));
		}
		return this;
	}

	private Integer getThreadId(final AtomicTraceElement<?> ate) {
		if (!mAddThreadIds || !ate.hasThreadId()) {
			return null;
		}
		return ate.getThreadId();
	}

	private static <TE, E> Location getLocation(final AtomicTraceElement<TE> ate, final boolean isTarget,
			final IBacktranslationValueProvider<TE, E> stringProvider) {
		final TE currentStep = ate.getStep();
		final int line = stringProvider.getLineNumberFromStep(currentStep, ate.getStepInfo());
		final int column = stringProvider.getColumnNumberFromStep(currentStep, ate.getStepInfo());
		final String function = stringProvider.getFunctionFromStep(currentStep);
		final String filename = stringProvider.getFileNameFromStep(currentStep);
		// WORKAROUND: We only use the column in the target waypoint for unreach-call
		// For other properties our column do not yet match the witness format. The target waypoint should point
		// to a full expression or statement
		// (https://gitlab.com/sosy-lab/benchmarking/sv-witnesses/-/blob/main/user-guide/Witness-Format.md#target)
		if (isTarget && !currentStep.toString().contains("reach_error")) {
			return new Location(filename, line, null, function);
		}
		return new Location(filename, line, column, function);
	}

	/**
	 * @return a violation witness for the program {@code filename} with no segment: it claims a violation, but names no
	 *         waypoint, not even the target
	 */
	public String makeEmptyYamlString(final String filename) {
		if (mWriter != null || !mSegments.isEmpty()) {
			throw new IllegalStateException("Segments were added, the witness is not empty");
		}
		mWriter = createWriter(filename);
		mLogger.info("Generated YAML witness without waypoints.");
		return mWriter.toString(new Witness(List.of(new ViolationSequence(mSegments))));
	}

	public String makeYamlString() {
		if (mWriter == null) {
			throw new IllegalStateException("Add a non-empty execution before generating the witness");
		}
		mLogger.info("Generated YAML witness of length %d.", mSegments.size());
		return mWriter.toString(new Witness(List.of(new ViolationSequence(mSegments))));
	}
}
