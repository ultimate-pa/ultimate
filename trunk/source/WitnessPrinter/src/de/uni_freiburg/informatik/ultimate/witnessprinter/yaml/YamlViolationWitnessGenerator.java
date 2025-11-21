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
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.FormatVersion;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.Location;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.Segment;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.Segment.SegmentType;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.ViolationSequence;
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
public class YamlViolationWitnessGenerator<TE, E> {
	private final IPreferenceProvider mPreferences;
	private final IBacktranslationValueProvider<TE, E> mStringProvider;
	private final ILogger mLogger;
	private final YamlWitnessWriter mWriter;
	private final ProgramStatePrinter<TE, E> mProgramStatePrinter;
	private IProgramExecution<TE, E> mStem;
	private IProgramExecution<TE, E> mLoop;

	// TODO: If when we produce assumptions, we should exclude them for the loop of termination witnesses
	private static final boolean PRODUCE_ASSUMPTIONS = false;

	public YamlViolationWitnessGenerator(final IProgramExecution<TE, E> execution, final ILogger logger,
			final IUltimateServiceProvider services) {
		this(execution, null, logger, services);
	}

	public YamlViolationWitnessGenerator(final IProgramExecution<TE, E> stem, final IProgramExecution<TE, E> loop,
			final ILogger logger, final IUltimateServiceProvider services) {
		mStringProvider = stem.getBacktranslationValueProvider();
		mProgramStatePrinter = new ProgramStatePrinter<>(mStringProvider);
		mLogger = logger;
		mStem = stem;
		mLoop = loop;
		mPreferences = PreferenceInitializer.getPreferences(services);
		final String filename = mStringProvider.getFileNameFromStep(stem.getTraceElement(0).getStep());
		final String producer = mPreferences.getString(PreferenceInitializer.LABEL_GRAPH_DATA_PRODUCER);
		final String hash = mPreferences.getString(PreferenceInitializer.LABEL_GRAPH_DATA_PROGRAMHASH);
		final String spec = mPreferences.getString(PreferenceInitializer.LABEL_GRAPH_DATA_SPECIFICATION);
		final String arch = mPreferences.getString(PreferenceInitializer.LABEL_GRAPH_DATA_ARCHITECTURE);
		final FormatVersion formatVersion =
				FormatVersion.fromString(mPreferences.getString(PreferenceInitializer.LABEL_YAML_FORMAT_VERSION));
		final String version = new UltimateCore().getUltimateVersionString();
		final Map<String, String> programHashes = Map.of(filename, hash);
		mWriter = YamlWitnessWriter.construct(formatVersion,
				new MetadataProvider(formatVersion, producer, version, programHashes, spec, arch, "C"));
	}

	private List<Segment> getSegments(final IProgramExecution<TE, E> execution, final SegmentType segmentType,
			final boolean addTargetWaypoint) {
		final List<Segment> segments = new ArrayList<>();
		for (int i = 0; i < execution.getLength(); i++) {
			final AtomicTraceElement<TE> currentATE = execution.getTraceElement(i);

			if (PRODUCE_ASSUMPTIONS && mStringProvider.isValidAssumptionLocation(currentATE.getStep())) {
				final String previousState = mProgramStatePrinter.stateAsExpression(
						i == 0 ? null : execution.getProgramState(i - 1), ProgramStatePrinter::isValidCVariable);
				if (previousState != null) {
					segments.add(new Segment(List.of(),
							new WaypointAssumption(previousState, getLocation(currentATE, false)), segmentType));
				}
			}

			if (addTargetWaypoint && i == execution.getLength() - 1) {
				segments.add(new Segment(List.of(), new WaypointTarget(getLocation(currentATE, true)), segmentType));
			}
			if (currentATE.hasStepInfo(StepInfo.CONDITION_EVAL_FALSE)) {
				segments.add(new Segment(List.of(), new WaypointBranching("false", getLocation(currentATE, false)),
						segmentType));
			}
			if (currentATE.hasStepInfo(StepInfo.CONDITION_EVAL_TRUE)) {
				segments.add(new Segment(List.of(), new WaypointBranching("true", getLocation(currentATE, false)),
						segmentType));
			}
			if (currentATE.hasStepInfo(StepInfo.PROC_CALL)) {
				segments.add(
						new Segment(List.of(), new WaypointFunctionEnter(getLocation(currentATE, false)), segmentType));
			}
			if (currentATE.hasStepInfo(StepInfo.PROC_RETURN)) {
				segments.add(
						new Segment(List.of(),
								new WaypointFunctionReturn(mProgramStatePrinter
										.stateAsExpression(execution.getProgramState(i), "\\result"::equals),
										getLocation(currentATE, false)),
								segmentType));
			}
		}
		return segments;
	}

	private Location getLocation(final AtomicTraceElement<TE> ate, final boolean isTarget) {
		final TE currentStep = ate.getStep();
		final int line = mStringProvider.getLineNumberFromStep(currentStep, ate.getStepInfo());
		final int column = mStringProvider.getColumnNumberFromStep(currentStep, ate.getStepInfo());
		final String function = mStringProvider.getFunctionFromStep(currentStep);
		final String filename = mStringProvider.getFileNameFromStep(currentStep);
		// WORKAROUND: We only use the column in the target waypoint for unreach-call
		// For other properties our column do not yet match the witness format. The target waypoint should point
		// to a full expression or statement
		// (https://gitlab.com/sosy-lab/benchmarking/sv-witnesses/-/blob/main/user-guide/Witness-Format.md#target)
		if (isTarget && !currentStep.toString().contains("reach_error")) {
			return new Location(filename, line, null, function);
		}
		return new Location(filename, line, column, function);
	}

	public String makeYamlString() {
		final boolean isTerminationWitness = mLoop != null;
		final List<Segment> segments = getSegments(mStem, SegmentType.FOLLOW, !isTerminationWitness);
		if (isTerminationWitness) {
			segments.addAll(getSegments(mLoop, SegmentType.CYCLE, !isTerminationWitness));
		}
		mLogger.info("Generated YAML witness of length %d.", segments.size());
		return mWriter.toString(new Witness(List.of(new ViolationSequence(segments))));
	}
}
