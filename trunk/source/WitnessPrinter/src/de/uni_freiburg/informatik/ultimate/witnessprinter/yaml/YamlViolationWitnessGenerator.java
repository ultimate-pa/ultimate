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
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution.ProgramState;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.Constraint;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.FormatVersion;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.Location;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.Segment;
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
		final List<Segment> content = new ArrayList<>();
		for (int i = 0; i < mExecution.getLength(); i++) {
			final AtomicTraceElement<TE> currentATE = mExecution.getTraceElement(i);
			final TE currentStep = currentATE.getStep();
			final ProgramState<E> currentState = mExecution.getProgramState(i);
			final int startLine = mStringProvider.getStartLineNumberFromStep(currentStep);
			// TODO: change column in Location to startColumn once we can calculate the right column
			final int startColumn = mStringProvider.getStartColumnNumberFromStep(currentStep);
			final String function = mStringProvider.getFunctionFromStep(currentStep);
			final String filename = mStringProvider.getFileNameFromStep(currentStep);
			final Location currentLocation =
					new Location(filename, mProgramHashes.get(filename), startLine, null, function);
			if (haveVariablesChanged(mExecution, i)) {
				final String assumption =
						mProgramStatePrinter.stateAsExpression(currentState, ProgramStatePrinter::isValidCVariable);
				final Constraint constraint = new Constraint(assumption, "c_expression");
				content.add(new Segment(List.of(), new WaypointAssumption(constraint, currentLocation)));
			}
			if (i == mExecution.getLength() - 1) {
				content.add(new Segment(List.of(), new WaypointTarget(currentLocation)));
			}
			if (currentATE.hasStepInfo(StepInfo.CONDITION_EVAL_FALSE)) {
				final Constraint constraint = new Constraint("false", null);
				content.add(new Segment(List.of(), new WaypointBranching(constraint, currentLocation)));
			}
			if (currentATE.hasStepInfo(StepInfo.CONDITION_EVAL_TRUE)) {
				final Constraint constraint = new Constraint("true", null);
				content.add(new Segment(List.of(), new WaypointBranching(constraint, currentLocation)));
			}
			if (currentATE.hasStepInfo(StepInfo.PROC_CALL)) {
				content.add(new Segment(List.of(), new WaypointFunctionEnter(currentLocation)));
			}
			if (currentATE.hasStepInfo(StepInfo.PROC_RETURN)) {
				final Constraint constraint = getReturnConstraint(currentState);
				content.add(new Segment(List.of(), new WaypointFunctionReturn(constraint, currentLocation)));
			}
		}
		mLogger.info("Generated YAML witness of length %d.", content.size());
		return new Witness(List.of(new ViolationSequence(content)));
	}

	private Constraint getReturnConstraint(final ProgramState<E> state) {
		final String result = mProgramStatePrinter.stateAsExpression(state, "\\result"::equals);
		if (result == null) {
			return null;
		}
		// TODO: check if result is an acsl_expression
		return new Constraint(result, "acsl_expression");
	}

	// checks if the values of the variables have changed compared to the previous State
	private Boolean haveVariablesChanged(final IProgramExecution<TE, E> execution, final int i) {
		// besser mit string matching?
		if (i == 0) {
			return false;
		}
		final ProgramState<E> oldState = execution.getProgramState(i - 1);
		final ProgramState<E> newState = execution.getProgramState(i);
		if (oldState == null || newState == null) {
			return false;
		}

		final Set<E> newVariables = newState.getVariables();
		for (final E Var : newVariables) {
			if (newState.getValues(Var) != oldState.getValues(Var)) {
				return true;
			}
		}
		return false;
	}

	public String makeYamlString() {
		return mWriter.toString(getWitness());
	}
}
