/*
 * Copyright (C) 2021 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of the ULTIMATE Core.
 *
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Core grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.core.lib.results;

import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.DataRaceAnnotation;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.DataRaceAnnotation.Race;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResultWithFiniteTrace;
import de.uni_freiburg.informatik.ultimate.core.model.services.IBacktranslationService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * A result that indicates that a data race was found in a concurrent program.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <ELEM>
 *            Type of position
 * @param <TE>
 *            Type of trace element
 * @param <E>
 *            Type of expression
 */
public class DataRaceFoundResult<ELEM extends IElement, TE extends IElement, E> extends AbstractResultAtElement<ELEM>
		implements IResultWithFiniteTrace<TE, E> {

	private final IProgramExecution<TE, E> mProgramExecution;
	private final String mProgramExecutionAsString;
	private final List<ILocation> mFailurePath;

	private final DataRaceAnnotation mRaceAnnotation;
	private final HashRelation<Race, Race> mPossibleConflicts;

	/**
	 * Creates a new instance.
	 *
	 * @param position
	 *            The error location at which the error occurs. This should be a location created by
	 *            {@link DataRaceChecker}.
	 * @param plugin
	 *            The plugin that found the error.
	 * @param translatorSequence
	 *            The current backtranslator service (obtained from {@link IUltimateServiceProvider}).
	 * @param execution
	 *            A program execution leading to this error.
	 */
	public DataRaceFoundResult(final ELEM position, final String plugin,
			final IBacktranslationService translatorSequence, final IProgramExecution<TE, E> execution) {
		super(position, plugin);

		mRaceAnnotation = DataRaceAnnotation.getAnnotation(position);
		assert mRaceAnnotation != null;

		mPossibleConflicts = findPossibleViolations(mRaceAnnotation, execution);
		assert mPossibleConflicts.size() > 0;

		// TODO cleanup execution: remove fragments that are only for race detection (using annotations)
		// TODO cleanup execution: reorder independent parts so that racing accesses next to each other (possible?)
		// TODO cleanup execution: stop before race begins
		mProgramExecution = execution;

		mProgramExecutionAsString = translatorSequence.translateProgramExecution(mProgramExecution).toString();
		mFailurePath = ResultUtil.getLocationSequence(execution);
	}

	private HashRelation<Race, Race> findPossibleViolations(final DataRaceAnnotation annotation,
			final IProgramExecution<TE, E> execution) {
		// TODO see if program states can help rule out more conflicts

		final HashRelation<Race, Race> result = new HashRelation<>();
		for (int i = execution.getLength() - 2; i >= 0; i--) {
			final DataRaceAnnotation current = DataRaceAnnotation.getAnnotation(execution.getTraceElement(i).getStep());
			if (current == null) {
				continue;
			}
			for (final Race race : annotation.getRaces()) {
				for (final Race other : current.getRaces()) {
					final Optional<Boolean> conflict = race.isConflictingAccess(other);
					if (conflict.orElse(false)) {
						final HashRelation<Race, Race> definite = new HashRelation<>();
						definite.addPair(race, other);
						return definite;
					}
					if (conflict.isEmpty()) {
						result.addPair(race, other);
					}
				}
			}
		}
		return result;
	}

	@Override
	public String getShortDescription() {
		return "Data race detected";
	}

	@Override
	public String getLongDescription() {
		final StringBuilder sb = new StringBuilder();
		sb.append(getShortDescription());
		sb.append(CoreUtil.getPlatformLineSeparator());
		sb.append("The following path leads to a data race: ");
		sb.append(CoreUtil.getPlatformLineSeparator());
		sb.append(mProgramExecutionAsString);
		sb.append(CoreUtil.getPlatformLineSeparator());

		if (mPossibleConflicts.size() == 1) {
			final Map.Entry<Race, Race> definite = mPossibleConflicts.getSetOfPairs().iterator().next();
			formatDefiniteRace(sb, definite.getKey(), definite.getValue());
		} else {
			sb.append("Now there is a data race, but we were unable to determine exactly"
					+ " which statements and variables are involved.");
			for (final Map.Entry<Race, HashSet<Race>> entry : mPossibleConflicts.entrySet()) {
				formatPossibleRace(sb, entry.getKey(), entry.getValue());
			}
		}
		return sb.toString();
	}

	private static void formatDefiniteRace(final StringBuilder sb, final Race check, final Race access) {
		sb.append("Now there is a data race ");
		if (check.isUndeterminedRace()) {
			sb.append("(on the heap)");
		} else {
			sb.append("on ");
			sb.append(access.getVariable());
		}
		sb.append(" between ");
		sb.append(CoreUtil.getPlatformLineSeparator());
		sb.append("\t");
		sb.append(access.getOriginalLocation());
		sb.append(CoreUtil.getPlatformLineSeparator());
		sb.append("and");
		sb.append(CoreUtil.getPlatformLineSeparator());
		sb.append("\t");
		sb.append(check.getOriginalLocation());
		sb.append(CoreUtil.getPlatformLineSeparator());
	}

	private static void formatPossibleRace(final StringBuilder sb, final Race check, final Set<Race> accesses) {
		assert !accesses.isEmpty();
		sb.append(" There could be a race between");
		if (accesses.size() == 1) {
			sb.append(CoreUtil.getPlatformLineSeparator());
			sb.append("\t");
			sb.append(accesses.iterator().next().getOriginalLocation());
			sb.append(CoreUtil.getPlatformLineSeparator());
		} else {
			sb.append(" one of the statements");
			sb.append(CoreUtil.getPlatformLineSeparator());
			for (final Race access : accesses) {
				sb.append("\t* ");
				sb.append(access.getOriginalLocation());
				sb.append(CoreUtil.getPlatformLineSeparator());
			}
		}
		sb.append("and");
		sb.append(CoreUtil.getPlatformLineSeparator());
		sb.append("\t");
		sb.append(check.getOriginalLocation());
		sb.append(CoreUtil.getPlatformLineSeparator());
	}

	@Override
	public List<ILocation> getFailurePath() {
		return mFailurePath;
	}

	@Override
	public IProgramExecution<TE, E> getProgramExecution() {
		return mProgramExecution;
	}
}
