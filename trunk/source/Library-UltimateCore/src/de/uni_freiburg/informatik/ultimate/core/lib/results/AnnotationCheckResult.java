/*
 * Copyright (C) 2018 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
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

import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResultWithSeverity;
import de.uni_freiburg.informatik.ultimate.core.model.services.IBacktranslationService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution.ProgramState;

/**
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <ELEM>
 *            Type of position
 * @param <EXPR>
 *            Type of expression
 */
public class AnnotationCheckResult<ELEM extends IElement, EXPR> extends AbstractResult implements IResultWithSeverity {

	public enum AnnotationState {
		VALID, UNKNOWN, INVALID
	}

	final IBacktranslationService mTranslatorSequence;

	private final List<LoopFreeSegment<ELEM>> mSegmentsValid;
	private final List<LoopFreeSegment<ELEM>> mSegmentsUnknown;
	private final List<LoopFreeSegmentWithStatePair<ELEM, EXPR>> mSegmentsInvalid;

	private final AnnotationState mAnnotationState;

	/**
	 * @param plugin
	 *            Which plugin (PluginId) found the error location=
	 * @param translatorSequence
	 *            The current backtranslator service (obtained from {@link IUltimateServiceProvider}).
	 */
	public AnnotationCheckResult(final String plugin, final IBacktranslationService translatorSequence,
			final List<LoopFreeSegment<ELEM>> segmentsValid, final List<LoopFreeSegment<ELEM>> segmentsUnknown,
			final List<LoopFreeSegmentWithStatePair<ELEM, EXPR>> segmentsInvalid) {
		super(plugin);
		mTranslatorSequence = translatorSequence;
		mSegmentsValid = segmentsValid;
		mSegmentsUnknown = segmentsUnknown;
		mSegmentsInvalid = segmentsInvalid;
		mAnnotationState = determineAnnotationState(segmentsValid, segmentsUnknown, segmentsInvalid);
	}

	private AnnotationState determineAnnotationState(final List<LoopFreeSegment<ELEM>> segmentsValid,
			final List<LoopFreeSegment<ELEM>> segmentsUnknown,
			final List<LoopFreeSegmentWithStatePair<ELEM, EXPR>> segmentsInvalid) {
		final AnnotationState result;
		if (segmentsInvalid.isEmpty()) {
			if (segmentsUnknown.isEmpty()) {
				result = AnnotationState.VALID;
			} else {
				result = AnnotationState.UNKNOWN;
			}
		} else {
			result = AnnotationState.INVALID;
		}
		return result;
	}

	@Override
	public Severity getSeverity() {
		switch (mAnnotationState) {
		case VALID:
			return Severity.INFO;
		case INVALID:
		case UNKNOWN:
			return Severity.ERROR;
		default:
			throw new AssertionError("Unknown value " + mAnnotationState);
		}
	}

	@Override
	public String getShortDescription() {
		String result;
		switch (mAnnotationState) {
		case INVALID:
			result = "Annotation is not a valid proof of correctness.";
			break;
		case UNKNOWN:
			result = "Insufficient resources for checking whether annotation is a valid proof of correctness";
			break;
		case VALID:
			result = "Annotation is a valid proof of correctness";
			break;
		default:
			throw new AssertionError("illegal value " + mAnnotationState);
		}
		return result;
	}

	@Override
	public String getLongDescription() {
		final StringBuilder sb = new StringBuilder();
		sb.append(getShortDescription());
		sb.append(System.lineSeparator());
		for (final LoopFreeSegmentWithStatePair<ELEM, EXPR> segment : mSegmentsInvalid) {
			sb.append(invalidSegmentToString(segment, mTranslatorSequence));
			sb.append(System.lineSeparator());
		}
		for (final LoopFreeSegment<ELEM> segment : mSegmentsUnknown) {
			sb.append(unknownSegmentToString(segment));
			sb.append(System.lineSeparator());
		}
		for (final LoopFreeSegment<ELEM> segment : mSegmentsValid) {
			sb.append(validSegmentToString(segment));
			sb.append(System.lineSeparator());
		}
		return sb.toString();
	}

	public static <E> String validSegmentToString(final LoopFreeSegment<E> segment) {
		return "Annotation is valid for " + segment + ".";
	}

	public static <E> String unknownSegmentToString(final LoopFreeSegment<E> segment) {
		return "Insufficient resources for checking whether annotation is valid for " + segment + ".";
	}

	public static <ELEM, E> String invalidSegmentToString(final LoopFreeSegmentWithStatePair<ELEM, E> segment,
			final IBacktranslationService translation) {
		return "Annotation is not valid for " + segment + ". One counterxample starts in "
				+ translation.translateProgramStateToString(segment.getStateBefore()) + " and ends in "
				+ translation.translateProgramStateToString(segment.getStateAfter()) + ".";
	}

	public static class LoopFreeSegment<E> {
		final CategorizedProgramPoint mCppBefore;
		final CategorizedProgramPoint mCppAfter;

		public LoopFreeSegment(final CategorizedProgramPoint cppBefore, final CategorizedProgramPoint cppAfter) {
			super();
			this.mCppBefore = cppBefore;
			this.mCppAfter = cppAfter;
		}

		@Override
		public String toString() {
			return "all loop-free paths from " + mCppBefore + " to " + mCppAfter;
		}
	}

	public static class LoopFreeSegmentWithStatePair<ELEM, E> extends LoopFreeSegment<ELEM> {
		final ProgramState<E> mStateBefore;
		final ProgramState<E> mStateAfter;

		public LoopFreeSegmentWithStatePair(final CategorizedProgramPoint cppBefore,
				final CategorizedProgramPoint cppAfter, final ProgramState<E> stateBefore,
				final ProgramState<E> stateAfter) {
			super(cppBefore, cppAfter);
			mStateBefore = stateBefore;
			mStateAfter = stateAfter;
		}

		public ProgramState<E> getStateBefore() {
			return mStateBefore;
		}

		public ProgramState<E> getStateAfter() {
			return mStateAfter;
		}
	}

	public static abstract class CategorizedProgramPoint {
		private final ILocation mLocation;

		public CategorizedProgramPoint(final ILocation location) {
			super();
			mLocation = location;
		}

		protected ILocation getLocation() {
			return mLocation;
		}
	}

	public static class LoopHead extends CategorizedProgramPoint {

		public LoopHead(final ILocation location) {
			super(location);
		}

		@Override
		public String toString() {
			return "loop head at line " + getLocation().getStartLine();
		}
	}

	public static class ProcedureEntry extends CategorizedProgramPoint {

		final String mProcedureName;

		public ProcedureEntry(final ILocation location, final String procedureName) {
			super(location);
			mProcedureName = procedureName;
		}

		@Override
		public String toString() {
			return "entry of procedure " + mProcedureName;
		}
	}

	public static class ProcedureExit extends CategorizedProgramPoint {

		final String mProcedureName;

		public ProcedureExit(final ILocation location, final String procedureName) {
			super(location);
			mProcedureName = procedureName;
		}

		@Override
		public String toString() {
			return "exit of procedure " + mProcedureName;
		}
	}

	public static class CheckPoint extends CategorizedProgramPoint {

		final Check mCheck;

		public CheckPoint(final ILocation location, final Check check) {
			super(location);
			mCheck = check;
		}

		@Override
		public String toString() {
			return "check that " + mCheck.getPositiveMessage() + " at line " + getLocation().getStartLine();
		}
	}

}
