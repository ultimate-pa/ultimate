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

import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
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
public class AnnotationCheckResult<ELEM extends IElement, EXPR> extends AbstractResult {

	public enum AnnotationState { VALID, UNKNOWN, INVALID };

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
			final List<LoopFreeSegment<ELEM>> segmentsUnknown, final List<LoopFreeSegmentWithStatePair<ELEM, EXPR>> segmentsInvalid) {
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
	public String getShortDescription() {
		String result;
		switch (mAnnotationState) {
		case INVALID:
			result = "Annotation is not a valid proof of correctness.";
			break;
		case UNKNOWN:
			result = "Unable to check if annotation is a valid proof of correctness";
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
		for (final LoopFreeSegmentWithStatePair<ELEM, EXPR> segment : mSegmentsInvalid) {
			sb.append(validSegmentToString(segment, mTranslatorSequence));
			sb.append(System.lineSeparator());
		}
		for (final LoopFreeSegment<ELEM> segment : mSegmentsUnknown) {
			sb.append(validSegmentToString(segment));
			sb.append(System.lineSeparator());
		}
		for (final LoopFreeSegment<ELEM> segment : mSegmentsValid) {
			sb.append(validSegmentToString(segment));
			sb.append(System.lineSeparator());
		}
		return sb.toString();
	}

	public static <E> String validSegmentToString(final LoopFreeSegment<E> segment) {
		return "Annotation is valid for all loop-free paths from " + segment.before() + " to " + segment.after();
	}

	public static <E> String unknownSegmentToString(final LoopFreeSegment<E> segment) {
		return "Unable to check if annotation is valid for all loop-free paths from " + segment.before() + " to "
				+ segment.after();
	}

	public static <ELEM, E> String validSegmentToString(final LoopFreeSegmentWithStatePair<ELEM, E> segment,
			final IBacktranslationService translation) {
		return "Annotation is not valid for all loop-free paths from " + segment.before() + " to " + segment.after()
				+ ". One counterxample starts in " + translation.translateProgramState(segment.getStateBefore())
				+ " and ends in " + translation.translateProgramState(segment.getStateAfter());
	}

	public static class LoopFreeSegment<E> {
		final ILocation mLocationBefore;
		final ILocation mLocationAfter;
		final String mLocationTypeBefore;
		final String mLocationTypeAfter;

		public LoopFreeSegment(final ILocation locationBefore, final ILocation locationAfter, final String locationTypeBefore,
				final String locationTypeAfter) {
			super();
			mLocationBefore = locationBefore;
			mLocationAfter = locationAfter;
			mLocationTypeBefore = locationTypeBefore;
			mLocationTypeAfter = locationTypeAfter;
		}

		public String before() {
			return mLocationTypeBefore + " at line " + mLocationBefore.getStartLine();
		}

		public String after() {
			return mLocationTypeAfter + " at line " + mLocationBefore.getEndLine();
		}


		public ILocation getLocationBefore() {
			return mLocationBefore;
		}

		public ILocation getLocationAfter() {
			return mLocationAfter;
		}

		public String getLocationTypeBefore() {
			return mLocationTypeBefore;
		}

		public String getLocationTypeAfter() {
			return mLocationTypeAfter;
		}




	}

	public static class LoopFreeSegmentWithStatePair<ELEM, E> extends LoopFreeSegment<ELEM> {
		final ProgramState<E> mStateBefore;
		final ProgramState<E> mStateAfter;
		public LoopFreeSegmentWithStatePair(final ILocation locationBefore, final ILocation locationAfter,
				final String locationTypeBefore, final String locationTypeAfter, final ProgramState<E> stateBefore,
				final ProgramState<E> stateAfter) {
			super(locationBefore, locationAfter, locationTypeBefore, locationTypeAfter);
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


}
