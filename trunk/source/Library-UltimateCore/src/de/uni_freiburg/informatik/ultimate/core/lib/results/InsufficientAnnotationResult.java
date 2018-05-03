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

import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.IBacktranslationService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution.ProgramState;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;

/**
 * Result that tells us that an annotation of a program with loop invariants and
 * procedure specifications is not inductive.
 * This result takes two locations and tells us that it is not true that their 
 * annotation is inductive for all loop-free paths between these locations. 
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <ELEM>
 *            Type of position
 * @param <E>
 *            Type of expression
 */
public class InsufficientAnnotationResult<ELEM extends IElement, E>
		extends AbstractResultAtElement<ELEM> {

	final ILocation mLocationBefore;
	final ILocation mLocationAfter;
	final ProgramState<E> mStateBefore;
	final ProgramState<E> mStateAfter;

	/**
	 * Constructs a {@link InsufficientAnnotationResult}.
	 *
	 * @param positionBefore
	 *            Location of pre annotation
	 * @param positionAfter
	 *            Location of post annotation
	 * @param plugin
	 *            Which plugin (PluginId) found the error location=
	 * @param translatorSequence
	 *            The current backtranslator service (obtained from {@link IUltimateServiceProvider}).
	 */
	public InsufficientAnnotationResult(final ELEM positionBefore, final String plugin,
			final IBacktranslationService translatorSequence, final ELEM positionAfter,
			final ProgramState<E> stateBefore, final ProgramState<E> stateAfter) {
		super(positionBefore, plugin, translatorSequence);
		mLocationBefore = ILocation.getAnnotation(positionBefore);
		mLocationAfter = ILocation.getAnnotation(positionAfter);
		if (mLocationBefore == null) {
			throw new UnsupportedOperationException("position does not have a location");
		}
		if (mLocationAfter == null) {
			throw new UnsupportedOperationException("position does not have a location");
		}
		mStateBefore = stateBefore;
		mStateAfter = stateAfter;
	}

	@Override
	public String getShortDescription() {
		return "Annotation between " + mLocationBefore.getStartLine() + " and " + mLocationAfter.getStartLine()
				+ " is not inductive";
	}

	@Override
	public String getLongDescription() {
		final StringBuilder sb = new StringBuilder();
		sb.append(getShortDescription());
		sb.append(CoreUtil.getPlatformLineSeparator());
		sb.append("Counterexample state before: ");
		sb.append(mTranslatorSequence.translateProgramState(mStateBefore));
		sb.append(CoreUtil.getPlatformLineSeparator());
		sb.append("Counterexample state after: ");
		sb.append(mTranslatorSequence.translateProgramState(mStateAfter));
		return sb.toString();
	}

}
