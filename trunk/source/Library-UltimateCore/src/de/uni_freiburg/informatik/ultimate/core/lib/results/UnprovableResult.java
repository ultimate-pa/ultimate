/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Oleksii Saukh (saukho@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Stefan Wissert
 * Copyright (C) 2015 University of Freiburg
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

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check.Spec;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResultWithFiniteTrace;
import de.uni_freiburg.informatik.ultimate.core.model.services.IBacktranslationService;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;

/**
 * Result to store that we are not able to determine if a specification given at
 * some location holds. We also provide a potential counterexample for which one
 * of the following holds.
 * <ul>
 * <li>We are not able to determine feasibility of the counterexample. (e.g.,
 * multiplication of variables and LIRA logic, timeout of solver,..)
 * <li>We are not able to exclude the counterexample in the refined abstraction.
 * (e.g., predicate abstraction with fixed set of predicates)
 * </ul>
 * If the fail of a model checker is not related to one specific counterexample
 * we use the timeout result.
 * 
 * @author Markus Lindenmann
 * @author Stefan Wissert
 * @author Oleksii Saukh
 * @author Matthias Heizmann
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * 
 * @param <ELEM>
 *            Type of position
 * @param <TE>
 *            Type of trace element
 * @param <E>
 *            Type of expression
 */
public class UnprovableResult<ELEM extends IElement, TE extends IElement, E> extends AbstractResultAtElement<ELEM>
		implements IResultWithFiniteTrace<TE, E> {

	private final Check mCheckedSpecification;
	private final IProgramExecution<TE, E> mProgramExecution;
	private final List<ILocation> mFailurePath;
	private final List<UnprovabilityReason> mUnprovabilityReasons;
	private String mProgramExecutionAsString;

	public UnprovableResult(final String plugin, final ELEM position, final IBacktranslationService translatorSequence,
			final IProgramExecution<TE, E> programExecution) {
		this(plugin, position, translatorSequence, programExecution, new ArrayList<UnprovabilityReason>());
	}

	public UnprovableResult(final String plugin, final ELEM position, final IBacktranslationService translatorSequence,
			final IProgramExecution<TE, E> programExecution, final String unprovabilityReason) {
		this(plugin, position, translatorSequence, programExecution,
				Collections.singletonList(new UnprovabilityReason(unprovabilityReason)));
	}

	public UnprovableResult(final String plugin, final ELEM position, final IBacktranslationService translatorSequence,
			final IProgramExecution<TE, E> programExecution, final List<UnprovabilityReason> unprovabilityReasons) {
		super(position, plugin, translatorSequence);
		assert unprovabilityReasons != null;
		assert programExecution != null;
		final Check check = ResultUtil.getCheckedSpecification(position);
		if (check == null) {
			mCheckedSpecification = new Check(Spec.UNKNOWN);
		} else {
			mCheckedSpecification = check;
		}
		mProgramExecution = programExecution;
		mFailurePath = ResultUtil.getLocationSequence(programExecution);
		mUnprovabilityReasons = unprovabilityReasons;
	}

	public Check getCheckedSpecification() {
		return mCheckedSpecification;
	}

	@Override
	public String getShortDescription() {
		return "Unable to prove that " + mCheckedSpecification.getPositiveMessage();
	}

	@Override
	public String getLongDescription() {
		final StringBuilder sb = new StringBuilder();
		sb.append(getShortDescription());
		sb.append(CoreUtil.getPlatformLineSeparator());
		sb.append(getReasons());
		sb.append(CoreUtil.getPlatformLineSeparator());
		sb.append("Possible FailurePath: ");
		sb.append(CoreUtil.getPlatformLineSeparator());
		sb.append(getProgramExecutionAsString());
		return sb.toString();
	}

	public String getProgramExecutionAsString() {
		if (mProgramExecutionAsString == null) {
			mProgramExecutionAsString = mTranslatorSequence.translateProgramExecution(mProgramExecution).toString();
		}
		return mProgramExecutionAsString;
	}

	/**
	 * Getter for the failure path.
	 * 
	 * @return the failurePath
	 */
	@Override
	public List<ILocation> getFailurePath() {
		return mFailurePath;
	}

	@Override
	public IProgramExecution<TE, E> getProgramExecution() {
		return mProgramExecution;
	}

	/**
	 * @return a description of the reasons for unprovability.
	 */
	public String getReasons() {
		final StringBuilder sb = new StringBuilder();
		sb.append(" Reason: ");
		for (int i = 0; i < mUnprovabilityReasons.size(); i++) {
			sb.append(mUnprovabilityReasons.get(i));
			if (i == mUnprovabilityReasons.size() - 1) {
				sb.append(". ");
			} else {
				sb.append(", ");
			}
		}
		return sb.toString();
	}
}
