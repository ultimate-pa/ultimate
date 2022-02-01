/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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

import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResultWithInfiniteLassoTrace;
import de.uni_freiburg.informatik.ultimate.core.model.services.IBacktranslationService;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;

/**
 * Result that reports that a nonterminating execution for a lasso shaped
 * sequence of statements has been found.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class NonterminatingLassoResult<ELEM extends IElement, TE extends IElement, EXP> extends
		AbstractResultAtElement<ELEM> implements IResultWithInfiniteLassoTrace<TE, EXP> {

	protected final IProgramExecution<TE, EXP> mStem;
	protected final IProgramExecution<TE, EXP> mLoop;

	public NonterminatingLassoResult(final ELEM position, final String plugin, final IBacktranslationService translatorSequence,
			final IProgramExecution<TE, EXP> stem, final IProgramExecution<TE, EXP> loop, final ILocation location) {
		super(position, plugin, translatorSequence);
		mStem = stem;
		mLoop = loop;
	}

	@Override
	public String getShortDescription() {
		return "Nonterminating execution";
	}

	@Override
	public String getLongDescription() {
		final StringBuilder sb = new StringBuilder();
		sb.append("Found a nonterminating execution for the following lasso shaped sequence of statements.");
		sb.append(System.getProperty("line.separator"));
		sb.append("Stem:");
		sb.append(System.getProperty("line.separator"));
		sb.append(mTranslatorSequence.translateProgramExecution(mStem));
		sb.append("Loop:");
		sb.append(System.getProperty("line.separator"));
		sb.append(mTranslatorSequence.translateProgramExecution(mLoop));
		sb.append("End of lasso representation.");
		return sb.toString();
	}

	@Override
	public IProgramExecution<TE, EXP> getStem() {
		return mStem;
	}

	@Override
	public IProgramExecution<TE, EXP> getLasso() {
		return mLoop;
	}
}
