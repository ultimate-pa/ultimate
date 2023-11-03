/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables;

import java.io.Serializable;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Default implementation of {@link IProgramVar}.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public abstract class ProgramVar implements IProgramVar, Serializable {

	private static final long serialVersionUID = 103072739646531062L;
	protected final String mIdentifier;
	private final TermVariable mTermVariable;
	private final ApplicationTerm mDefaultConstant;
	private final ApplicationTerm mPrimedConstant;

	public ProgramVar(final String identifier, final TermVariable tv, final ApplicationTerm defaultConstant,
			final ApplicationTerm primedContant) {
		mIdentifier = identifier;
		mTermVariable = tv;
		mDefaultConstant = defaultConstant;
		mPrimedConstant = primedContant;
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public TermVariable getTermVariable() {
		assert mTermVariable != null;
		return mTermVariable;
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public ApplicationTerm getDefaultConstant() {
		return mDefaultConstant;
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public ApplicationTerm getPrimedConstant() {
		return mPrimedConstant;
	}

	@Override
	/**
	 * {@inheritDoc}
	 */
	public Term getTerm() {
		return mTermVariable;
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public String toString() {
		return getGloballyUniqueId();
	}

	/**
	 * {@inheritDoc}
	 */

	@Override
	public Sort getSort() {
		return getTerm().getSort();
	}

}
