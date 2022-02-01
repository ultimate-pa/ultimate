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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie;

import java.io.Serializable;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Variable in a boogie program. The procedure field of global variables is null. Only global variables can be old
 * variables. Two BoogieVars are equivalent if they have the same identifier, same procedure, same old-flag. Equivalence
 * does not depend on the IType. We expect that two equivalent BoogieVars with different ITypes never occur in the same
 * program.
 *
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public abstract class BoogieVar implements IProgramVar, Serializable {

	private static final long serialVersionUID = 103072739646531062L;
	protected final String mIdentifier;

	/**
	 * TermVariable which represents this BoogieVar in SMT terms.
	 */
	private final TermVariable mTermVariable;

	/**
	 * Constant (0-ary ApplicationTerm) which represents this BoogieVar in closed SMT terms.
	 */
	private final ApplicationTerm mDefaultConstant;

	/**
	 * Constant (0-ary ApplicationTerm) which represents this BoogieVar if it occurs as next state variable in closed
	 * SMT which describe a transition.
	 */
	private final ApplicationTerm mPrimedConstant;

	public BoogieVar(final String identifier, final TermVariable tv, final ApplicationTerm defaultConstant,
			final ApplicationTerm primedContant) {
		mIdentifier = identifier;
		mTermVariable = tv;
		mDefaultConstant = defaultConstant;
		mPrimedConstant = primedContant;
	}

	@Override
	public TermVariable getTermVariable() {
		assert mTermVariable != null;
		return mTermVariable;
	}

	@Override
	public ApplicationTerm getDefaultConstant() {
		return mDefaultConstant;
	}

	@Override
	public ApplicationTerm getPrimedConstant() {
		return mPrimedConstant;
	}

	@Override
	public Term getTerm() {
		return mTermVariable;
	}

	@Override
	public String toString() {
		return getGloballyUniqueId();
	}

	@Override
	public Sort getSort() {
		return getTerm().getSort();
	}

}
