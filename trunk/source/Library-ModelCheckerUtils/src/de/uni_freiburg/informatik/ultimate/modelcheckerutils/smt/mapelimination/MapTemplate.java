/*
 * Copyright (C) 2016 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE LassoRanker Library.
 *
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE LassoRanker Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.mapelimination;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayIndex;

/**
 * This class is a common interface for the different types of maps (arrays and uninterpreted functions)
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public abstract class MapTemplate {
	/**
	 * Returns the term to of the map of the given arguments
	 */
	public abstract Term getTerm(final ArrayIndex arguments);

	/**
	 * Returns the identifier of the map (the array or function-name)
	 */
	public abstract Object getIdentifier();

	@Override
	public abstract String toString();

	@Override
	public boolean equals(final Object other) {
		if (other instanceof MapTemplate) {
			return getIdentifier().equals(((MapTemplate) (other)).getIdentifier());
		}
		return false;
	}

	@Override
	public int hashCode() {
		return getIdentifier().hashCode();
	}
}

/**
 * This class represents an array as a map as defined in {@link MapTemplate}
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
class ArrayTemplate extends MapTemplate {
	private final Term mArray;
	private final Script mScript;

	public ArrayTemplate(final Term array, final Script script) {
		mArray = array;
		mScript = script;
	}

	@Override
	public Term getTerm(final ArrayIndex arguments) {
		return SmtUtils.multiDimensionalSelect(mScript, mArray, arguments);
	}

	@Override
	public Object getIdentifier() {
		return mArray;
	}

	@Override
	public String toString() {
		return "(select " + mArray + " ...)";
	}
}

/**
 * This class represents an uninterpreted function as a map as defined in {@link MapTemplate}
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
class UFTemplate extends MapTemplate {
	private final String mFunctionName;
	private final Script mScript;

	public UFTemplate(final String functionName, final Script script) {
		mFunctionName = functionName;
		mScript = script;
	}

	@Override
	public Term getTerm(final ArrayIndex arguments) {
		final Term[] params = arguments.toArray(new Term[arguments.size()]);
		return mScript.term(mFunctionName, params);
	}

	@Override
	public Object getIdentifier() {
		return mFunctionName;
	}

	@Override
	public String toString() {
		return "(" + mFunctionName + " ...)";
	}
}
