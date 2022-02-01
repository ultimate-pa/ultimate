/*
 * Copyright (C) 2016 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2016 Mostafa M.A. (mostafa.amin93@gmail.com)
 * Copyright (C) 2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.chc;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Sort;

/**
 * Represents an uninterpreted predicate symbol that appears in a set of Horn clauses.
 *
 * @author nutz, mostafa-mahmoud
 *
 */
public class HcPredicateSymbol {

	private final FunctionSymbol mFunctionSymbol;
	private final String mFunctionName;
	private final List<Sort> mParameterSorts;

	/**
	 * Create this only via {@link HcSymbolTable}!
	 *
	 * @param symbolTable
	 * @param fsym  -- must be from solver (not parser) theory!
	 * @param functionParameters
	 */
	HcPredicateSymbol(final HcSymbolTable symbolTable, final FunctionSymbol fsym) {
		mFunctionSymbol = fsym;
		if (fsym == null) {
			assert this instanceof HornClauseDontCarePredicateSymbol;
			mFunctionName = getName();
			mParameterSorts = null;
		} else {
			mFunctionName = fsym.getName();
			mParameterSorts = Arrays.asList(fsym.getParameterSorts());
		}
	}

	public FunctionSymbol getFunctionSymbol() {
		return mFunctionSymbol;
	}

	public String getName() {
		return mFunctionName;
	}

	public int getArity() {
		return mParameterSorts.size();
	}

	public List<Sort> getParameterSorts() {
		return mParameterSorts;
	}

	@Override
	public String toString() {
		return mFunctionName;
	}

	public abstract static class HornClauseConstantPredicateSymbol extends HcPredicateSymbol {

		HornClauseConstantPredicateSymbol(final HcSymbolTable symbolTable, final FunctionSymbol fsym,
				final List<Sort> functionParameters) {
			super(symbolTable, fsym);
		}

	}

	public static class HornClauseFalsePredicateSymbol extends HornClauseConstantPredicateSymbol {
		public HornClauseFalsePredicateSymbol(final FunctionSymbol fsym) {
			super(null, fsym, Collections.emptyList());
		}

		@Override
		public String getName() {
			return "False";
		}

		@Override
		public int getArity() {
			return 0;
		}

		@Override
		public String toString() {
			return getName();
		}
	}

	public static class HornClauseTruePredicateSymbol extends HornClauseConstantPredicateSymbol {
		public HornClauseTruePredicateSymbol(final FunctionSymbol fsym) {
			super(null, fsym, Collections.emptyList());
		}

		@Override
		public String getName() {
			return "True";
		}

		@Override
		public int getArity() {
			return 0;
		}

		@Override
		public String toString() {
			return getName();
		}
	}

	public static class HornClauseDontCarePredicateSymbol extends HornClauseConstantPredicateSymbol {
		public HornClauseDontCarePredicateSymbol() {
			super(null, null, Collections.emptyList());
		}

		@Override
		public String getName() {
			return "DontCare";
		}

		@Override
		public int getArity() {
			return 0;
		}

		@Override
		public String toString() {
			return getName();
		}
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((mFunctionSymbol == null) ? 0 : mFunctionSymbol.hashCode());
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final HcPredicateSymbol other = (HcPredicateSymbol) obj;
		if (mFunctionSymbol == null) {
			if (other.mFunctionSymbol != null) {
				return false;
			}
		} else if (!mFunctionSymbol.equals(other.mFunctionSymbol)) {
			return false;
		}
		return true;
	}
}
