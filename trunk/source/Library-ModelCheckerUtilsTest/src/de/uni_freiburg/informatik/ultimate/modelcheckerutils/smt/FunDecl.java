/*
 * Copyright (C) 2020 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtilsTest Library.
 *
 * The ULTIMATE ModelCheckerUtilsTest Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtilsTest Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtilsTest Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtilsTest Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtilsTest Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt;

import java.util.Arrays;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;

/**
 * Objects of this class provide all information of declaring a list of
 * functions that have the same sort.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class FunDecl {
	private final SortConstructor[] mParamSorts;
	private final SortConstructor mReturnSort;
	private final String[] mIdentifiers;

	public FunDecl(final SortConstructor[] paramSorts, final SortConstructor returnSort, final String... identifiers) {
		super();
		mParamSorts = paramSorts;
		mReturnSort = returnSort;
		mIdentifiers = identifiers;
	}

	public FunDecl(final SortConstructor returnSort, final String... identifiers) {
		super();
		mParamSorts = new SortConstructor[0];
		mReturnSort = returnSort;
		mIdentifiers = identifiers;
	}

	public void declareFuns(final Script script) {
		final Sort[] paramSorts = Arrays.stream(mParamSorts).map(x -> x.constructSort(script)).toArray(Sort[]::new);
		final Sort sort = mReturnSort.constructSort(script);
		for (final String identifier : mIdentifiers) {
			script.declareFun(identifier, paramSorts, sort);
		}
	}

	@FunctionalInterface
	public interface SortConstructor {
		public Sort constructSort(Script script);
	}
}
