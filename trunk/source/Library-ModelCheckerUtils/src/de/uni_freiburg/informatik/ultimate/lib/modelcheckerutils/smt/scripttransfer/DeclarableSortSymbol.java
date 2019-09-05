/*
 * Copyright (C) 2019 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer;

import java.util.Arrays;
import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.logic.PrintTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;

public class DeclarableSortSymbol implements ISmtDeclarable {

	private final String mName;
	private final int mArity;
	private final Sort[] mParams;
	private final Sort mDefinition;

	private DeclarableSortSymbol(final String name, final Sort[] params, final Sort definition, final int arity) {
		mName = Objects.requireNonNull(name);
		mParams = params;
		mDefinition = definition;
		mArity = arity;
		assert mParams == null || mParams.length == arity;
		assert params == null || Arrays.stream(params).allMatch(a -> a != null);
	}

	public static DeclarableSortSymbol createFromScriptDefineSort(final String sort, final Sort[] sortParams,
			final Sort definition) {
		return new DeclarableSortSymbol(sort, sortParams, definition, sortParams == null ? 0 : sortParams.length);
	}

	public static ISmtDeclarable createFromScriptDeclareSort(final String sort, final int arity) {
		return new DeclarableSortSymbol(sort, null, null, arity);
	}

	@Override
	public void defineOrDeclare(final Script script) {
		final NonDeclaringTermTransferrer ndtt = new NonDeclaringTermTransferrer(script);
		if (mDefinition == null && mParams == null) {
			script.declareSort(mName, mArity);
			return;
		}

		final Sort[] newParams;
		if (mParams == null) {
			newParams = null;
		} else {
			newParams = ndtt.transferSorts(mParams);
		}
		final Sort newDef;
		if (mDefinition == null) {
			newDef = null;
		} else {
			newDef = ndtt.transferSort(mDefinition);
		}
		script.defineSort(mName, newParams, newDef);
	}

	@Override
	public String getName() {
		return mName;
	}

	@Override
	public String toString() {
		return "(" + PrintTerm.quoteIdentifier(mName) + " " + mArity + ")";
	}

}
