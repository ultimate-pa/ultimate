/*
 * Copyright (C) 2012-2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Model Checker Utils Library.
 *
 * The ULTIMATE Model Checker Utils Library is free software: you can 
 * redistribute it and/or modify it under the terms of the GNU Lesser General 
 * Public License as published by the Free Software Foundation, either 
 * version 3 of the License, or (at your option) any later version.
 *
 * The ULTIMATE Model Checker Utils Library is distributed in the hope that it
 * will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty 
 * of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Model Checker Utils Library. If not,
 * see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Model Checker Utils Library, or any covered work, 
 * by linking or combining it with Eclipse RCP (or a modified version of
 * Eclipse RCP), containing parts covered by the terms of the Eclipse Public
 * License, the licensors of the ULTIMATE Model Checker Utils Library grant you
 * additional permission to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.debug;

import java.io.PrintWriter;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;

public final class DeclarationAdder extends TermTransformer {
	private final Set<FunctionSymbol> mFuncSymbols;
	private final PrintWriter mWriter;

	public DeclarationAdder(final PrintWriter pw) {
		super();
		mWriter = pw;
		mFuncSymbols = new HashSet<>();
	}

	@Override
	protected void convert(Term term) {
		if (term instanceof ApplicationTerm) {
			final FunctionSymbol symbol = ((ApplicationTerm) term).getFunction();

			if (!symbol.isIntern() && mFuncSymbols.add(symbol)) {
				mWriter.append("(declare-fun ").append(symbol.getName()).append(" () ")
						.append(symbol.getReturnSort().toString()).append(")").println();
			}
		}
		super.convert(term);
	}
}