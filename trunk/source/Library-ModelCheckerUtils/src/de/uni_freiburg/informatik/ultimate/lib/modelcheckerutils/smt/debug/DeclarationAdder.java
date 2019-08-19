/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.debug;

import java.io.PrintWriter;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * {@link DeclarationAdder} is a {@link TermTransformer} that adds the
 * declarations of a term as <code>(declare-fun ...)</code> to a
 * {@link PrintWriter}. Each declaration gets its own line.
 * 
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public final class DeclarationAdder extends TermTransformer {
	private final Set<FunctionSymbol> mFuncSymbols;
	private final Set<TermVariable> mTermSymbols;
	private final PrintWriter mWriter;

	/**
	 * Construct a {@link DeclarationAdder}.
	 * 
	 * @param pw
	 *            The print writer to which the declarations are appended. The
	 *            writer has to be initialized. We do not close the writer.
	 */
	public DeclarationAdder(final PrintWriter pw) {
		super();
		mWriter = pw;
		mFuncSymbols = new HashSet<>();
		mTermSymbols = new HashSet<>();
	}

	@Override
	protected void convert(Term term) {
		if (term instanceof ApplicationTerm) {
			final FunctionSymbol symbol = ((ApplicationTerm) term).getFunction();

			if (!symbol.isIntern() && mFuncSymbols.add(symbol)) {
				mWriter.append("(declare-fun ").append(symbol.getName()).append(" () ")
						.append(symbol.getReturnSort().toString()).append(")").println();
			}
		} else if (term instanceof TermVariable) {
			final TermVariable termVar = (TermVariable) term;
			if (mTermSymbols.add(termVar)) {
				mWriter.append("(declare-fun ").append(termVar.getName()).append(" () ")
						.append(termVar.getSort().toString()).append(")").println();
			}
		}
		super.convert(term);
	}
}
