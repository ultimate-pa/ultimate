/*
 * Copyright (C) 2009-2012 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;

public class SymbolChecker extends TermTransformer {

	private Map<FunctionSymbol, Integer> mLeftAllowed;
	private Map<FunctionSymbol, Integer> mRightAllowed;
	private HashSet<FunctionSymbol> mLeftErrors;
	private HashSet<FunctionSymbol> mRightErrors;
	private final Set<FunctionSymbol> mGlobals;

	public SymbolChecker(Set<FunctionSymbol> globals) {
		mGlobals = globals;
	}

	/**
	 * Check whether an interpolant contains only allowed symbols.
	 * 
	 * @param interpolant
	 *            The interpolant.
	 * @param leftAllowed
	 *            The symbols allowed from the left-hand side.
	 * @param rightAllowed
	 *            The symbols allowed from the right-hand side.
	 * @return <code>true</code> if an error has been detected.
	 */
	public final boolean check(Term interpolant, Map<FunctionSymbol, Integer> leftAllowed,
			Map<FunctionSymbol, Integer> rightAllowed) {
		mLeftAllowed = leftAllowed;
		mRightAllowed = rightAllowed;
		mLeftErrors = new HashSet<FunctionSymbol>();
		mRightErrors = new HashSet<FunctionSymbol>();
		transform(interpolant);
		return !(mLeftErrors.isEmpty() && mRightErrors.isEmpty());
	}

	@Override
	public void convert(Term term) {
		if (term instanceof AnnotatedTerm) {
			throw new SMTLIBException("Interpolant contains annotated term: " + term);
		}
		super.convert(term);
	}

	@Override
	public void convertApplicationTerm(ApplicationTerm appTerm, Term[] newArgs) {
		final FunctionSymbol fs = appTerm.getFunction();
		if (!fs.isIntern() && !mGlobals.contains(fs)) {
			final Integer left = mLeftAllowed.get(fs);
			final Integer right = mRightAllowed.get(fs);
			if (left == null && right == null) {
				throw new InternalError("Detected new symbol in interpolant: " + fs);
			} else if (left == null) {
				mRightErrors.add(fs);
			} else if (right - left <= 0) {
				mLeftErrors.add(fs);
			}
		}
		super.convertApplicationTerm(appTerm, newArgs);
	}

	public Set<FunctionSymbol> getLeftErrors() {
		return mLeftErrors;
	}

	public Set<FunctionSymbol> getRightErrors() {
		return mRightErrors;
	}

}
