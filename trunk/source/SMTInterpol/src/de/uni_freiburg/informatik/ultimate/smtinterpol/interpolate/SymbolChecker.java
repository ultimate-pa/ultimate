/*
 * Copyright (C) 2009-2019 University of Freiburg
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

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * This is a symbol checker specialized to check symbol condition in interpolants.
 *
 * @author Christ, Hoenicke
 */
public class SymbolChecker {

	private Map<FunctionSymbol, Integer> mSubtreeOccurrences;
	private final Map<FunctionSymbol, Integer> mAllOccurences;
	private HashSet<FunctionSymbol> mALocal;
	private HashSet<FunctionSymbol> mBLocal;
	private final Set<FunctionSymbol> mGlobals;
	private final SymbolCollector mCollector = new SymbolCollector();

	/**
	 * Create a new checker for symbol occurrences in interpolants.
	 *
	 * @param globals
	 *            The symbols that occur in the background theory.
	 * @param occurrences
	 *            A map from each symbol to the number of partitions where the symbol occurs.
	 */
	public SymbolChecker(final Set<FunctionSymbol> globals, final Map<FunctionSymbol, Integer> allOccurrences) {
		mGlobals = globals;
		mAllOccurences = allOccurrences;
	}

	/**
	 * Check whether an interpolant contains only allowed symbols.
	 *
	 * @param interpolant
	 *            The interpolant.
	 * @param subtreeOccurrences
	 *            This maps for each symbol the number of partitions in the subtree (A-part) where the symbol occurs.
	 * @return {@code true} if an A local or B local symbol was found in the interpolant.
	 */
	public final boolean check(final Term interpolant, final Map<FunctionSymbol, Integer> subtreeOccurrences) {
		mSubtreeOccurrences = subtreeOccurrences;
		mALocal = new HashSet<FunctionSymbol>();
		mBLocal = new HashSet<FunctionSymbol>();
		mCollector.collect(interpolant);
		for (final FunctionSymbol fsym : mCollector.getSymbols()) {
			if (!mGlobals.contains(fsym)) {
				final Integer inA = mSubtreeOccurrences.get(fsym);
				final Integer inAll = mAllOccurences.get(fsym);
				if (inAll == null) {
					throw new InternalError("Detected new symbol in interpolant: " + fsym);
				} else if (inA == null) {
					// symbol doesn't occur in the A part
					mBLocal.add(fsym);
				} else if (inAll - inA <= 0) {
					// symbol doesn't occur in the B part
					mALocal.add(fsym);
				}
			}
		}
		mSubtreeOccurrences = null;
		return !(mALocal.isEmpty() && mBLocal.isEmpty());
	}

	/**
	 * Get all symbols from the interpolant that are A-local. If this is non-empty it indicates an error.
	 *
	 * @return The A-local symbols.
	 */
	public Set<FunctionSymbol> getALocals() {
		return mALocal;
	}

	/**
	 * Get all symbols from the interpolant that are B-local. If this is non-empty it indicates an error.
	 *
	 * @return The B-local symbols.
	 */
	public Set<FunctionSymbol> getBLocals() {
		return mBLocal;
	}
}
