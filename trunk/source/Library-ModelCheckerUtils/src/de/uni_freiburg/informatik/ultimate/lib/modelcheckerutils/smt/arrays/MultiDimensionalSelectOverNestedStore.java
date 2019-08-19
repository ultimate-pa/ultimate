/*
 * Copyright (C) 2019 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.ApplicationTermFinder;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class MultiDimensionalSelectOverNestedStore {

	private final MultiDimensionalSelect mSelect;
	private final MultiDimensionalNestedStore mNestedStore;
	private final Term mTerm;

	public MultiDimensionalSelectOverNestedStore(final Script script, final Term term) {
		final MultiDimensionalSelect select = new MultiDimensionalSelect(term);
		if (!select.getIndex().isEmpty()) {
			final Term innerArray = select.getArray();
			if (innerArray instanceof ApplicationTerm) {
				final MultiDimensionalNestedStore store = MultiDimensionalNestedStore.convert(script, innerArray);
				if (store != null && store.getIndices().get(0).size() == select.getIndex().size()) {
					mSelect = select;
					mNestedStore = store;
					mTerm = term;
					return;
				}
			}
		}
		mSelect = null;
		mNestedStore = null;
		mTerm = null;
	}

	public MultiDimensionalSelect getSelect() {
		return mSelect;
	}

	public MultiDimensionalNestedStore getNestedStore() {
		return mNestedStore;
	}

	public Term toTerm() {
		return mTerm;
	}

	public static MultiDimensionalSelectOverNestedStore convert(final Script script, final Term term) {
		final MultiDimensionalSelectOverNestedStore mdsos = new MultiDimensionalSelectOverNestedStore(script, term);
		if (mdsos.getSelect() == null) {
			return null;
		} else {
			return mdsos;
		}
	}


	/**
	 * @return Term that is equivalent to this {@link MultiDimensionalSelectOverNestedStore}
	 * if the index of the select and the index of each store are distinct.
	 */
	public Term constructNotEqualsReplacement(final Script script) {
		final MultiDimensionalSelect mds = new MultiDimensionalSelect(getNestedStore().getArray(), getSelect().getIndex(),
				script);
		return mds.getSelectTerm();
	}


	/**
	 *
	 * @return List of all {@link MultiDimensionalSelectOverNestedStore} that occur
	 *         in given term.
	 */
	public static List<MultiDimensionalSelectOverNestedStore> extractMultiDimensionalSelectOverStores(final Script script,
			final Term term) {
		final List<MultiDimensionalSelectOverNestedStore> result = new ArrayList<>();
		final Set<ApplicationTerm> allSelectTerms = new ApplicationTermFinder("select", false)
				.findMatchingSubterms(term);
		for (final ApplicationTerm selectTerm : allSelectTerms) {
			final MultiDimensionalSelectOverNestedStore mdsos = MultiDimensionalSelectOverNestedStore.convert(script,
					selectTerm);
			if (mdsos != null) {
				result.add(mdsos);
			}
		}
		return result;
	}

	/**
	 *
	 * @return List of all {@link MultiDimensionalSelectOverNestedStore} that occur
	 *         in given term and where arr is first operand of the (inner) store.
	 */
	public static List<MultiDimensionalSelectOverNestedStore> extractMultiDimensionalSelectOverStores(final Script script,
			final Term term, final Term arr) {
		final List<MultiDimensionalSelectOverNestedStore> result = new ArrayList<>();
		final Set<ApplicationTerm> allSelectTerms = new ApplicationTermFinder("select", false)
				.findMatchingSubterms(term);
		for (final ApplicationTerm selectTerm : allSelectTerms) {
			final MultiDimensionalSelectOverNestedStore mdsos = MultiDimensionalSelectOverNestedStore.convert(script,
					selectTerm);
			if (mdsos != null && mdsos.getNestedStore().getArray() == arr) {
				result.add(mdsos);
			}
		}
		return result;
	}

}
