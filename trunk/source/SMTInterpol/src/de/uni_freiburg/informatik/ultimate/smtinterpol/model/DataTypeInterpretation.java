/*
 * Copyright (C) 2022 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.model;

import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.DataType;
import de.uni_freiburg.informatik.ultimate.logic.DataType.Constructor;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

public class DataTypeInterpretation implements SortInterpretation {
	Model mModel;
	Sort mSort;

	Set<Term> mExistingTerms = new LinkedHashSet<>();
	private FunctionSymbol mInfiniteConstructor;
	private int mInfiniteConsArg;

	public DataTypeInterpretation(Model model, Sort sort) {
		mModel = model;
		mSort = sort;
	}

	@Override
	public Term toSMTLIB(final Theory t, final Sort sort) {
		throw new InternalError("Should never be called!");
	}

	@Override
	public Term extendFresh(final Sort sort) {
		assert mSort == sort;
		return extendFreshOrLast(new HashSet<Sort>());
	}

	private boolean isInfinite(Sort sort, Set<Sort> visited) {
		final DataType dataType = (DataType) sort.getSortSymbol();
		for (final Constructor constr : dataType.getConstructors()) {
			for (final Sort argSort : constr.getArgumentSorts()) {
				final Sort realArgSort = argSort.mapSort(sort.getArguments());
				if (realArgSort.isNumericSort() || realArgSort.isArraySort() || !realArgSort.isInternal()
						|| (realArgSort.getSortSymbol().isDatatype() && isInfinite(realArgSort, visited))) {
					return true;
				}
			}
		}
		return false;
	}

	private void findInfiniteConstructor() {
		final DataType dataType = (DataType) mSort.getSortSymbol();
		final HashSet<Sort> visited = new HashSet<>();
		visited.add(mSort);
		for (final Constructor constr : dataType.getConstructors()) {
			final Sort[] argSorts = constr.getArgumentSorts();
			Sort[] realArgSorts = argSorts;
			if (mSort.getArguments().length > 0) {
				realArgSorts = new Sort[argSorts.length];
				for (int j = 0; j < argSorts.length; j++) {
					realArgSorts[j] = argSorts[j].mapSort(mSort.getArguments());
				}
			}
			for (int j = 0; j < argSorts.length; j++) {
				if (realArgSorts[j].isNumericSort() ||
						realArgSorts[j].isArraySort() ||
						!realArgSorts[j].isInternal() ||
						(realArgSorts[j].getSortSymbol().isDatatype() && isInfinite(realArgSorts[j], visited))) {
					mInfiniteConsArg = j;
					final Sort constrSort = constr.needsReturnOverload() ? mSort : null;
					mInfiniteConstructor = mModel.getTheory().getFunctionWithResult(constr.getName(), null,
							constrSort, realArgSorts);
				}
			}
		}
	}

	private Term createSomeTerm(HashSet<Sort> visited) {
		if (!mExistingTerms.isEmpty()) {
			return mExistingTerms.iterator().next();
		}
		if (!visited.add(mSort)) {
			return null;
		}
		final DataType dataType = (DataType) mSort.getSortSymbol();
		next_constructor:
		for (final Constructor constr : dataType.getConstructors()) {
			final Sort[] argSorts = constr.getArgumentSorts();
			Sort[] realArgSorts = argSorts;
			final Term[] args = new Term[argSorts.length];
			if (mSort.getArguments().length > 0) {
				realArgSorts = new Sort[argSorts.length];
				for (int j = 0; j < argSorts.length; j++) {
					realArgSorts[j] = argSorts[j].mapSort(mSort.getArguments());
				}
			}
			for (int j = 0; j < argSorts.length; j++) {
				if (realArgSorts[j].getSortSymbol().isDatatype()) {
					final DataTypeInterpretation childInterpretation =
							((DataTypeInterpretation) mModel.provideSortInterpretation(realArgSorts[j]));
					args[j] = childInterpretation.createSomeTerm(visited);
					if (args[j] == null) {
						continue next_constructor;
					}
				} else {
					args[j] = mModel.getSomeValue(realArgSorts[j]);
				}
			}
			final Sort returnSort = constr.needsReturnOverload() ? mSort : null;
			final Term newTerm = mModel.getTheory().term(constr.getName(), null, returnSort, args);
			register(newTerm);
			return newTerm;
		}
		throw new AssertionError("DataType is empty");
	}

	private Term getLastAddedTerm() {
		if (mExistingTerms.isEmpty()) {
			final Term term = createSomeTerm(new HashSet<Sort>());
			assert term != null : "DataType is empty";
			return term;
		} else {
			final Iterator<Term> it = mExistingTerms.iterator();
			Term last = it.next();
			while (it.hasNext()) {
				last = it.next();
			}
			return last;
		}
	}

	private Term extendFreshOrLast(Set<Sort> visited) {
		if (!visited.add(mSort)) {
			// in case we are calling ourself for a fresh term, we provide the last term, which will ensure
			// that the returned term is fresh.
			return getLastAddedTerm();
		}
		if (mInfiniteConstructor == null) {
			findInfiniteConstructor();
		}
		final Sort[] argSorts = mInfiniteConstructor.getParameterSorts();
		final Term[] args = new Term[argSorts.length];
		for (int i = 0; i < args.length; i++) {
			if (i != mInfiniteConsArg) {
				args[i] = mModel.getSomeValue(argSorts[i]);
			} else if (argSorts[i].getSortSymbol().isDatatype()) {
				final DataTypeInterpretation childInterpretation =
						((DataTypeInterpretation) mModel.provideSortInterpretation(argSorts[i]));
				args[i] = childInterpretation.extendFreshOrLast(visited);
			} else {
				args[i] = mModel.extendFresh(argSorts[i]);
			}
		}
		final Term newTerm = mModel.getTheory().term(mInfiniteConstructor, args);
		register(newTerm);
		return newTerm;
	}

	@Override
	public void register(final Term term) {
		assert term.getSort() == mSort && ((ApplicationTerm) term).getFunction().isConstructor();
		mExistingTerms.add(term);
	}

	@Override
	public String toString() {
		return "datatypeSort" + mExistingTerms;
	}

	public static Rational toRational(final Term constTerm) {
		return ((Rational) ((ConstantTerm) constTerm).getValue());
	}

	@Override
	public Term getModelValue(int idx, final Sort sort) {
		while (idx >= mExistingTerms.size()) {
			extendFresh(sort);
		}
		final Iterator<Term> it = mExistingTerms.iterator();
		while (idx-- > 0) {
			it.next();
		}
		return it.next();
	}
}
