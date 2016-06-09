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
package de.uni_freiburg.informatik.ultimate.logic;

import java.math.BigInteger;
import java.util.ArrayDeque;
import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.util.HashUtils;

/**
 * Represents an SMTLIB sort.  We distinguish real sorts (which
 * are declared with declare-sort or pre-defined in the logic) from
 * defined sort (which are defined with define-sort to some other sort.
 * For a real sort, <tt>getRealSort() == this</tt> holds.
 * 
 * A sort has a sort symbol and as many sort arguments as the sort symbol
 * specifies.  There are also parametric sorts used for declaring polymorphic
 * function symbols.  A parametric sort (or sort variable) has a position
 * (used for substitution) and a name, both stored in the SortSymbol.
 * 
 * Every term has a closed real sort, which can be obtained by term.getSort().
 * Defined sorts may occur only in function symbols and the declared sort of
 * a term variable.  Sorts that are not closed may only occur in polymorphic
 * function symbols and in sort definitions in SortSymbol.
 * 
 * @author Jochen Hoenicke
 */
public final class Sort {
	/**
	 * The sort symbol.
	 */
	final SortSymbol mSymbol;
	/**
	 * The arguments of the sort symbol.  This is null if the sort symbol 
	 * has no arguments, otherwise it is an array with mSymbol.mnumParams
	 * elements.
	 */
	final Sort[]     mArgs;
	/**
	 * The indices of the sort symbol.  For the sort BitVec this is an
	 * array with one element containing the bit length.  This field is
	 * null (instead of the empty array) if there are no indices.
	 */
	final BigInteger[] mIndices;
	/**
	 * The cached real sort.  This is null if real sort was not yet computed.
	 * Otherwise it is this for a real sort and the real sort as which the
	 * sort is defined in all other cases.
	 */
	//@ invariant mRealSort == null || mRealSort.getRealSort() == mRealSort
	Sort       mRealSort;
	
	private int mHash;
	
	Sort(SortSymbol sym, BigInteger[] indices, Sort[] args) {
		assert args != null;
		assert args.length == (sym.isParametric() ? 0 : sym.mNumParams) 
				: "Sort created with wrong number of args";
		mSymbol = sym;
		mIndices = indices;
		mArgs = args;
		mHash = HashUtils.hashJenkins(mSymbol.hashCode(), (Object[]) mArgs);
		if (mIndices != null) {
			mHash = HashUtils.hashJenkins(mHash, (Object[]) mIndices);
		}
	}
	
	/**
	 * Get the name of this sort.
	 * @return the name.
	 */
	public String getName() {
		return mSymbol.getName();
	}

	/**
	 * Get the indexed name of this sort in smtlib representation.
	 * @return the name.
	 */
	public String getIndexedName() {
		final String name = PrintTerm.quoteIdentifier(mSymbol.getName());
		if (mIndices == null) {
			return name;
		}
		final StringBuilder sb = new StringBuilder();
		sb.append("(_ ").append(name);
		for (final BigInteger i : mIndices) {
			sb.append(' ').append(i);
		}
		sb.append(')');
		return sb.toString();
	}
	
	
	/**
	 * Get the indices, if this is an indexed sort like (_ bv 5).
	 * @return the indices, null if this sort is not indexed.
	 */
	public BigInteger[] getIndices() {
		return mIndices;
	}
	
	/**
	 * Get the sort arguments for a sort.  This is used for a sort, whose
	 * sort symbol was declared with 
	 * {@link Script#declareSort(String, int) declare-sort(name, int)}
	 * where the second parameter is not zero.  In that case the sort is created
	 * with sort arguments and these arguments are returned by this method.
	 * @return An array containing the sort arguments for this sort.
	 * You must never write to this array.     
	 */
	public Sort[] getArguments() {
		return mArgs;
	}
	
	/**
	 * Get the real sort.  This is used for sorts that are defined with
	 * {@link Script#defineSort(String, Sort[], Sort) define-sort}.
	 * For other sorts this just returns this.
	 * @return the sort representation where all sort definitions are expanded.
	 */
	public Sort getRealSort() {
		if (mRealSort == null) {
			if (mSymbol.mSortDefinition == null) {
				if (mArgs.length == 0) {
					mRealSort = this;
				} else {
					Sort[] newArgs = mArgs;
					for (int i = 0; i < newArgs.length; i++) {
						final Sort realArg = mArgs[i].getRealSort();
						if (realArg != mArgs[i]) {
							if (newArgs == mArgs) {
								newArgs = mArgs.clone();
							}
							newArgs[i] = realArg;
						}
					}
					if (newArgs == mArgs) {
						mRealSort = this;
					} else {
						mRealSort =
							mSymbol.getSort(mIndices, newArgs).getRealSort();
					}
				}
			} else {
				mRealSort = 
					mSymbol.mSortDefinition.mapSort(mArgs).getRealSort();
			}
		}
		return mRealSort;
	}
	
	boolean equalsSort(Sort other) {
		if (this == other) {
			return true;
		}
		return getRealSort() == other.getRealSort();
	}
	
	/**
	 * Unify this sort with a concrete sort.
	 * 
	 * @param unifier The unifier map. It serves as map from sort parameters 
	 * to substituted sorts, and also as cache for all open sorts.  It should
	 * contain all previously computed substitutions.
	 * @param concrete the concrete sort to unify this sort with.  
	 *        It must be closed and real.
	 * @return true if the sorts unify (in which case the unifier is extended)
	 * or false otherwise.
	 */
    boolean unifySort(HashMap<Sort,Sort> unifier, Sort concrete) {
    	assert concrete.getRealSort() == concrete;
		final Sort last = unifier.get(this);
		if (last != null) {
			return last == concrete;
		}
		
		if (!mSymbol.isParametric()) {
			final Sort me = getRealSort();
			if (me.mSymbol != concrete.mSymbol) {
				return false;
			}

			for (int i = 0; i < me.mArgs.length; i++) {
				if (!me.mArgs[i].unifySort(unifier, concrete.mArgs[i])) {
					return false;
				}
			}
		}
		unifier.put(this, concrete);
		return true;
	}

	/**
	 * Substitute this sort.  
	 * 
	 * @param substitution The substitution. Note that every sort variable has
	 * a unique position which is used as index in the substitution array.
	 * @return The substituted sort.
	 */
    Sort mapSort(Sort[] substitution) {
		if (mSymbol.isParametric()) {
			return substitution[mSymbol.mNumParams];
		}
		if (mArgs.length == 0) {
			return this;
		}
    	if (mArgs.length == 1) {
    		final Sort arg = mArgs[0].mapSort(substitution);
    		return mSymbol.getSort(mIndices, new Sort[] { arg });
    	}
    	
    	// For more than two arguments create a cache to avoid exponential blow
    	final HashMap<Sort, Sort> cachedMappings = new HashMap<Sort,Sort>();
    	return mapSort(substitution, cachedMappings);
    }
    
	/**
	 * Substitute this sort.  
	 * 
	 * @param substitution The substitution. Note that every sort variable has
	 * a unique position which is used as index in the substitution array.
	 * @param cachedMappings A cache storing for each visited sort the 
	 * corresponding substituted sort.
	 * @return The substituted sort.
	 */
    Sort mapSort(Sort[] substitution, HashMap<Sort, Sort> cachedMappings) {
		if (mSymbol.isParametric()) {
			return substitution[mSymbol.mNumParams];
		}
    	Sort result = cachedMappings.get(this);
    	if (result != null) {
			return result;
		}
    	if (mArgs.length == 0) {
			result = this;
		} else {
			final Sort[] newArgs = new Sort[mArgs.length];
			for (int i = 0; i < mArgs.length; i++) {
				newArgs[i] = mArgs[i].mapSort(substitution, cachedMappings);
			}
			result = mSymbol.getSort(mIndices, newArgs);
    	}
		cachedMappings.put(this, result);
		return result;
	}

	/**
	 * This returns true if and only if the sort was created with
	 * {@link Script#sortVariables(String...)}.  These are only used for a 
	 * later {@link Script#defineSort(String, Sort[], Sort) define-sort}
	 * command.
	 * @return true iff this is a sort variable.     
	 */
	public boolean isParametric() {
		return mSymbol.isParametric();
	}

	/**
	 * This returns the SMTLIB string represenation of this sort.
	 * @return the SMTLIB string representation.     
	 */
	@Override
	public String toString() {
		if (mArgs.length == 0) {
			return getIndexedName();
		}
		final StringBuilder sb = new StringBuilder();
		new PrintTerm().append(sb, this);
		return sb.toString();
	}
	
	/**
	 * Convert a sort to a string in a stack based fashion.
	 * @param mTodo The stack where to put the strings and sub sorts.
	 * @see PrintTerm
	 */
	void toStringHelper(ArrayDeque<Object> mTodo) {
		final String name = getIndexedName();
		final Sort[] args = getArguments();
		if (args.length == 0) {
			mTodo.addLast(name);
		} else {
			mTodo.addLast(")");
			for (int i = args.length - 1; i >= 0; i--) {
				mTodo.addLast(args[i]);
				mTodo.addLast(" ");
			}
			mTodo.addLast(name);
			mTodo.addLast("(");
		}
	}
	
	public Theory getTheory() {
		return mSymbol.mTheory;
	}

	/**
	 * Returns true if this is an array sort.  This is any instantiation
	 * of the parametric sort Array defined by the SMTLIB array theory.
	 * @return true if this is an array sort.
	 */
	public boolean isArraySort() {
		return getRealSort().mSymbol.isArray();
	}
	/**
	 * Returns true if this is a numeric sort.  Numeric sorts are only the
	 * sorts Int and Real defined by the corresponding SMTLIB theories.
	 * @return true if this is a numeric sort.
	 */
	public boolean isNumericSort() {
		return getRealSort().mSymbol.isNumeric();
	}

	/**
	 * Returns true if this sort is internal, i.e., defined by an SMTLIB 
	 * theory.
	 * @return true if the sort is internal, false if it is user defined.
	 */
	public boolean isInternal() {
		return mSymbol.isIntern();
	}
	
	@Override
	public int hashCode() {
		return mHash;
	}
}
