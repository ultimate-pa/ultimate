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

import java.util.ArrayDeque;

import de.uni_freiburg.informatik.ultimate.util.HashUtils;

/**
 * Represents a function application term.  This consists of a function 
 * symbol and zero or more sub-terms (the parameters of the function).
 * A constant is represented as function application with zero parameters.
 *
 * An application term is created by 
 * {@link Script#term(String, Term...)} or
 * for indexed function symbols or for symbols with generic return sort by
 * {@link Script#term(String, java.math.BigInteger[], Sort, Term...)}.
 *
 * @author hoenicke
 */
public class ApplicationTerm extends Term {
	final FunctionSymbol mFunction;
	final Term[] mParameters;

	ApplicationTerm(FunctionSymbol function, Term[] parameters, int hash) {
		super(hash);
		function.typecheck(parameters);
		mFunction   = function;
		mParameters = parameters;
	}

	/**
	 * Get the function symbol.
	 * @return the function symbol. 
	 * @see FunctionSymbol#getName()
	 */
	public FunctionSymbol getFunction() {
		return mFunction;
	}

	/**
	 * Get the parameters of the function application.
	 * @return the parameters.  For constants this array is empty.
	 * Never write to this array!
	 */
	public Term[] getParameters() {
		return mParameters;
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public Sort getSort() {
		return mFunction.mReturnSort.getRealSort();
	}
		
	static final int hashApplication(
			FunctionSymbol func, Term[] parameters) {
		return HashUtils.hashJenkins(func.hashCode(), (Object[])parameters);
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public void toStringHelper(ArrayDeque<Object> mTodo) {
		final String func = getFunction().getApplicationString();
		final Term[] args = getParameters();
		if (args.length == 0) {
			mTodo.add(func);
		} else {
			// Add arguments to stack.
			mTodo.addLast(")");
			for (int i = args.length - 1; i >= 0; i--) {
				mTodo.addLast(args[i]);
				mTodo.addLast(" ");
			}
			mTodo.add(func);
			mTodo.add("(");
		}
	}
}
