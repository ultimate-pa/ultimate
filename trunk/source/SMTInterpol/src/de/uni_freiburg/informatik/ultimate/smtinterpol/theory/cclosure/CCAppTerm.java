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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure;

import java.util.ArrayDeque;
import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.HashUtils;

public class CCAppTerm extends CCTerm {
	final FunctionSymbol mFunc;
	final CCTerm[] mArgs;
	Term mSmtTerm;

	CongruenceTrigger mCongTrigger;
	FindTriggerTrigger mFindTrigger;

	public CCAppTerm(FunctionSymbol fsym, final CCTerm[] args,
			final CClosure engine, final boolean isFromQuant) {
		super(HashUtils.hashJenkins(fsym.hashCode(), (Object[]) args), isFromQuant ? CCAppTerm.computeAge(args) : 0);
		mFunc = fsym;
		mArgs = args;
	}

	private final static int computeAge(CCTerm[] args) {
		int age = 1;
		for (int i = 0; i < args.length; i++) {
			age = Math.max(age, args[i].mAge + 1);
		}
		return age;
	}

	public FunctionSymbol getFunctionSymbol() {
		return mFunc;
	}

	public CCTerm[] getArguments() {
		return mArgs;
	}

	public CCTerm getArgument(int argPosition) {
		return mArgs[argPosition];
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		final HashMap<CCAppTerm, Integer> visited = new HashMap<>();
		final ArrayDeque<Object> todo = new ArrayDeque<>();
		todo.add(this);
		while (!todo.isEmpty()) {
			final Object item = todo.removeLast();
			if (item instanceof String) {
				sb.append(item);
			} else if (item instanceof CCAppTerm) {
				final CCAppTerm app = (CCAppTerm) item;
				final Integer id = visited.get(item);
				if (id != null) {
					sb.append("@" + id);
				} else {
					visited.put(app, visited.size());
					todo.add(")");
					for (int i = app.mArgs.length - 1; i >= 0; i--) {
						todo.add(app.mArgs[i]);
						todo.add(" ");
					}
					todo.add(app.mFunc.getApplicationString());
					todo.add("(");
				}
			} else if (item instanceof CCBaseTerm) {
				sb.append(item);
			} else {
				throw new AssertionError("Unknown CCTerm " + item);
			}
		}
		return sb.toString();
	}
}
