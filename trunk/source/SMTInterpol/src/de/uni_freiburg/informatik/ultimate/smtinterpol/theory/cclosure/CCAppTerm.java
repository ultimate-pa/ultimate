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
import java.util.ArrayList;
import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.HashUtils;

public class CCAppTerm extends CCTerm {
	final FunctionSymbol mFunc;
	/**
	 * The arguments of the application as {@link CCParameter}s: argument {@code i} of the represented application has
	 * value {@code mArgs[i]}, i.e. {@code mArgs[i].getCCTerm() + mArgs[i].getOffset()}. An offset-free argument is a
	 * bare {@link CCTerm} (no wrapper object), so a term like {@code f(x+5)} stores the offset-free CCTerm {@code x}
	 * wrapped in an {@link OffsettedCCTerm} remembering the {@code +5} only for that one argument; plain congruence
	 * closure allocates nothing extra.
	 */
	final CCParameter[] mArgs;
	Term mSmtTerm;

	CongruenceTrigger mCongTrigger;
	FindTriggerTrigger mFindTrigger;
	/**
	 * The reverse trigger signatures created for this application by {@link MasterReverseTrigger#activate}, one per
	 * master trigger watching this application's function symbol. They must be removed together with this term (see
	 * {@code CClosure.removeTerm}), otherwise a stale application entry survives a pop and later trigger merges
	 * activate reverse triggers on the removed term.
	 */
	ArrayList<ReverseTriggerTrigger> mReverseTriggers;

	public CCAppTerm(FunctionSymbol fsym, final CCParameter[] args,
			final CClosure engine, final boolean isFromQuant) {
		super(HashUtils.hashJenkins(fsym.hashCode(), (Object[]) args), isFromQuant ? CCAppTerm.computeAge(args) : 0);
		mFunc = fsym;
		mArgs = args;
	}

	private final static int computeAge(CCParameter[] args) {
		int age = 1;
		for (int i = 0; i < args.length; i++) {
			age = Math.max(age, args[i].getCCTerm().mAge + 1);
		}
		return age;
	}

	public FunctionSymbol getFunctionSymbol() {
		return mFunc;
	}

	/** The number of arguments of this application. */
	public int getArgCount() {
		return mArgs.length;
	}

	/**
	 * @return the constant offset added to the argument at the given position, i.e. the argument value is
	 *         {@code getArgParam(argPosition).getCCTerm() + getArgOffset(argPosition)}.
	 */
	public Rational getArgOffset(int argPosition) {
		return mArgs[argPosition].getOffset();
	}

	/**
	 * The value of the argument at the given position as a {@link CCParameter} ("a CCTerm up to a constant offset").
	 * This is the only argument accessor: callers that genuinely want the offset-free structural CCTerm must say so
	 * explicitly via {@code getArgParam(i).getCCTerm()}.
	 */
	public CCParameter getArgParam(int argPosition) {
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
						if (!app.getArgOffset(i).equals(Rational.ZERO)) {
							todo.add("+" + app.getArgOffset(i));
						}
						todo.add(app.mArgs[i].getCCTerm());
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
