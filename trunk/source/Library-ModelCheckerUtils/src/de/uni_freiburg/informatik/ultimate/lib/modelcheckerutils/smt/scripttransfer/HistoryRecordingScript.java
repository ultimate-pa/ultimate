/*
 * Copyright (C) 2019 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.WrapperScript;

/**
 * {@link HistoryRecordingScript} is a {@link WrapperScript} that tracks definitions and declarations of functions,
 * sorts and variables of the underlying {@link Script} instance in the order of their occurence as
 * {@link ISmtDeclarable}.
 *
 * {@link ISmtDeclarable} can be used to initialize a new solver instance with the same functions, sorts and variables.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class HistoryRecordingScript extends WrapperScript {

	private final Deque<ISmtDeclarable> mHistory;

	public HistoryRecordingScript(final Script script) {
		super(script);
		mHistory = new ArrayDeque<>();
	}

	@Override
	public void defineFun(final String fun, final TermVariable[] params, final Sort resultSort, final Term definition)
			throws SMTLIBException {
		super.defineFun(fun, params, resultSort, definition);
		insert(SmtFunctionDefinition.createFromScriptDefineFun(fun, params, resultSort, definition));
	}

	@Override
	public void defineSort(final String sort, final Sort[] sortParams, final Sort definition) {
		super.defineSort(sort, sortParams, definition);
	}

	@Override
	public TermVariable variable(final String varname, final Sort sort) {
		return super.variable(varname, sort);
	}

	@Override
	public void declareFun(final String fun, final Sort[] paramSorts, final Sort resultSort) {
		super.declareFun(fun, paramSorts, resultSort);
		insert(SmtFunctionDefinition.createFromScriptDeclareFun(fun, paramSorts, resultSort));
	}

	@Override
	public void declareSort(final String sort, final int arity) {
		super.declareSort(sort, arity);
	}

	@Override
	public void push(final int levels) {
		super.push(levels);
		for (int i = 0; i < levels; ++i) {
			mHistory.push(StackMarker.INSTANCE);
		}
	}

	@Override
	public void pop(final int levels) {
		super.pop(levels);
		final Iterator<ISmtDeclarable> iter = mHistory.descendingIterator();
		int markerCount = 0;
		for (int i = 0; i < levels; ++i) {
			while (iter.hasNext()) {
				// TODO: Possibly too expensive!
				final ISmtDeclarable current = iter.next();
				iter.remove();
				if (current == StackMarker.INSTANCE) {
					markerCount++;
					break;
				}
			}
		}
		if (markerCount != levels) {
			throw new AssertionError("Found not enough markers!");
		}
	}

	private void insert(final ISmtDeclarable declarable) {
		mHistory.add(declarable);
	}

	/**
	 * Transfers the history from this {@link Script} instance to the given one. This means that all declarations and
	 * definitions recorded by this {@link Script} instance will be redone on the supplied {@link Script} instance,
	 * including {@link Script#push(int)} and {@link Script#pop(int)} operations.
	 *
	 * Note: If the other {@link Script} instance already has a state, this might lead to confusing results or even
	 * crashes (e.g., if symbols are defined twice).
	 *
	 * @param script
	 *            The {@link Script} instance that will receive all definitions and declarations known to this
	 *            {@link Script}.
	 */
	public void transferHistory(final Script script) {
		for (final ISmtDeclarable elem : mHistory) {
			if (elem instanceof StackMarker) {
				script.push(1);
				continue;
			}
			elem.defineOrDeclare(script);
		}
	}

	/**
	 * @return A map from function name to {@link SmtFunctionDefinition} in the order of declaration or definition in
	 *         the underlying script. The map does not update when the underlying script changes.
	 */
	public Map<String, SmtFunctionDefinition> getFunctionDefinitionHistory() {
		final Map<String, SmtFunctionDefinition> rtr = new LinkedHashMap<>();
		mHistory.stream().filter(a -> a instanceof SmtFunctionDefinition).forEachOrdered(a -> {
			final SmtFunctionDefinition def = (SmtFunctionDefinition) a;
			rtr.put(def.getName(), def);
		});
		return rtr;
	}

	private static final class StackMarker implements ISmtDeclarable {

		private static final StackMarker INSTANCE = new StackMarker();

		@Override
		public void defineOrDeclare(final Script script) {
			throw new UnsupportedOperationException(
					getClass().getName() + " only marks stacks, it cannot be defined or declared");
		}

	}
}
