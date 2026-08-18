/*
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of the ULTIMATE CountertraceParser plug-in.
 *
 * The ULTIMATE CountertraceParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CountertraceParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CountertraceParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CountertraceParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CountertraceParser plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.countertrace.parser;

import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.DeclarationPattern;

/**
 * Result of parsing an entire {@code .ct} file.
 *
 * <p>
 * A {@code .ct} file may contain two kinds of entries:
 * </p>
 * <ul>
 * <li><b>Declarations</b> — variable and constant declarations analogous to {@code .req} files (e.g.,
 * {@code Input R is bool}, {@code Const c is 5}). These are stored as {@link DeclarationPattern} objects.</li>
 * <li><b>Countertraces</b> — one or more countertrace formulae, each optionally preceded by an ID. These are stored as
 * {@link CountertraceParserResult} objects.</li>
 * </ul>
 *
 * @author University of Freiburg
 */
public class CountertraceFileResult {

	private final List<DeclarationPattern> mDeclarations;
	private final List<CountertraceParserResult> mCountertraces;

	public CountertraceFileResult(final List<DeclarationPattern> declarations,
			final List<CountertraceParserResult> countertraces) {
		mDeclarations = Collections.unmodifiableList(declarations);
		mCountertraces = Collections.unmodifiableList(countertraces);
	}

	/**
	 * @return The variable/constant declarations from this file (may be empty).
	 */
	public List<DeclarationPattern> getDeclarations() {
		return mDeclarations;
	}

	/**
	 * @return The countertrace entries from this file (may be empty).
	 */
	public List<CountertraceParserResult> getCountertraces() {
		return mCountertraces;
	}
}
