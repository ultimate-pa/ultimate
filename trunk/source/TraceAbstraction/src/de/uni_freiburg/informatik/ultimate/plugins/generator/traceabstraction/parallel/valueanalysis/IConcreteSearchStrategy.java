/*
 * Copyright (C) 2026 University of Freiburg
 * Copyright (C) 2026 LMU Munich
 * Copyright (C) 2026 Max Barth (Max.Barth@lmu.de)
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.valueanalysis;

import java.util.function.BooleanSupplier;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.valueanalysis.ConcreteConfiguration;
import de.uni_freiburg.informatik.ultimate.lib.valueanalysis.ConcreteNwaSemantics;

/**
 * A way to explore the concrete configurations of a program in search of an error location. This is the extension
 * point of the value analysis worker: a new search implements this interface and gets a constant in
 * {@code TraceAbstractionPreferenceInitializer.ValueAnalysisSearch}, which {@code ValueAnalysisWorkerThread} maps to
 * it.
 * <p>
 * A search must not stop at the first error configuration it finds: {@code confirm} may reject it (the trace check
 * did not agree), and the search then goes on as if it had not found it.
 *
 * @param <L>
 *            the type of letters
 * @author Max Barth (max.barth@lmu.de)
 */
public interface IConcreteSearchStrategy<L extends IIcfgTransition<?>> {

	/**
	 * @param semantics
	 *            the program's concrete semantics
	 * @param keepGoing
	 *            polled regularly; the search stops as soon as it answers false. It is the only bound of the search:
	 *            it asks the worker's time limit and whether it was retired.
	 * @param confirm
	 *            asked for every error configuration found; true ends the search with it
	 * @return the confirmed error configuration, or null if the search ended without one
	 */
	ConcreteConfiguration<L> search(ConcreteNwaSemantics<L> semantics, BooleanSupplier keepGoing,
			Predicate<ConcreteConfiguration<L>> confirm);

	/**
	 * @return a one-line summary of the last search, for the log
	 */
	String getStatistics();
}
