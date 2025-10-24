/*
 * Copyright (C) 2024 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify it under the
 * terms of the GNU Lesser General Public License as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License along with the
 * ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7: If you modify the ULTIMATE TraceCheckerUtils Library,
 * or any covered work, by linking or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the licensors of the
 * ULTIMATE TraceCheckerUtils Library grant you additional permission to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.assertorders;

import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.Counterexample;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.AnnotateAndAsserter;

/**
 * This interface is used as an abstraction for assert orders. An assert order is a partitioning of the counterexample.
 * The actual assertion of the partitions is done in {@link AnnotateAndAsserter}.
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public interface IAssertOrder<L extends IAction> {
	/**
	 * Partitions the trace of the counterexample. As a trace might contain statements multiple times, the indices of
	 * the statements in the trace are contained in the result, rather the the statements itself.
	 *
	 * @param counterexample
	 *            the current counterexample
	 * @return the partitions represented by their indices.
	 */
	List<Set<Integer>> partition(final Counterexample<L> counterexample);
}
