/*
 * Copyright (C) 2024 Matthias Heizmann (matthias.heizmann@iste.uni-stuttgart.de)
 * Copyright (C) 2024 University of Stuttgart
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

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Random;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.Counterexample;

/**
 * Partitions a trace of length n into n singletons. Use a pseudo random generator to order the elements of the
 * partition. The seed for the pseudo random generator is given by the (stable) hash code of the trace.
 *
 * @author Matthias Heizmann (matthias.heizmann@iste.uni-stuttgart.de)
 */
public class AssertOrderShuffledSingletons<L extends IAction> implements IAssertOrder<L> {
	@Override
	public List<Set<Integer>> partition(final Counterexample<L> counterexample) {
		final List<Set<Integer>> list = new ArrayList<>();
		for (int i = 0; i < counterexample.getWord().length(); i++) {
			list.add(Set.of(i));
		}
		Collections.shuffle(list, new Random(counterexample.getWord().asList().hashCode()));
		return list;
	}
}
