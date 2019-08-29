/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-Sifa plug-in.
 *
 * The ULTIMATE Library-Sifa plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-Sifa plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-Sifa plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-Sifa plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-Sifa plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.sifa.summarizers;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Star;

/**
 * Computes summaries to skip loops.
 *
 * @author schaetzc@tf.uni-freiburg.de
 */
public interface ILoopSummarizer {

	/**
	 * Computes a loop summary for a given starred regex and its input.
	 * <p>
	 * A loop summary over-approximates the states obtained by executing the loop body arbitrarily often
	 * (this includes never). In other words:
	 * <pre>
	 * summarize((inner)*, input) ⊇ input ∪ post(input, inner) ∪ post(post(input, inner), inner) ∪ …
	 * </pre>
	 * <p>
	 *
	 * @param regex A regex of the form {@code (inner)*}
	 * @param input Input before executing {@code inner}
	 * @return A loop summary
	 */
	IPredicate summarize(Star<IIcfgTransition<IcfgLocation>> regex, IPredicate input);
}
