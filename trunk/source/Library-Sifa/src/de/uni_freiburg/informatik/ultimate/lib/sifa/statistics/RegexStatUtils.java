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
package de.uni_freiburg.informatik.ultimate.lib.sifa.statistics;

import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.ILabeledGraph;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.PathExpressionComputer;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.IRegex;
import de.uni_freiburg.informatik.ultimate.lib.sifa.regexdag.RegexDag;
import de.uni_freiburg.informatik.ultimate.lib.sifa.regexdag.RegexDagCompressor;
import de.uni_freiburg.informatik.ultimate.lib.sifa.regexdag.RegexDagNode;
import de.uni_freiburg.informatik.ultimate.lib.sifa.regexdag.RegexToDag;

/**
 * Performs regex operations while updating statistics.
 * Statistics are not included in any regex classes to make them independent of sifa-specific classes.
 *
 * TODO This class would be better as wrappers around PEComputer, RegexToDag, and so on.
 *      The classes to be wrapped have only few public methods, so the change should be simple.
 *
 * @author schaetzc@tf.uni-freiburg.de
 */
public final class RegexStatUtils {

	private RegexStatUtils() {
		// objects are not required to use this class
	}

	/** @see PathExpressionComputer#PathExpressionComputer(ILabeledGraph) */
	public static <N, L> PathExpressionComputer<N, L> createPEComputer(final SifaStats stats,
			final ILabeledGraph<N, L> graph) {

		stats.start(SifaStats.Key.PATH_EXPR_TIME);
		final PathExpressionComputer<N, L> result = new PathExpressionComputer<>(graph);
		stats.stop(SifaStats.Key.PATH_EXPR_TIME);
		return result;
	}

	/** @see PathExpressionComputer#exprBetween(Object, Object) */
	public static <N, L> IRegex<L> exprBetween(final SifaStats stats,
			final PathExpressionComputer<N, L> peComputer, final N source, final N target) {

		stats.start(SifaStats.Key.PATH_EXPR_TIME);
		final IRegex<L> result = peComputer.exprBetween(source, target);
		stats.stop(SifaStats.Key.PATH_EXPR_TIME);
		return result;
	}

	/** @see RegexToDag#RegexToDag() */
	public static <L> RegexToDag<L> createRegexToDag(final SifaStats stats) {

		stats.start(SifaStats.Key.REGEX_TO_DAG_TIME);
		final RegexToDag<L> result = new RegexToDag<>();
		stats.stop(SifaStats.Key.REGEX_TO_DAG_TIME);
		return result;
	}

	/** @see RegexToDag#add(IRegex) */
	public static <L> RegexDagNode<L> addToDag(final SifaStats stats,
			final RegexToDag<L> regexToDag, final IRegex<L> regex) {

		stats.start(SifaStats.Key.REGEX_TO_DAG_TIME);
		final RegexDagNode<L> result = regexToDag.add(regex);
		stats.stop(SifaStats.Key.REGEX_TO_DAG_TIME);
		return result;
	}

	/** @see RegexToDag#getDagAndReset() */
	public static <L> RegexDag<L> getDagAndReset(final SifaStats stats,
			final RegexToDag<L> regexToDag) {

		stats.start(SifaStats.Key.REGEX_TO_DAG_TIME);
		final RegexDag<L> result = regexToDag.getDagAndReset();
		stats.stop(SifaStats.Key.REGEX_TO_DAG_TIME);
		return result;
	}

	/**
	 * Creates a {@link RegexToDag}, adds a single regex using {@link RegexToDag#add(IRegex)},
	 * and then returns the dag given {@link RegexToDag#getDagAndReset()}.
	 */
	public static <L> RegexDag<L> regexToDag(final SifaStats stats,
			final IRegex<L> regex) {

		stats.start(SifaStats.Key.REGEX_TO_DAG_TIME);
		final RegexToDag<L> regexToDag = new RegexToDag<>();
		regexToDag.add(regex);
		final RegexDag<L> result = regexToDag.getDagAndReset();
		stats.stop(SifaStats.Key.REGEX_TO_DAG_TIME);
		return result;
	}

	/** @see RegexDagCompressor#compress(RegexDag) */
	public static <L> RegexDag<L> compress(final SifaStats stats,
			final RegexDag<L> dag) {

		stats.add(SifaStats.Key.DAG_COMPRESSION_PROCESSED_NODES, dag.collectNodes().size());
		stats.start(SifaStats.Key.DAG_COMPRESSION_TIME);
		final RegexDag<L> result = new RegexDagCompressor<L>().compress(dag);
		stats.stop(SifaStats.Key.DAG_COMPRESSION_TIME);
		stats.add(SifaStats.Key.DAG_COMPRESSION_RETAINED_NODES, result.collectNodes().size());
		return result;
	}
}
