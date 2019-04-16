/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-SymbolicInterpretation plug-in.
 *
 * The ULTIMATE Library-SymbolicInterpretation plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-SymbolicInterpretation plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-SymbolicInterpretation plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-SymbolicInterpretation plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-SymbolicInterpretation plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.regexdag;

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.PathExpressionComputer;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Star;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.cfgpreprocessing.CfgPreprocessor;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.cfgpreprocessing.ProcedureGraph;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;

public class RegexDagManager {

	private final Map<String, RegexDag<IIcfgTransition<IcfgLocation>>> mProcedures = new HashMap<>();
	private final Map<Star<IIcfgTransition<IcfgLocation>>, RegexDag<IIcfgTransition<IcfgLocation>>> mStars =
			new HashMap<>();
	private final RegexToDag<IIcfgTransition<IcfgLocation>> mRegexToDag = new RegexToDag<>();
	private final CfgPreprocessor mCfgPreprocessor;

	public RegexDagManager(final IIcfg<IcfgLocation> icfg) {
		mCfgPreprocessor = new CfgPreprocessor(icfg);
	}

	public RegexDag<IIcfgTransition<IcfgLocation>> dagOfProcedure(final String procedureName) {
		RegexDag<IIcfgTransition<IcfgLocation>> dag = mProcedures.get(procedureName);
		if (dag != null) {
			return dag;
		}
		dag = makeDagForProcedure(procedureName);
		mProcedures.put(procedureName, dag);
		return dag;
	}

	public RegexDag<IIcfgTransition<IcfgLocation>> dagOfStar(final Star<IIcfgTransition<IcfgLocation>> star) {
		RegexDag<IIcfgTransition<IcfgLocation>> dag = mStars.get(star);
		if (dag != null) {
			return dag;
		}
		dag = makeDagForStar(star);
		mStars.put(star, dag);
		return dag;
	}

	private RegexDag<IIcfgTransition<IcfgLocation>> makeDagForProcedure(final String procedureName) {
		final ProcedureGraph procGraph = mCfgPreprocessor.graphOfProcedure(procedureName);
		final PathExpressionComputer<IcfgLocation, IIcfgTransition<IcfgLocation>> peComputer =
				new PathExpressionComputer<>(procGraph);
		procGraph.errorAndExitNodesStream()
				.map(errorOrExit -> peComputer.exprBetween(procGraph.getEntryNode(), errorOrExit))
				.forEach(mRegexToDag::apply);
		final RegexDag<IIcfgTransition<IcfgLocation>> dag = retrieveAndCompressDag();
		mProcedures.put(procedureName, dag);
		return dag;
	}

	private RegexDag<IIcfgTransition<IcfgLocation>> makeDagForStar(final Star<IIcfgTransition<IcfgLocation>> star) {
		mRegexToDag.apply(star);
		final RegexDag<IIcfgTransition<IcfgLocation>> dag = retrieveAndCompressDag();
		mStars.put(star, dag);
		return dag;
	}

	private RegexDag<IIcfgTransition<IcfgLocation>> retrieveAndCompressDag() {
		RegexDag<IIcfgTransition<IcfgLocation>> dag = mRegexToDag.getDag();
		mRegexToDag.resetDag();
		// TODO compress DAG by merging nodes
		return dag;
	}
}







