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
package de.uni_freiburg.informatik.ultimate.lib.sifa;

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.IRegex;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Star;
import de.uni_freiburg.informatik.ultimate.lib.sifa.regexdag.RegexDag;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.RegexStatUtils;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;

/**
 * Stores compressed {@link RegexDag}s for the content of star expressions.
 * Inside a RegexDag the very same star expression may appear multiple times, therefore, we can save a lot
 * of work by caching the result of converting the star expression into a DAG and then compressing that DAG.
 *
 * @author schaetzc@tf.uni-freiburg.de
 */
public class StarDagCache {

	private final SifaStats mStats;
	private final Map<IRegex<IIcfgTransition<IcfgLocation>>, RegexDag<IIcfgTransition<IcfgLocation>>> mCache =
			new HashMap<>();

	public StarDagCache(final SifaStats stats) {
		mStats = stats;
	}

	public RegexDag<IIcfgTransition<IcfgLocation>> dagOf(final IRegex<IIcfgTransition<IcfgLocation>> regex) {
		return mCache.computeIfAbsent(regex, this::computeDagOf);
	}

	private RegexDag<IIcfgTransition<IcfgLocation>> computeDagOf(final IRegex<IIcfgTransition<IcfgLocation>> regex) {
		if (regex instanceof Star<?>) {
			throw new AssertionError("Tried to compute RegexDag for star expression. "
					+ "Computing such a DAG is possible but probably not what you want. "
					+ "Either you forgot to call .inner() on the star for which you want to compute a DAG "
					+ "or your regex is of the form ((expr)*)* which could be simplified to just (expr)*.");
		}
		return RegexStatUtils.compress(mStats, RegexStatUtils.regexToDag(mStats, regex));
	}
}
