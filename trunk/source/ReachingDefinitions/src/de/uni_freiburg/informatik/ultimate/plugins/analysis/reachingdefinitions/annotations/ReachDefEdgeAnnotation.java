/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE ReachingDefinitions plug-in.
 * 
 * The ULTIMATE ReachingDefinitions plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE ReachingDefinitions plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ReachingDefinitions plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ReachingDefinitions plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE ReachingDefinitions plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations;

import java.util.HashMap;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.boogie.ScopedBoogieVar;

public class ReachDefEdgeAnnotation extends ReachDefBaseAnnotation {

	private static final long serialVersionUID = 1L;

	private final IcfgEdge mEdge;
	private DefCollector mDefCollector;
	private UseCollector mUseCollector;
	private final IAnnotationProvider<ReachDefStatementAnnotation> mProvider;
	private final String mKey;

	public ReachDefEdgeAnnotation(IcfgEdge e, IAnnotationProvider<ReachDefStatementAnnotation> provider, String key) {
		mEdge = e;
		mProvider = provider;
		mKey = key;
	}

	public ReachDefEdgeAnnotation(IcfgEdge e, IAnnotationProvider<ReachDefStatementAnnotation> provider) {
		this(e, provider, null);
	}

	public String getKey() {
		return mKey;
	}

	@Override
	public HashMap<ScopedBoogieVar, HashSet<IndexedStatement>> getDefs() {
		if (mEdge == null) {
			return new HashMap<>();
		}

		if (mDefCollector == null) {
			mDefCollector = new DefCollector(mProvider, mKey);
		}

		return mDefCollector.collect(mEdge);
	}

	@Override
	public HashMap<ScopedBoogieVar, HashSet<IndexedStatement>> getUse() {
		if (mEdge == null) {
			return new HashMap<>();
		}
		if (mUseCollector == null) {
			mUseCollector = new UseCollector(mProvider, mKey);
		}

		return mUseCollector.collect(mEdge);
	}
}
