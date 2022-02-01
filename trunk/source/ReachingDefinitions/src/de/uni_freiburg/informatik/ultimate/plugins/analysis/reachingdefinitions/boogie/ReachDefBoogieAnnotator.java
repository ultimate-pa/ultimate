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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.boogie;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations.ReachDefBaseAnnotation;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations.ReachDefStatementAnnotation;

public class ReachDefBoogieAnnotator {

	private final ReachDefBoogieVisitor mVisitor;

	private final Collection<ReachDefStatementAnnotation> mPredecessors;
	private final ReachDefStatementAnnotation mCurrent;
	private final ILogger mLogger;

	public ReachDefBoogieAnnotator(Collection<ReachDefStatementAnnotation> predecessors,
			ReachDefStatementAnnotation current, ILogger logger, ScopedBoogieVarBuilder builder) {
		this(predecessors, current, logger, builder, null);
	}

	public ReachDefBoogieAnnotator(Collection<ReachDefStatementAnnotation> predecessors,
			ReachDefStatementAnnotation current, ILogger logger, ScopedBoogieVarBuilder builder, String key) {
		assert current != null;
		mPredecessors = predecessors;
		mCurrent = current;
		mVisitor = new ReachDefBoogieVisitor(current, builder,key);
		mLogger = logger;
	}

	/**
	 * 
	 * @param transFormula 
	 * @return true iff annotations were changed.
	 * @throws Throwable
	 */
	public boolean annotate(Statement stmt, UnmodifiableTransFormula transFormula) throws Throwable {
		final ReachDefBaseAnnotation old = mCurrent.clone();
		union(mCurrent, mPredecessors);

		if (mLogger.isDebugEnabled()) {
			mLogger.debug("                                      Old Use: " + mCurrent.getUseAsString());
			mLogger.debug("                                      Old Def: " + mCurrent.getDefAsString());
		}

		mVisitor.process(stmt,transFormula);

		return !old.equals(mCurrent);
	}

	/**
	 * Changes current s.t. it contains the union of current's defs with the
	 * defs of previousRDs.
	 * 
	 * @param current
	 * @param previousRDs
	 */
	private void union(ReachDefStatementAnnotation current, Collection<ReachDefStatementAnnotation> previousRDs) {
		if (previousRDs == null) {
			return;
		}

		assert previousRDs != null;
		assert current != null;

		for (final ReachDefStatementAnnotation pre : previousRDs) {
			if (pre == current) {
				continue;
			}
			current.unionDef(pre);
		}
	}

}
