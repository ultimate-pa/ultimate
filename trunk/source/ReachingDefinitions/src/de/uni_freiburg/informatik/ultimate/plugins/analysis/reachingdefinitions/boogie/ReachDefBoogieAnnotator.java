package de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.boogie;

import java.util.Collection;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations.ReachDefBaseAnnotation;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations.ReachDefStatementAnnotation;

public class ReachDefBoogieAnnotator {

	private ReachDefBoogieVisitor mVisitor;

	private Collection<ReachDefStatementAnnotation> mPredecessors;
	private ReachDefStatementAnnotation mCurrent;
	private final Logger mLogger;

	public ReachDefBoogieAnnotator(Collection<ReachDefStatementAnnotation> predecessors,
			ReachDefStatementAnnotation current, Logger logger, ScopedBoogieVarBuilder builder) {
		this(predecessors, current, logger, builder, null);
	}

	public ReachDefBoogieAnnotator(Collection<ReachDefStatementAnnotation> predecessors,
			ReachDefStatementAnnotation current, Logger logger, ScopedBoogieVarBuilder builder, String key) {
		assert current != null;
		mPredecessors = predecessors;
		mCurrent = current;
		mVisitor = new ReachDefBoogieVisitor(current, builder,key);
		mLogger = logger;
	}

	/**
	 * 
	 * @return true iff annotations were changed.
	 * @throws Throwable
	 */
	public boolean annotate(Statement stmt) throws Throwable {
		ReachDefBaseAnnotation old = mCurrent.clone();
		union(mCurrent, mPredecessors);

		if (mLogger.isDebugEnabled()) {
			mLogger.debug("                                      Old Use: " + mCurrent.getUseAsString());
			mLogger.debug("                                      Old Def: " + mCurrent.getDefAsString());
		}

		mVisitor.process(stmt);

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

		for (ReachDefStatementAnnotation pre : previousRDs) {
			if (pre == current) {
				continue;
			}
			current.unionDef(pre);
		}
	}

}
