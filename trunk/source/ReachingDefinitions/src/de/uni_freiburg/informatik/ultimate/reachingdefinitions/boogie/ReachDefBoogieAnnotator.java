package de.uni_freiburg.informatik.ultimate.reachingdefinitions.boogie;

import java.util.Collection;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.reachingdefinitions.annotations.ReachDefBaseAnnotation;
import de.uni_freiburg.informatik.ultimate.reachingdefinitions.annotations.ReachDefStatementAnnotation;
import de.uni_freiburg.informatik.ultimate.reachingdefinitions.plugin.Activator;

public class ReachDefBoogieAnnotator {

	private ReachDefBoogieVisitor mVisitor;

	private Collection<ReachDefStatementAnnotation> mPredecessors;
	private ReachDefStatementAnnotation mCurrent;
	private Logger mLogger;

	public ReachDefBoogieAnnotator(Collection<ReachDefStatementAnnotation> predecessors,
			ReachDefStatementAnnotation current) {
		assert current != null;
		mPredecessors = predecessors;
		mCurrent = current;
		mVisitor = new ReachDefBoogieVisitor(current);
		mLogger = Activator.getLogger();
	}

	/**
	 * 
	 * @return true iff annotations were changed.
	 * @throws Throwable
	 */
	public boolean annotate(Statement stmt) throws Throwable {
		ReachDefBaseAnnotation old = mCurrent.clone();
		assert old.equals(ReachDefStatementAnnotation.getAnnotation(stmt)) && old.equals(mCurrent);
		union(mCurrent, mPredecessors);
		mVisitor.process(stmt);
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("			                              Old: " + old);
		}

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
