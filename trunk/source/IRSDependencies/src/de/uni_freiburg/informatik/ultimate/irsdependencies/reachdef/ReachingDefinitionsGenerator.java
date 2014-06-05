package de.uni_freiburg.informatik.ultimate.irsdependencies.reachdef;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;

public class ReachingDefinitionsGenerator {

	private ReachingDefinitionsVisitor mVisitor;

	private List<ReachingDefinitionsStatementAnnotation> mLoopPredecessors;
	private ReachingDefinitionsStatementAnnotation mStraightlinePredecessors;
	private ReachingDefinitionsStatementAnnotation mCurrent;

	public ReachingDefinitionsGenerator(List<ReachingDefinitionsStatementAnnotation> loopPredecessors,
			ReachingDefinitionsStatementAnnotation straightlinePredecessor,
			ReachingDefinitionsStatementAnnotation current) {
		assert current != null;
		mLoopPredecessors = loopPredecessors;
		mStraightlinePredecessors = straightlinePredecessor;
		mCurrent = current;
		mVisitor = new ReachingDefinitionsVisitor(current);
	}

	/**
	 * 
	 * @return true iff annotations were changed.
	 * @throws Throwable
	 */
	public boolean generate(Statement stmt) throws Throwable {
//		ReachingDefinitionsStatementAnnotation copy;

		if (mStraightlinePredecessors == null) {
			// we have only loop predecessors, and therefore need to consider
			// them for fixpoint calculation
//			copy = mCurrent.clone();
			considerLoops(mLoopPredecessors, mCurrent);
		} else {
			// we have straightline predecessors, and therefore ignore loop
			// predecessors for fixpoint calculation
			considerLoops(mLoopPredecessors, mCurrent);
//			copy = mCurrent.clone();
			mCurrent.unionDef(mStraightlinePredecessors);
		}
//		copy = mCurrent.clone();
		mVisitor.process(stmt);

		//TODO: Fix this 
//		boolean rtr = !copy.equals(mCurrent);
		return false;
	}

	private void considerLoops(List<ReachingDefinitionsStatementAnnotation> previousRDs,
			ReachingDefinitionsStatementAnnotation current) {
		if (previousRDs == null) {
			return;
		}

		assert previousRDs != null;
		assert current != null;

		for (ReachingDefinitionsStatementAnnotation pre : previousRDs) {
			current.unionDef(pre);
		}
	}

}
