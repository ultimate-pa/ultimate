package de.uni_freiburg.informatik.ultimate.irsdependencies.reachdef;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;

public class ReachingDefinitionsGenerator {

	private ReachingDefinitionsVisitor mVisitor;
	
	private List<ReachingDefinitionsStatementAnnotation> mPredecessors;
	private ReachingDefinitionsStatementAnnotation mCurrent;
	
	public ReachingDefinitionsGenerator(List<ReachingDefinitionsStatementAnnotation> predecessors, ReachingDefinitionsStatementAnnotation current){
		assert predecessors != null;
		assert current != null;
		mPredecessors = predecessors;
		mCurrent = current;
		mVisitor = new ReachingDefinitionsVisitor(current);
	}
	
	
	/**
	 * 
	 * @return true iff annotations were changed. 
	 * @throws Throwable 
	 */
	public boolean generate(Statement stmt) throws Throwable{
		boolean rtr = prepareCurrentRDDef(mPredecessors, mCurrent);
		rtr = mVisitor.process(stmt) || rtr;
		return rtr;
	}
	
	
	/**
	 * 
	 * @param previousRDs
	 * @param current
	 * @return true iff current's Def set changed
	 */
	private boolean prepareCurrentRDDef(List<ReachingDefinitionsStatementAnnotation> previousRDs,
			ReachingDefinitionsStatementAnnotation current) {
		assert previousRDs != null;
		assert current != null;

		boolean rtr = false;

		for (ReachingDefinitionsStatementAnnotation pre : previousRDs) {
			rtr = current.unionDef(pre) || rtr;
		}
//		return rtr;
		//TODO: Do this right
		return false;

	}
	
}
