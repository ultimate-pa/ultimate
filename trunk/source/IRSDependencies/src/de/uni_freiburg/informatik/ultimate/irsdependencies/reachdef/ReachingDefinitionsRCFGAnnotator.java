package de.uni_freiburg.informatik.ultimate.irsdependencies.reachdef;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.Queue;

import de.uni_freiburg.informatik.ultimate.irsdependencies.observers.BaseObserver;
import de.uni_freiburg.informatik.ultimate.irsdependencies.rcfg.visitors.RCFGEdgeVisitor;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;

/**
 * 
 * {@link ReachingDefinitionsRCFGAnnotator} computes a DefUse set that is
 * expressed as {@link ReachingDefinitionsStatementAnnotation} annotation for
 * each edge of an RCFG.
 * 
 * It makes the following assumptions:
 * <ul>
 * <li>A
 * </ul>
 * 
 * @author dietsch
 * 
 */
public class ReachingDefinitionsRCFGAnnotator extends BaseObserver {

	@Override
	public boolean process(IElement root) throws Throwable {
		if (root instanceof RootNode) {
			process((RootNode) root);
		}
		return false;
	}

	private void process(RootNode node) throws Throwable {
		Queue<RCFGEdge> remaining = new LinkedList<>();
		for (RCFGEdge next : node.getOutgoingEdges()) {
			remaining.add(next);
		}

		while (!remaining.isEmpty()) {
			RCFGEdge current = remaining.poll();
			Visitor v = new Visitor();

			if (!v.process(current)) {
				for (RCFGEdge next : current.getTarget().getOutgoingEdges()) {
					remaining.add(next);
				}
			}
		}
	}

	private class Visitor extends RCFGEdgeVisitor {

		private boolean mFixpointReached;

		/**
		 * 
		 * @param e
		 * @return true iff a fixpoint was reached
		 */
		public boolean process(RCFGEdge e) {
			mFixpointReached = true;
			visit(e);
			return mFixpointReached;
		}

		@Override
		protected void visit(RootEdge e) {
			// root edges are never on a cycle, and we want to expand the
			// following edges
			mFixpointReached = false;
			super.visit(e);
		}

		@Override
		protected void visit(CodeBlock c) {
			ReachingDefinitionsEdgeAnnotation annot = ReachingDefinitionsEdgeAnnotation.getAnnotation(c);
			if (annot == null) {
				annot = new ReachingDefinitionsEdgeAnnotation(c);
				annot.annotate(c);
			}
			super.visit(c);
		}

		@Override
		protected void visit(StatementSequence edge) {
			boolean somethingChanged = false;

			for (Statement s : edge.getStatements()) {
				ReachingDefinitionsStatementAnnotation annot = ReachingDefinitionsStatementAnnotation.getAnnotation(s);
				if (annot == null) {
					annot = new ReachingDefinitionsStatementAnnotation();
					annot.annotate(s);
					// if we need a new annotation it is definitely not a
					// fixpoint
					somethingChanged = true;
				}
				ReachingDefinitionsGenerator generator = createGenerator(edge, s, annot);
				try {
					somethingChanged = generator.generate(s) || somethingChanged;
				} catch (Throwable e) {
					// Fail fast after fatal error
					sLogger.fatal("Fatal error occured", e);
					mFixpointReached = true;
					return;
				}
			}

			mFixpointReached = !somethingChanged && mFixpointReached;

			super.visit(edge);
		}

		/**
		 * 
		 * @param currentSeq
		 *            The statement sequence we currently process
		 * @param currentStmt
		 *            The statement of the sequence we currently process
		 * @param stmtAnnotation
		 *            The {@link ReachingDefinitionsStatementAnnotation}
		 *            annotation of currentStmt
		 * @return A generator that considers (a) where we are in the statement
		 *         sequence and (b) loops and stuff.
		 */
		private ReachingDefinitionsGenerator createGenerator(StatementSequence currentSeq, Statement currentStmt,
				ReachingDefinitionsStatementAnnotation stmtAnnotation) {
			List<ReachingDefinitionsStatementAnnotation> loopPredecessors = getPreceedingEdges(currentSeq);
			int currentIndex = currentSeq.getStatements().indexOf(currentStmt);
			if (currentIndex != 0) {
				// its not the first statement, so we can stay inside the
				// sequence
				return new ReachingDefinitionsGenerator(loopPredecessors,
						(ReachingDefinitionsStatementAnnotation) ReachingDefinitionsStatementAnnotation
								.getAnnotation(currentSeq.getStatements().get(currentIndex - 1)), stmtAnnotation);
			} else {
				// it is the first statement; the predecessors are the last
				// statements from before.
				return new ReachingDefinitionsGenerator(loopPredecessors, null, stmtAnnotation);
			}
		}

		private List<ReachingDefinitionsStatementAnnotation> getPreceedingEdges(StatementSequence currentSeq) {
			List<ReachingDefinitionsStatementAnnotation> rtr = new ArrayList<ReachingDefinitionsStatementAnnotation>();
			RCFGNode currentNode = currentSeq.getSource();

			if (currentNode == null) {
				sLogger.debug("Source is null: "+currentSeq);
				return rtr;
			}
			for (RCFGEdge pre : currentNode.getIncomingEdges()) {
				sLogger.debug(currentSeq + " preceeded by " + pre);

				if (pre instanceof StatementSequence) {
					StatementSequence stmtSeq = (StatementSequence) pre;
					ReachingDefinitionsStatementAnnotation annot = ReachingDefinitionsStatementAnnotation
							.getAnnotation(stmtSeq.getStatements().get(stmtSeq.getStatements().size() - 1));
					if (annot != null) {
						rtr.add(annot);
					}
				}
			}
			return rtr;
		}
	}
}
