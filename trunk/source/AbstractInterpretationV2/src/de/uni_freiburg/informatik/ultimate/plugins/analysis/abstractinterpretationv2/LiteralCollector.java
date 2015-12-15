//package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2;
//
//import java.util.ArrayDeque;
//import java.util.Collection;
//import java.util.Deque;
//import java.util.HashSet;
//import java.util.Set;
//
//import org.apache.log4j.Logger;
//
//import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVisitor;
//import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
//import de.uni_freiburg.informatik.ultimate.model.boogie.ast.RealLiteral;
//import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
//import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
//import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
//import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
//import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
//import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.RCFGEdgeVisitor;
//
///**
// * Collects int and real literals found in an RCFG. Some widening operators use
// * these.
// * 
// * @author Christopher Dillo
// */
//public class LiteralCollector extends RCFGEdgeVisitor {
//
//	private final Set<String> mLiterals;
//	private final Logger mLogger;
//	private StatementLiteralCollector mStatementLiteralCollector;
//
//	public LiteralCollector(final RootNode root, final Logger logger) {
//		mLogger = logger;
//		mLiterals = new HashSet<String>();
//		process(root.getOutgoingEdges());
//	}
//
//	/**
//	 * @deprecated This constructor was inserted by Fabian to collect literals
//	 *             from an NWA. We want to lift this to a more generic
//	 *             interface.
//	 */
//	public LiteralCollector(final INestedWordAutomaton<CodeBlock, Object> nwa, final Logger logger) {
//		mLogger = logger;
//		mLiterals = new HashSet<String>();
//		process(nwa.getAlphabet());
//	}
//
//	public Set<String> getResult() {
//		return mLiterals;
//	}
//
//	private <T extends RCFGEdge> void process(final Collection<T> edges) {
//		mStatementLiteralCollector = new StatementLiteralCollector();
//
//		final Deque<RCFGEdge> worklist = new ArrayDeque<RCFGEdge>();
//		final Set<RCFGEdge> finished = new HashSet<RCFGEdge>();
//
//		worklist.addAll(edges);
//		while (!worklist.isEmpty()) {
//			final RCFGEdge current = worklist.removeFirst();
//			if (!finished.add(current)) {
//				continue;
//			}
//			visit(current);
//			worklist.addAll(current.getTarget().getOutgoingEdges());
//		}
//		mStatementLiteralCollector = null;
//	}
//
//	@Override
//	protected void visit(StatementSequence c) {
//		super.visit(c);
//		for (final Statement s : c.getStatements()) {
//			mStatementLiteralCollector.processStatement(s);
//		}
//	}
//
//	/**
//	 * 
//	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
//	 */
//	private final class StatementLiteralCollector extends BoogieVisitor {
//
//		@Override
//		protected Statement processStatement(Statement statement) {
//			// override because we need the visibility here
//			return super.processStatement(statement);
//		}
//
//		@Override
//		protected void visit(IntegerLiteral expr) {
//			super.visit(expr);
//			if (mLiterals.add(expr.getValue())) {
//				mLogger.debug(String.format("Collected int literal \"%s\"", expr.getValue()));
//			}
//		}
//
//		@Override
//		protected void visit(RealLiteral expr) {
//			super.visit(expr);
//			if (mLiterals.add(expr.getValue())) {
//				mLogger.debug(String.format("Collected real literal \"%s\"", expr.getValue()));
//			}
//		}
//	}
//}