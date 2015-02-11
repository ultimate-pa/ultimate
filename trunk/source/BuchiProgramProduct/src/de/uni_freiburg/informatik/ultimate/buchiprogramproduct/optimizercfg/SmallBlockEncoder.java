package de.uni_freiburg.informatik.ultimate.buchiprogramproduct.optimizercfg;

import java.util.ArrayDeque;
import java.util.Collection;
import java.util.HashSet;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.BaseObserver;
import de.uni_freiburg.informatik.ultimate.buchiprogramproduct.ProductBacktranslator;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.normalforms.BoogieConditionWrapper;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.normalforms.ConditionTransformer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;

/**
 * Observer that performs small block encoding of a single statement RCFG.
 * 
 * The small block encoding works like this:
 * <ul>
 * <li>For each edge e := (loc,assume expr,loc') in RCFG
 * <li>Convert expr to DNF with disjuncts d1..dn
 * <li>If n>1 then for each disjunct di insert new edge (loc,assume di,loc')
 * <li>If n>1 then remove e
 * </ul>
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class SmallBlockEncoder extends BaseObserver {

	private final Logger mLogger;
	private final ProductBacktranslator mBacktranslator;

	public SmallBlockEncoder(Logger logger, ProductBacktranslator backtranslator) {
		mLogger = logger;
		mBacktranslator = backtranslator;
	}

	@Override
	public boolean process(IElement elem) throws Throwable {
		if (elem instanceof RootNode) {
			RootNode root = (RootNode) elem;

			int countDisjunctiveAssumes = 0;
			int countNewEdges = 0;

			ArrayDeque<RCFGEdge> edges = new ArrayDeque<>();
			HashSet<RCFGEdge> closed = new HashSet<>();

			ConditionTransformer<Expression> ct = new ConditionTransformer<>(new BoogieConditionWrapper());

			edges.addAll(root.getOutgoingEdges());

			while (!edges.isEmpty()) {
				RCFGEdge current = edges.removeFirst();
				if (closed.contains(current)) {
					continue;
				}
				closed.add(current);
				edges.addAll(current.getTarget().getOutgoingEdges());
				if (current instanceof StatementSequence) {
					StatementSequence ss = (StatementSequence) current;
					if (ss.getStatements().size() != 1) {
						throw new UnsupportedOperationException("StatementSequence has " + ss.getStatements().size()
								+ " statements, but SingleStatement should enforce that there is only 1.");
					}
					Statement stmt = ss.getStatements().get(0);
					if (stmt instanceof AssumeStatement) {
						AssumeStatement assume = (AssumeStatement) stmt;
						Collection<Expression> disjuncts = ct.toDnfDisjuncts(ct.rewriteNotEquals(assume.getFormula()));
						if (mLogger.isDebugEnabled() && disjuncts.size() > 1) {
							mLogger.debug("Edge " + current.hashCode() + ":");
							mLogger.debug("    has assume " + BoogiePrettyPrinter.print(assume.getFormula()));
							StringBuilder sb = new StringBuilder();
							sb.append("{");
							for (Expression dis : disjuncts) {
								sb.append(BoogiePrettyPrinter.print(dis)).append(", ");
							}
							sb.delete(sb.length() - 2, sb.length()).append("}");
							mLogger.debug("    converted to disjuncts " + sb.toString());
						}
						if (disjuncts.size() > 1) {
							countDisjunctiveAssumes++;
							for (Expression disjunct : disjuncts) {
								StatementSequence newss = new StatementSequence((ProgramPoint) current.getSource(),
										(ProgramPoint) current.getTarget(), new AssumeStatement(assume.getLocation(),
												disjunct), mLogger);
								closed.add(newss);
								countNewEdges++;
								mBacktranslator.mapEdges(newss, current);
							}
							current.disconnectSource();
							current.disconnectTarget();
						}
					}
				}
			}
			mLogger.info("Small block encoding converted " + countDisjunctiveAssumes + " assume edges to "
					+ countNewEdges + " new edges with only one disjunct");
			return false;
		}
		return true;
	}
}
