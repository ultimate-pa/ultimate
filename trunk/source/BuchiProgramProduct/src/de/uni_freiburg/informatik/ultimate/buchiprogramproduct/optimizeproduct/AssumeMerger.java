package de.uni_freiburg.informatik.ultimate.buchiprogramproduct.optimizeproduct;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.normalforms.BoogieConditionWrapper;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.normalforms.ConditionTransformer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ParallelComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence.Origin;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.RCFGEdgeVisitor;

public class AssumeMerger extends BaseProductOptimizer {

	private int mAssumesMerged;
	private IUltimateServiceProvider mServices;

	public AssumeMerger(RootNode product, IUltimateServiceProvider services) {
		super(product, services);
		mLogger.info("Merged " + mAssumesMerged + " AssumeStatements");
	}

	@Override
	protected void init(RootNode root, IUltimateServiceProvider services) {
		mAssumesMerged = 0;
		mServices = services;
	}

	@Override
	protected RootNode process(RootNode root) {
		ArrayDeque<RCFGEdge> edges = new ArrayDeque<>();
		HashSet<RCFGEdge> closed = new HashSet<>();

		edges.addAll(root.getOutgoingEdges());

		while (!edges.isEmpty()) {
			RCFGEdge current = edges.removeFirst();
			if (closed.contains(current)) {
				continue;
			}
			closed.add(current);
			edges.addAll(current.getTarget().getOutgoingEdges());

			if (current instanceof CodeBlock) {
				mergeEdge(root, (CodeBlock) current);
			}
		}
		return root;
	}

	private void mergeEdge(RootNode root, CodeBlock current) {
		List<Statement> stmts = new StatementExtractor().process(current);
		if (stmts.size() < 2) {
			// there is nothing to merge here
			return;
		}

		List<Statement> newStmts = new ArrayList<>();
		List<AssumeStatement> successiveAssumes = new ArrayList<>();
		boolean successive = false;
		for (Statement stmt : stmts) {
			if (stmt instanceof AssumeStatement) {
				successive = true;
				successiveAssumes.add((AssumeStatement) stmt);
			} else if (successive) {
				// this is the end of a succession of assume statements, now
				// process them.
				successive = false;
				newStmts.add(mergeAssumes(successiveAssumes));
				newStmts.add(stmt);
				successiveAssumes = new ArrayList<>();
			} else {
				newStmts.add(stmt);
			}
		}

		if (!successiveAssumes.isEmpty()) {
			// the edge ends with assumes
			newStmts.add(mergeAssumes(successiveAssumes));
		}

		if (!collectionsEqual(stmts, newStmts)) {
			// there were optimizations, replace the edge with new edge(s)
			createNewEdges(root, current, newStmts);
			// remove old edge
			current.disconnectSource();
			current.disconnectTarget();
		}

	}

	private void createNewEdges(RootNode root, CodeBlock current, List<Statement> newStmts) {
		boolean allAssumes = true;
		for (Statement stmt : newStmts) {
			if (!(stmt instanceof AssumeStatement)) {
				allAssumes = false;
				break;
			}
		}
		if (allAssumes) {
			// a new edge would contain only assumes. We check if we can split
			// them into multiple edges
			assert newStmts.size() == 1;
			AssumeStatement stmt = (AssumeStatement) newStmts.get(0);
			BoogieConditionWrapper bcw = new BoogieConditionWrapper();
			ConditionTransformer<Expression> ct = new ConditionTransformer<>(bcw);
			Collection<Expression> disjuncts = ct.toDnfDisjuncts(stmt.getFormula());
			if (disjuncts.size() > 1) {
				// yes we can
				for (Expression disjunct : disjuncts) {
					StatementSequence ss = new StatementSequence((ProgramPoint) current.getSource(),
							(ProgramPoint) current.getTarget(), new AssumeStatement(stmt.getLocation(), disjunct),
							Origin.IMPLEMENTATION, mLogger);
					generateTransFormula(root, ss);
				}
				return;
			}
			// no, we cannot, just make a normal edge
		}
		StatementSequence ss = new StatementSequence((ProgramPoint) current.getSource(),
				(ProgramPoint) current.getTarget(), newStmts, Origin.IMPLEMENTATION, mLogger);
		generateTransFormula(root, ss);
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Replacing first with second:");
			mLogger.debug(current);
			mLogger.debug(ss);
		}
	}

	private AssumeStatement mergeAssumes(List<AssumeStatement> successiveAssumes) {
		List<Expression> assumeExpressions = new ArrayList<>();
		mLogger.debug("Trying to merge the following assume statements:");
		for (AssumeStatement stmt : successiveAssumes) {
			if (mLogger.isDebugEnabled()) {
				mLogger.debug(BoogiePrettyPrinter.print(stmt));
			}
			assumeExpressions.add(stmt.getFormula());
		}
		
		BoogieConditionWrapper bcw = new BoogieConditionWrapper();
		ConditionTransformer<Expression> ct = new ConditionTransformer<>(bcw);
		int assumeExprSize = assumeExpressions.size();
		Collection<Expression> disjuncts = new ArrayList<>(ct.toDnfDisjuncts(bcw.makeAnd(assumeExpressions.iterator())));
		int disjunctsSize = disjuncts.size();

		if (successiveAssumes.size() > 1) {
			mAssumesMerged += successiveAssumes.size();
		} else if (successiveAssumes.size() == 1 && (assumeExprSize == disjunctsSize || disjunctsSize == 0)) {
			// there was no merging done, just return the one assumestatement
			mLogger.debug("Result: Keep it, already minimal");
			return successiveAssumes.get(0);
		}
		AssumeStatement rtr = new AssumeStatement(null, bcw.makeOr(disjuncts.iterator()));
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Result: " + BoogiePrettyPrinter.print(rtr));
		}
		return rtr;
	}

	private boolean collectionsEqual(List<Statement> stmts, List<Statement> newStmts) {
		if (stmts == null && newStmts == null) {
			return true;
		} else if (stmts != null && newStmts != null) {
			if (stmts.size() != newStmts.size()) {
				return false;
			} else {
				for (int i = 0; i < stmts.size(); ++i) {
					Statement stmt = stmts.get(i);
					Statement newStmt = newStmts.get(i);
					if (!stmt.equals(newStmt)) {
						return false;
					}
				}
				return true;
			}
		} else {
			return false;
		}
	}

	private void generateTransFormula(RootNode root, StatementSequence ss) {
		Boogie2SMT b2smt = root.getRootAnnot().getBoogie2SMT();
		TransFormulaBuilder tfb = new TransFormulaBuilder(b2smt, mServices);
		tfb.addTransitionFormulas((CodeBlock) ss, ((ProgramPoint) ss.getSource()).getProcedure());
		assert ss.getTransitionFormula() != null;
	}

	@Override
	public boolean IsGraphChanged() {
		return mAssumesMerged > 0;
	}

	private class StatementExtractor extends RCFGEdgeVisitor {

		private List<Statement> mStatements;

		private List<Statement> process(RCFGEdge edge) {
			mStatements = new ArrayList<>();
			visit(edge);
			return mStatements;
		}

		@Override
		protected void visit(ParallelComposition c) {
			throw new UnsupportedOperationException("Cannot merge ParallelComposition");
		}

		@Override
		protected void visit(StatementSequence c) {
			mStatements.addAll(c.getStatements());
			super.visit(c);
		}
	}

}
