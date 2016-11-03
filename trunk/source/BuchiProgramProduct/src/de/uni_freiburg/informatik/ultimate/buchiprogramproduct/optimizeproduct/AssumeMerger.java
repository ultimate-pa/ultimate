/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE BuchiProgramProduct plug-in.
 *
 * The ULTIMATE BuchiProgramProduct plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BuchiProgramProduct plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BuchiProgramProduct plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BuchiProgramProduct plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BuchiProgramProduct plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.buchiprogramproduct.optimizeproduct;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.buchiprogramproduct.Activator;
import de.uni_freiburg.informatik.ultimate.buchiprogramproduct.preferences.PreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.normalforms.BoogieExpressionTransformer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.normalforms.NormalFormTransformer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence.Origin;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class AssumeMerger extends BaseProductOptimizer {

	private int mAssumesMerged;
	private final boolean mRewriteNotEquals;
	private final boolean mUseSBE;

	private final TransFormulaBuilder mTransFormulaBuilder;

	public AssumeMerger(final RootNode product, final IUltimateServiceProvider services,
			final IToolchainStorage storage, final SimplificationTechnique simplificationTechnique,
			final XnfConversionTechnique xnfConversionTechnique) {
		super(product, services, storage);
		mAssumesMerged = 0;
		mRewriteNotEquals = mServices.getPreferenceProvider(Activator.PLUGIN_ID)
				.getBoolean(PreferenceInitializer.OPTIMIZE_SIMPLIFY_ASSUMES_REWRITENOTEQUALS);
		mUseSBE = mServices.getPreferenceProvider(Activator.PLUGIN_ID)
				.getBoolean(PreferenceInitializer.OPTIMIZE_SIMPLIFY_ASSUMES_SBE);
		mTransFormulaBuilder =
				new TransFormulaBuilder(product, services, simplificationTechnique, xnfConversionTechnique);
	}

	@Override
	protected RootNode createResult(final RootNode root) {
		final ArrayDeque<IcfgEdge> edges = new ArrayDeque<>();
		final HashSet<IcfgEdge> closed = new HashSet<>();

		edges.addAll(root.getOutgoingEdges());

		while (!edges.isEmpty()) {
			final IcfgEdge current = edges.removeFirst();
			if (closed.contains(current)) {
				continue;
			}
			closed.add(current);
			edges.addAll(current.getTarget().getOutgoingEdges());

			if (current instanceof CodeBlock) {
				mergeEdge(root, (CodeBlock) current);
			}
		}
		mLogger.info("Merged " + mAssumesMerged + " AssumeStatements");
		return root;
	}

	private void mergeEdge(final RootNode root, final CodeBlock current) {
		final List<Statement> stmts = new StatementExtractor(mLogger).process(current);
		if (stmts.size() < 2) {
			// there is nothing to merge here
			return;
		}

		final List<Statement> newStmts = new ArrayList<>();
		List<AssumeStatement> successiveAssumes = new ArrayList<>();
		boolean successive = false;
		for (final Statement stmt : stmts) {
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

	private void createNewEdges(final RootNode root, final CodeBlock current, final List<Statement> newStmts) {
		boolean allAssumes = true;
		for (final Statement stmt : newStmts) {
			if (!(stmt instanceof AssumeStatement)) {
				allAssumes = false;
				break;
			}
		}
		if (mUseSBE && allAssumes) {
			// a new edge would contain only assumes. We check if we can split
			// them into multiple edges
			assert newStmts.size() == 1;
			final AssumeStatement stmt = (AssumeStatement) newStmts.get(0);
			final NormalFormTransformer<Expression> ct = new NormalFormTransformer<>(new BoogieExpressionTransformer());

			Expression formula = stmt.getFormula();
			if (mRewriteNotEquals) {
				formula = ct.rewriteNotEquals(formula);
			}
			final Collection<Expression> disjuncts = ct.toDnfDisjuncts(formula);
			if (disjuncts.size() > 1) {
				// yes we can
				for (final Expression disjunct : disjuncts) {
					final StatementSequence ss = mCbf.constructStatementSequence((BoogieIcfgLocation) current.getSource(),
							(BoogieIcfgLocation) current.getTarget(), new AssumeStatement(stmt.getLocation(), disjunct),
							Origin.IMPLEMENTATION);

					mTransFormulaBuilder.addTransFormula(ss);
					assert ss.getTransitionFormula() != null;
				}
				return;
			}
			// no, we cannot, just make a normal edge
		}
		final StatementSequence ss = mCbf.constructStatementSequence((BoogieIcfgLocation) current.getSource(),
				(BoogieIcfgLocation) current.getTarget(), newStmts, Origin.IMPLEMENTATION);
		mTransFormulaBuilder.addTransFormula(ss);
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Replacing first with second:");
			mLogger.debug(current);
			mLogger.debug(ss);
		}
	}

	private AssumeStatement mergeAssumes(final List<AssumeStatement> successiveAssumes) {
		final List<Expression> assumeExpressions = new ArrayList<>();
		mLogger.debug("Trying to merge the following assume statements:");
		for (final AssumeStatement stmt : successiveAssumes) {
			if (mLogger.isDebugEnabled()) {
				mLogger.debug(BoogiePrettyPrinter.print(stmt));
			}
			assumeExpressions.add(stmt.getFormula());
		}

		final BoogieExpressionTransformer bcw = new BoogieExpressionTransformer();
		final NormalFormTransformer<Expression> ct = new NormalFormTransformer<>(bcw);
		final int assumeExprSize = assumeExpressions.size();
		final Collection<Expression> disjuncts =
				new ArrayList<>(ct.toDnfDisjuncts(bcw.makeAnd(assumeExpressions.iterator())));
		final int disjunctsSize = disjuncts.size();

		if (successiveAssumes.size() > 1) {
			mAssumesMerged += successiveAssumes.size();
		} else if (successiveAssumes.size() == 1 && (assumeExprSize == disjunctsSize || disjunctsSize == 0)) {
			// there was no merging done, just return the one assumestatement
			mLogger.debug("Result: Keep it, already minimal");
			return successiveAssumes.get(0);
		}
		final AssumeStatement rtr = new AssumeStatement(null, bcw.makeOr(disjuncts.iterator()));
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Result: " + BoogiePrettyPrinter.print(rtr));
		}
		return rtr;
	}

	private static boolean collectionsEqual(final List<Statement> stmts, final List<Statement> newStmts) {
		if (stmts == null && newStmts == null) {
			return true;
		} else if (stmts != null && newStmts != null) {
			if (stmts.size() != newStmts.size()) {
				return false;
			}
			for (int i = 0; i < stmts.size(); ++i) {
				final Statement stmt = stmts.get(i);
				final Statement newStmt = newStmts.get(i);
				if (!stmt.equals(newStmt)) {
					return false;
				}
			}
			return true;
		} else {
			return false;
		}
	}

	@Override
	public boolean isGraphChanged() {
		return mAssumesMerged > 0;
	}
}
