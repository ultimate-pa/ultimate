/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE BlockEncodingV2 plug-in.
 *
 * The ULTIMATE BlockEncodingV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BlockEncodingV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BlockEncodingV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BlockEncodingV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BlockEncodingV2 plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.blockencoding.encoding;

import java.util.ArrayDeque;
import java.util.Collection;
import java.util.Deque;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.core.lib.observers.BaseObserver;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.normalforms.BoogieExpressionTransformer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.normalforms.NormalFormTransformer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.blockencoding.BlockEncodingBacktranslator;
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
 * @deprecated SmallBlockEncoder has to be rewritten for transforumlas.
 */
@Deprecated
public class SmallBlockEncoder extends BaseObserver {

	private final ILogger mLogger;
	private final BlockEncodingBacktranslator mBacktranslator;
	private final boolean mRewriteAssumes;
	private final IUltimateServiceProvider mServices;
	private final SimplificationTechnique mSimplificationTechnique;
	private final XnfConversionTechnique mXnfConversionTechnique;

	public SmallBlockEncoder(final ILogger logger, final BlockEncodingBacktranslator backtranslator,
			final boolean rewriteAssumes, final IUltimateServiceProvider services,
			final SimplificationTechnique simplTech, final XnfConversionTechnique xnfConfTech) {
		mLogger = logger;
		mBacktranslator = backtranslator;
		mRewriteAssumes = rewriteAssumes;
		mServices = services;
		mSimplificationTechnique = simplTech;
		mXnfConversionTechnique = xnfConfTech;
	}

	@Override
	public boolean process(final IElement elem) throws Throwable {
		if (!(elem instanceof IIcfg<?>)) {
			return true;
		}

		final IIcfg<?> icfg = (IIcfg<?>) elem;
		final Deque<IcfgEdge> edges = new ArrayDeque<>();
		final Set<IcfgEdge> closed = new HashSet<>();
		final NormalFormTransformer<Expression> ct = new NormalFormTransformer<>(new BoogieExpressionTransformer());
		// final IcfgEdgeBuilder edgeBuilder = new IcfgEdgeBuilder(icfg.getCfgSmtToolkit(), mServices,
		// mSimplificationTechnique, mXnfConversionTechnique);

		int countDisjunctiveAssumes = 0;
		int countNewEdges = 0;

		edges.addAll(IcfgUtils.extractStartEdges(icfg));

		while (!edges.isEmpty()) {
			final IcfgEdge current = edges.removeFirst();
			if (closed.contains(current)) {
				continue;
			}
			closed.add(current);
			edges.addAll(current.getTarget().getOutgoingEdges());
			if (mLogger.isDebugEnabled()) {
				printDebugLogCurrentEdge(current);
			}

			if (current instanceof StatementSequence) {
				final StatementSequence ss = (StatementSequence) current;
				if (ss.getStatements().size() != 1) {
					throw new AssertionError("StatementSequence has " + ss.getStatements().size()
							+ " statements, but SingleStatement should enforce that there is only 1.");
				}
				final Statement stmt = ss.getStatements().get(0);
				if (stmt instanceof AssumeStatement) {
					final AssumeStatement assume = (AssumeStatement) stmt;
					Expression expr = assume.getFormula();
					if (mRewriteAssumes) {
						expr = ct.rewriteNotEquals(expr);
					}

					if (mLogger.isDebugEnabled()) {
						printDebugLogAssume(assume, expr);
					}
					final Collection<Expression> disjuncts = ct.toDnfDisjuncts(expr);
					if (mLogger.isDebugEnabled()) {
						printDebugLogDisjuncts(disjuncts);
					}
					if (disjuncts.size() > 1) {
						countDisjunctiveAssumes++;
						for (final Expression disjunct : disjuncts) {
							final StatementSequence newss = null;
							// final StatementSequence newss = edgeBuilder.constructStatementSequence(
							// (BoogieIcfgLocation) current.getSource(), (BoogieIcfgLocation) current.getTarget(),
							// new AssumeStatement(assume.getLocation(), disjunct));
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
		mLogger.info("Small block encoding converted " + countDisjunctiveAssumes + " assume edges to " + countNewEdges
				+ " new edges with only one disjunct");
		return false;
	}

	private void printDebugLogCurrentEdge(final IcfgEdge current) {
		mLogger.debug("Processing edge " + current.hashCode() + ":");
		mLogger.debug("    " + current);
	}

	private void printDebugLogAssume(final AssumeStatement assume, final Expression expr) {
		mLogger.debug("    has assume " + BoogiePrettyPrinter.print(assume.getFormula()));
		if (mRewriteAssumes) {
			mLogger.debug("    after rewrite " + BoogiePrettyPrinter.print(expr));
		}
	}

	private void printDebugLogDisjuncts(final Collection<Expression> disjuncts) {
		if (disjuncts.size() > 1) {
			final StringBuilder sb = new StringBuilder();
			sb.append("{");
			for (final Expression dis : disjuncts) {
				sb.append(BoogiePrettyPrinter.print(dis)).append(", ");
			}
			sb.delete(sb.length() - 2, sb.length()).append("}");
			mLogger.debug("    converted to disjuncts " + sb.toString());
		} else {
			mLogger.debug("    only one disjunct " + BoogiePrettyPrinter.print(disjuncts.iterator().next()));
		}
	}
}
