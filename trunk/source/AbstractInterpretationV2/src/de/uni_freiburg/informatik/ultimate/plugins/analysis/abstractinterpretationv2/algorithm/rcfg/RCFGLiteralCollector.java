/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg;

import java.math.BigDecimal;
import java.util.ArrayDeque;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieVisitor;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SubTermFinder;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.ILiteralCollector;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.generic.LiteralCollection;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.util.AbsIntUtil;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.RCFGEdgeVisitor;

/**
 * Collects literals of type int or real found in an RCFG. Some widening operators can use these.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class RCFGLiteralCollector extends RCFGEdgeVisitor implements ILiteralCollector {

	private final Set<String> mLiterals;
	private final Set<BigDecimal> mNumberLiterals;
	private final StatementLiteralCollector mStatementLiteralCollector;
	private final SubTermFinder mSubTermFinder;
	private final LiteralCollection mLiteralCollection;

	public RCFGLiteralCollector(final IIcfg<?> root) {
		mLiterals = new HashSet<>();
		mNumberLiterals = new HashSet<>();
		mStatementLiteralCollector = new StatementLiteralCollector();
		mSubTermFinder = new SubTermFinder(RCFGLiteralCollector::isConstant);
		process(RcfgUtils.getInitialEdges(root));
		mLiteralCollection = new LiteralCollection(mNumberLiterals);
	}

	private static boolean isConstant(final Term term) {
		return SmtUtils.isConstant(term) || term instanceof ConstantTerm;
	}

	@Override
	public LiteralCollection getLiteralCollection() {
		return mLiteralCollection;
	}

	public Collection<BigDecimal> getNumberLiterals() {
		return Collections.unmodifiableCollection(mNumberLiterals);
	}

	private <T extends IcfgEdge> void process(final Collection<T> edges) {
		final Deque<IcfgEdge> worklist = new ArrayDeque<>();
		final Set<IcfgEdge> finished = new HashSet<>();

		worklist.addAll(edges);
		while (!worklist.isEmpty()) {
			final IcfgEdge current = worklist.removeFirst();
			if (!finished.add(current)) {
				continue;
			}
			visit(current.getLabel());
			worklist.addAll(current.getTarget().getOutgoingEdges());
		}
	}

	@Override
	protected void visit(final StatementSequence c) {
		super.visit(c);
		for (final Statement s : c.getStatements()) {
			mStatementLiteralCollector.processStatement(s);
		}
	}

	@Override
	protected void visit(final Call c) {
		super.visit(c);
		mStatementLiteralCollector.processStatement(c.getCallStatement());
	}

	@Override
	protected void visit(final IIcfgCallTransition<?> e) {
		super.visit(e);
		addConstantsFromTerms(e.getLocalVarsAssignment().getClosedFormula());
	}

	@Override
	protected void visit(final IIcfgInternalTransition<?> e) {
		super.visit(e);
		addConstantsFromTerms(e.getTransformula().getClosedFormula());
	}

	private void addConstantsFromTerms(final Term t) {
		final Set<Term> results = mSubTermFinder.findMatchingSubterms(t);
		for (final Term constTerm : results) {
			if (constTerm instanceof ConstantTerm) {
				final Rational rat = SmtUtils.convertConstantTermToRational((ConstantTerm) constTerm);
				mNumberLiterals.add(new BigDecimal(rat.numerator()).divide(new BigDecimal(rat.denominator())));
			}
		}
	}

	@Override
	public String toString() {
		return getLiteralCollection().toString();
	}

	/**
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 */
	private final class StatementLiteralCollector extends BoogieVisitor {

		private boolean mNegate = false;

		@Override
		protected Statement processStatement(final Statement statement) {
			// override because we need the visibility here
			return super.processStatement(statement);
		}

		@Override
		protected void visit(final IntegerLiteral expr) {
			super.visit(expr);
			final StringBuilder litBuilder = new StringBuilder();
			if (mNegate) {
				litBuilder.append("-");
			}
			litBuilder.append(expr.getValue());
			mLiterals.add(litBuilder.toString());

			BigDecimal val = AbsIntUtil.sanitizeBigDecimalValue(expr.getValue());
			if (mNegate) {
				val = val.negate();
			}
			mNumberLiterals.add(val);

			mNegate = false;
		}

		@Override
		protected void visit(final UnaryExpression expr) {
			super.visit(expr);
			if (expr.getOperator() == Operator.ARITHNEGATIVE) {
				mNegate = !mNegate;
			}
		}

		@Override
		protected void visit(final RealLiteral expr) {
			super.visit(expr);
			final StringBuilder litBuilder = new StringBuilder();
			if (mNegate) {
				litBuilder.append("-");
			}
			litBuilder.append(expr.getValue());
			mLiterals.add(litBuilder.toString());

			BigDecimal val = AbsIntUtil.sanitizeBigDecimalValue(expr.getValue());
			if (mNegate) {
				val = val.negate();
			}
			mNumberLiterals.add(val);

			mNegate = false;
		}
	}
}