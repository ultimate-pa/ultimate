/*
 * Copyright (C) 2015-2016 Claus Schaetzle (schaetzc@informatik.uni-freiburg.de)
 * Copyright (C) 2015-2016 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import java.math.BigDecimal;
import java.math.RoundingMode;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieVisitor;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.IBoogieSymbolTableVariableProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval.IntervalDomainState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval.IntervalPostOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util.typeutils.TypeUtils;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.util.AbsIntUtil;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlockFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence.Origin;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Part of the {@link OctPostOperator}, specialized for the {@link AssumeStatement}.
 *
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class OctAssumeProcessor {

	/** Post operator. */
	private final OctPostOperator mPostOp;
	private final ILogger mLogger;
	private final IAbstractPostOperator<IntervalDomainState, IcfgEdge> mIntervalPostOperator;
	private final CodeBlockFactory mCodeBlockFactory;
	private final IBoogieSymbolTableVariableProvider mVariableProvider;

	public OctAssumeProcessor(final ILogger logger, final OctPostOperator postOperator,
			final IAbstractPostOperator<IntervalDomainState, IcfgEdge> fallBackPostOperator,
			final CodeBlockFactory codeBlockFactory, final IBoogieSymbolTableVariableProvider variableProvider) {
		mPostOp = postOperator;
		mLogger = logger;
		mIntervalPostOperator = fallBackPostOperator;
		mCodeBlockFactory = codeBlockFactory;
		mVariableProvider = variableProvider;
	}

	/**
	 * Assume an expression.
	 *
	 * @param assumption
	 *            Expression to be assumed
	 * @param oldStates
	 *            Pre-states -- may be modified in-place.
	 * @return Post-states
	 */
	public List<OctDomainState> assume(final Expression assumption, final List<OctDomainState> oldStates) {
		return processBooleanOperations(assumption, false, oldStates);
	}

	/**
	 * Assume an boolean expression.
	 *
	 * @param expr
	 *            Boolean expression to be assumed.
	 * @param isNegated
	 *            The expression was inside a logical negation ("x < y" will be "x >= y").
	 * @param oldStates
	 *            Pre-states -- may be modified in-place.
	 * @return Post-states
	 */
	private List<OctDomainState> processBooleanOperations(final Expression expr, final boolean isNegated,
			final List<OctDomainState> oldStates) {

		assert TypeUtils.isBoolean(expr.getType()) : "Expression " + BoogiePrettyPrinter.print(expr)
				+ " is not boolean";

		if (expr instanceof BooleanLiteral) {
			if (((BooleanLiteral) expr).getValue() ^ isNegated) {
				return oldStates; // assume true
			}
			return new ArrayList<>(); // assume false

		} else if (expr instanceof IdentifierExpression) {
			final IProgramVarOrConst var = mPostOp.getBoogieVar((IdentifierExpression) expr);
			final BoolValue value = BoolValue.get(!isNegated);
			oldStates.forEach(s -> s.assumeBooleanVar(var, value));
			return oldStates;
		} else if (expr instanceof UnaryExpression) {
			final UnaryExpression unExpr = (UnaryExpression) expr;

			switch (unExpr.getOperator()) {
			case LOGICNEG:
				return processBooleanOperations(unExpr.getExpr(), !isNegated, oldStates);
			case OLD:
				return oldStates; // safe over-approximation
			default:
				throw new UnsupportedOperationException("Unknown, unsupported or mistyped expression: " + expr);
			}

		} else if (expr instanceof BinaryExpression) {
			final BinaryExpression binExpr = (BinaryExpression) expr;
			final Expression left = binExpr.getLeft();
			final Expression right = binExpr.getRight();

			switch (binExpr.getOperator()) {
			case LOGICAND:
				return isNegated ? assumeOr(left, true, right, true, oldStates)
						: assumeAnd(left, false, right, false, oldStates);
			case LOGICOR:
				return isNegated ? assumeAnd(left, true, right, true, oldStates)
						: assumeOr(left, false, right, false, oldStates);
			case LOGICIMPLIES:
				// left => right
				return isNegated ? assumeAnd(left, false, right, true, oldStates)
						: assumeOr(left, true, right, false, oldStates);
			case LOGICIFF:
				// left <=> right
				return assumeIff(left, right, isNegated, oldStates);
			case COMPEQ:
			case COMPNEQ:
			case COMPGEQ:
			case COMPGT:
			case COMPLEQ:
			case COMPLT:
			case COMPPO:
				if (TypeUtils.isNumeric(left.getType())) {
					return processNumericRelation(binExpr, isNegated, oldStates);
				} else if (TypeUtils.isBoolean(left.getType())) {
					return processBooleanRelation(binExpr, isNegated, oldStates);
				} else {
					// unsupported relation (e.g. array == array)
					return oldStates; // safe over-approximation
				}
			default:
				throw new UnsupportedOperationException("Unknown, unsupported or mistyped expression: " + expr);
			}

		} else if (expr instanceof IfThenElseExpression) {
			final IfThenElseExpression ie = (IfThenElseExpression) expr;
			// isNegated refers to the then and else part of the IfThenElseExpressions -- condition is not affected
			final Expression condition = ie.getCondition();
			final Expression notCondition = mPostOp.getExprTransformer().logicNegCached(condition);
			final Expression thenPart = ie.getThenPart();
			final Expression elsePart = ie.getElsePart();
			return mPostOp.splitF(oldStates,
					stateList -> processBooleanOperations(thenPart, isNegated, assume(condition, stateList)),
					stateList -> processBooleanOperations(elsePart, isNegated, assume(notCondition, stateList)));
		} else {
			// unknown expression (ArrayAccessExpression, FunctionApplication, QuantifierExpression, ...)
			return oldStates; // safe over-approximation

		}
	}

	/**
	 * Assume the logical conjunction of the expressions {@code left} and {@code right}
	 *
	 * @param left
	 *            First expression to be assumed.
	 * @param negLeft
	 *            Negate the first expression.
	 * @param right
	 *            Second expression to be assumed.
	 * @param negRight
	 *            Negate the second expression.
	 * @param oldStates
	 *            Pre-states -- may be modified in-place.
	 * @return Post-states
	 */
	private List<OctDomainState> assumeAnd(final Expression left, final boolean negLeft, final Expression right,
			final boolean negRight, List<OctDomainState> oldStates) {

		oldStates = processBooleanOperations(left, negLeft, oldStates);
		oldStates = processBooleanOperations(right, negRight, oldStates);
		return oldStates;
	}

	/**
	 * Assume the logical disjunction of the expressions {@code left} and {@code right}
	 *
	 * @param left
	 *            First expression to be assumed.
	 * @param negLeft
	 *            Negate the first expression.
	 * @param right
	 *            Second expression to be assumed.
	 * @param negRight
	 *            Negate the second expression.
	 * @param oldStates
	 *            Pre-states -- may be modified in-place.
	 * @return Post-states
	 */
	private List<OctDomainState> assumeOr(final Expression left, final boolean negLeft, final Expression right,
			final boolean negRight, final List<OctDomainState> oldStates) {

		return mPostOp.splitF(oldStates, statesBeforeOr -> processBooleanOperations(left, negLeft, statesBeforeOr),
				statesBeforeOr -> processBooleanOperations(right, negRight, statesBeforeOr));
	}

	/**
	 * Assume the logical equivalence ("if and only if") of the expressions {@code left} and {@code right}
	 *
	 * @param left
	 *            First expression to be assumed.
	 * @param right
	 *            Second expression to be assumed.
	 * @param negIff
	 *            Negate the equivalence.
	 * @param oldStates
	 *            Pre-states -- may be modified in-place.
	 * @return Post-states
	 */
	private List<OctDomainState> assumeIff(final Expression left, final Expression right, final boolean negIff,
			final List<OctDomainState> oldStates) {

		return mPostOp.splitF(oldStates, statesBeforeIff -> assumeAnd(left, negIff, right, false, statesBeforeIff),
				statesBeforeIff -> assumeAnd(left, !negIff, right, true, statesBeforeIff));
	}

	/**
	 * Assume a relation between two boolean variables (for instance "boolA == boolB").
	 *
	 * @param binExpr
	 *            Boolean relation to be assumed.
	 * @param isNegated
	 *            Negate the relation.
	 * @param oldStates
	 *            Pre-states -- may be modified in-place.
	 * @return Post-states
	 */
	private List<OctDomainState> processBooleanRelation(final BinaryExpression binExpr, final boolean isNegated,
			final List<OctDomainState> oldStates) {

		boolean not = false;
		switch (binExpr.getOperator()) {
		case COMPNEQ:
			not = true;
		case COMPEQ:
			return assumeIff(binExpr.getLeft(), binExpr.getRight(), not ^ isNegated, oldStates);
		case COMPPO:
			return oldStates; // safe over-approximation
		default:
			throw new IllegalArgumentException("Not a relation on bools: " + binExpr);
		}
	}

	/**
	 * Assume a relation between two numeric variables (for instance "intA < intB").
	 *
	 * @param binExpr
	 *            Numeric relation to be assumed.
	 * @param isNegated
	 *            Negate the relation.
	 * @param oldStates
	 *            Pre-states -- may be modified in-place.
	 * @return Post-states
	 */
	private List<OctDomainState> processNumericRelation(final BinaryExpression binExpr, final boolean isNegated,
			final List<OctDomainState> oldStates) {

		final List<OctDomainState> newStates = new ArrayList<>();
		final IfExpressionTree ifExprTree = mPostOp.getExprTransformer().removeIfExprsCached(binExpr);
		for (final Pair<Expression, List<OctDomainState>> leaf : ifExprTree.assumeLeafs(mPostOp, oldStates)) {
			newStates.addAll(processNumericRelationWithoutIfs(mLogger, (BinaryExpression) leaf.getFirst(), isNegated,
					leaf.getSecond(), mVariableProvider, mIntervalPostOperator, mCodeBlockFactory));
		}
		return mPostOp.joinDownToMax(newStates);
	}

	/**
	 * @param variableProvider
	 * @param codeBlockFactory
	 * @param fallBackPostOperator
	 * @param octDomainStateFactory
	 * @see #processNumericRelation(BinaryExpression, boolean, List)
	 */
	private List<OctDomainState> processNumericRelationWithoutIfs(final ILogger logger, final BinaryExpression binExpr,
			final boolean isNegated, final List<OctDomainState> oldStates,
			final IBoogieSymbolTableVariableProvider variableProvider,
			final IAbstractPostOperator<IntervalDomainState, IcfgEdge> fallBackPostOperator,
			final CodeBlockFactory codeBlockFactory) {

		Operator relOp = binExpr.getOperator();
		if (relOp == BinaryExpression.Operator.COMPPO) {
			return oldStates; // safe over-approximation
		} else if (isNegated) {
			relOp = AbsIntUtil.negateRelOp(relOp);
		}

		final Expression left = binExpr.getLeft();
		final Expression right = binExpr.getRight();

		final AffineExpression affLeft = mPostOp.getExprTransformer().affineExprCached(left);
		final AffineExpression affRight = mPostOp.getExprTransformer().affineExprCached(right);
		if (affLeft == null || affRight == null) {
			// Construct a new binary expression with the correct operator (if negated or not, determined above).
			final BinaryExpression boogieBinExp = new BinaryExpression(binExpr.getLoc(), binExpr.getType(), relOp,
					binExpr.getLeft(), binExpr.getRight());
			if (logger.isDebugEnabled()) {
				logger.debug("Unable to handle expression " + BoogiePrettyPrinter.print(boogieBinExp)
						+ " with Octagons (not affine). Projecting to intervals.");
			}
			final Set<IProgramVarOrConst> relevantVars =
					new VariableCollector(binExpr, variableProvider).getVariables();

			return projectAssumeOnIntervals(logger, oldStates, boogieBinExp, fallBackPostOperator, codeBlockFactory,
					relevantVars);
		}
		assert left.getType().equals(right.getType());
		final boolean intRelation = TypeUtils.isNumericInt(left.getType());
		boolean strictRelation = false;
		switch (relOp) {
		case COMPEQ:
			return processAffineEqZero(mLogger, affLeft.subtract(affRight), intRelation, oldStates, binExpr,
					mIntervalPostOperator, mCodeBlockFactory);
		case COMPNEQ:
			return processAffineNeZero(affLeft.subtract(affRight), intRelation, oldStates);
		case COMPLT:
			strictRelation = true;
		case COMPLEQ:
			return processAffineLtZero(affLeft.subtract(affRight), intRelation, strictRelation, oldStates);
		case COMPGT:
			strictRelation = true;
		case COMPGEQ:
			return processAffineLtZero(affRight.subtract(affLeft), intRelation, strictRelation, oldStates);
		default:
			throw new IllegalArgumentException("Not a relation on numbers: " + relOp);
		}
	}

	/**
	 * Assume the relation "affineExpression != 0".
	 *
	 * @param affExpr
	 *            Expression to be assumed to be not equal zero.
	 * @param intRelation
	 *            The operands/variables are integers.
	 * @param oldStates
	 *            Pre-states -- may be modified in-place.
	 * @return Post-states
	 */
	private List<OctDomainState> processAffineNeZero(AffineExpression affExpr, final boolean intRelation,
			final List<OctDomainState> oldStates) {

		if (affExpr.isConstant()) {
			if (affExpr.getConstant().signum() == 0) {
				// (assume 0 != 0) is equivalent to (assume false)
				return new ArrayList<>();
			}
			// (assume 0 != ±7) is equivalent to (assume true)
			return oldStates;
		}

		if (affExpr.getCoefficients().size() > 2 || (affExpr = affExpr.unitCoefficientForm()) == null) {
			return oldStates;
		}

		// from now on handle (affExpr - c != 0) as (affExpr <= c) or (affExpr >= c) ----------------
		BigDecimal leC; // affExpr \in [-\inf, leC] ...
		BigDecimal geC; // ... or affExpr \in [ geC, \inf]
		leC = geC = affExpr.getConstant().negate();
		if (intRelation) {
			// in case of integers: (affExpr - c != 0) as (affExpr <= c-1) or (affExpr >= c+1)
			if (AbsIntUtil.isIntegral(leC)) {
				leC = leC.subtract(BigDecimal.ONE);
				geC = geC.add(BigDecimal.ONE);
			} else {
				// Integers are always not equal to any non-integer number (intVar != 1.5)
				return oldStates;
			}
		}
		affExpr = affExpr.withoutConstant();

		final AffineExpression.OneVarForm ovf;
		final AffineExpression.TwoVarForm tvf;
		if ((ovf = affExpr.getOneVarForm()) != null) {
			OctValue geCOct, leCOct;
			if (ovf.negVar) {
				geCOct = new OctValue(leC.negate());
				leCOct = new OctValue(geC.negate());
			} else {
				geCOct = new OctValue(geC);
				leCOct = new OctValue(leC);
			}
			return mPostOp.splitC(oldStates, s -> s.assumeNumericVarInterval(ovf.var, geCOct, OctValue.INFINITY), // v>c
					s -> s.assumeNumericVarInterval(ovf.var, OctValue.INFINITY, leCOct) // v<c
			);
		} else if ((tvf = affExpr.getTwoVarForm()) != null) {
			final OctValue leCOct = new OctValue(leC);
			final OctValue leCOct2 = new OctValue(geC.negate()); // (affExpr > c) is equivalent to (-affExpr < -c)
			return mPostOp.splitC(oldStates,
					s -> s.assumeNumericVarRelationLeConstant(tvf.var1, tvf.negVar1, tvf.var2, tvf.negVar2, leCOct),
					s -> s.assumeNumericVarRelationLeConstant(tvf.var1, !tvf.negVar1, tvf.var2, !tvf.negVar2, leCOct2));

		} else {
			return oldStates; // safe over-approximation

		}
	}

	/**
	 * Assume the relation "affineExpression == 0".
	 *
	 * @param affExpr
	 *            Expression to be assumed to be equal zero.
	 * @param intRelation
	 *            The operands/variables are integers.
	 * @param oldStates
	 *            Pre-states -- may be modified in-place.
	 * @param codeBlockFactory
	 *            The code block factory.
	 * @param octDomainStateFactory
	 *            The state factory to create new octagon states.
	 * @param binExpr
	 *            The original expression.
	 * @param statement
	 * @return Post-states
	 */
	private static List<OctDomainState> processAffineEqZero(final ILogger logger, AffineExpression affExpr,
			final boolean intRelation, final List<OctDomainState> oldStates, final Expression originalExpression,
			final IAbstractPostOperator<IntervalDomainState, IcfgEdge> fallBackPostOperator,
			final CodeBlockFactory codeBlockFactory) {

		if (affExpr.isConstant()) {
			if (affExpr.getConstant().signum() != 0) {
				// (assume 0 == ±7) is equivalent to (assume false)
				return new ArrayList<>();
			}
			// (assume 0 == 0) is equivalent to (assume true)
			return oldStates;
		}

		final List<OctDomainState> nonBottomStates =
				oldStates.stream().filter(state -> !state.isBottom()).collect(Collectors.toList());
		if (nonBottomStates.isEmpty()) {
			// If the list is empty, there were only bottom states in oldStates. Therefore, the expression cannot be
			// assumed and bottom is returned.
			return new ArrayList<>();
		}

		final AffineExpression backupExpr = affExpr;
		if (affExpr.getCoefficients().size() > 2 || (affExpr = affExpr.unitCoefficientForm()) == null) {
			logger.debug("Unable to handle affine expression " + backupExpr
					+ " == 0 with Octagons. Projecting to intervals.");
			return projectAssumeOnIntervals(logger, nonBottomStates, originalExpression, fallBackPostOperator,
					codeBlockFactory, backupExpr.getCoefficients().keySet());
		}

		// from now on handle (affExpr - c == 0) as (affExpr == c) ----------------
		final BigDecimal c = affExpr.getConstant().negate();
		if (intRelation && !AbsIntUtil.isIntegral(c)) {
			// (assume intVar == 1.5) is equivalent to (assume false).
			return new ArrayList<>();
		}
		affExpr = affExpr.withoutConstant();

		final AffineExpression.OneVarForm ovf;
		final AffineExpression.TwoVarForm tvf;

		// Apply the assume to all states that are not bottom and return the result.
		if ((ovf = affExpr.getOneVarForm()) != null) {
			final OctValue cOct = new OctValue(ovf.negVar ? c.negate() : c);
			nonBottomStates.forEach(state -> state.assumeNumericVarInterval(ovf.var, cOct, cOct));
			return nonBottomStates;
		} else if ((tvf = affExpr.getTwoVarForm()) != null) {
			final OctValue cOct = new OctValue(c);
			final OctValue cOctNeg = new OctValue(c.negate());
			nonBottomStates.forEach(state -> state.assumeNumericVarRelationLeConstant(tvf.var1, tvf.negVar1, tvf.var2,
					tvf.negVar2, cOct));
			nonBottomStates.forEach(state -> state.assumeNumericVarRelationLeConstant(tvf.var1, !tvf.negVar1, tvf.var2,
					!tvf.negVar2, cOctNeg));
			return nonBottomStates;
		} else {
			return oldStates; // safe over-approximation
		}
	}

	/**
	 * Projects a given expression on intervals, computes the interval post, and projects back on the original octagon
	 * state in the hopes to deduce some more values.
	 *
	 * @param logger
	 *            The logger.
	 * @param oldStates
	 *            The old {@link OctDomainState}s.
	 * @param originalExpression
	 *            The expression to assume.
	 * @param fallBackPostOperator
	 *            The post operator of the fall back domain, here an {@link IntervalPostOperator}.
	 * @param codeBlockFactory
	 *            The factory to construct code blocks.
	 * @param octDomainStateFactory
	 * @param backupExpr
	 * @return
	 */
	private static List<OctDomainState> projectAssumeOnIntervals(final ILogger logger,
			final List<OctDomainState> oldStates, final Expression originalExpression,
			final IAbstractPostOperator<IntervalDomainState, IcfgEdge> fallBackPostOperator,
			final CodeBlockFactory codeBlockFactory, final Set<IProgramVarOrConst> relevantVars) {
		final List<IntervalDomainState> intervalStates = oldStates.stream().filter(state -> !state.isBottom())
				.map(state -> IntervalProjection.projectOctagonStateToIntervalDomainState(logger, state))
				.collect(Collectors.toList());

		assert intervalStates.stream().noneMatch(state -> state
				.isBottom()) : "At least one interval state became bottom during conversion. This should not happen";

		// All oldstates are bottom
		if (intervalStates.isEmpty()) {
			return oldStates;
		}

		final AssumeStatement assume = new AssumeStatement(originalExpression.getLoc(), originalExpression);
		final StatementSequence assumeBlock = codeBlockFactory.constructStatementSequence(null, null,
				Collections.singletonList(assume), Origin.IMPLEMENTATION);
		if (logger.isDebugEnabled()) {
			logger.debug("Projection of current OctDomainState to Intervals: " + intervalStates);
			logger.debug("Applying the following statement to each state: " + BoogiePrettyPrinter.print(assume));
		}

		final List<IntervalDomainState> computedIntervalPost = new ArrayList<>();
		for (final IntervalDomainState iState : intervalStates) {
			computedIntervalPost.addAll(fallBackPostOperator.apply(iState, assumeBlock));
		}
		if (logger.isDebugEnabled()) {
			logger.debug("Resulting interval states: " + computedIntervalPost);
			logger.debug("Projecting back to octagons.");
		}

		final List<OctDomainState> returnStates = new ArrayList<>();

		for (final OctDomainState oldState : oldStates) {
			for (final IntervalDomainState iState : computedIntervalPost) {
				final OctDomainState newOld =
						IntervalProjection.projectIntervalStateToOctagon(logger, iState, oldState, relevantVars);
				if (newOld.isBottom()) {
					returnStates.add(newOld);
				} else {
					returnStates.add(oldState.intersect(newOld));
				}
			}
		}

		logger.debug("Resulting octagon states: " + returnStates);
		return returnStates;
	}

	/**
	 * Assume the relation "affineExpression < 0" or "affineExpression <= 0".
	 *
	 * @param affExpr
	 *            Expression to be assumed to be less than zero.
	 * @param intRelation
	 *            The operands/variables are integers.
	 * @param strictRelation
	 *            The relation is strict, that is "<" instead of "<=".
	 * @param oldStates
	 *            Pre-states -- may be modified in-place.
	 * @return Post-states
	 */
	private static List<OctDomainState> processAffineLtZero(AffineExpression affExpr, final boolean intRelation,
			final boolean strictRelation, final List<OctDomainState> oldStates) {

		if (affExpr.getCoefficients().size() > 2 || (affExpr = affExpr.unitCoefficientForm()) == null) {
			return oldStates;
		}

		// from now on handle (affExpr - c <= 0) as (affExpr <= c) ----------------
		BigDecimal c = affExpr.getConstant().negate();
		if (intRelation) {
			if (!AbsIntUtil.isIntegral(c)) {
				// int <= 1.5 ==> int <= 1
				// int < 1.5 ==> int <= 1
				c = c.setScale(0, RoundingMode.FLOOR);
			} else if (strictRelation) { // && c is int
				// int < 2 ==> int <= 1
				c = c.subtract(BigDecimal.ONE);
			}
		}
		affExpr = affExpr.withoutConstant();

		final AffineExpression.OneVarForm ovf;
		final AffineExpression.TwoVarForm tvf;
		if (affExpr.isConstant()) {
			if (c.signum() < 0) {
				// (assume 0 <= -7) is equivalent to (assume false)
				return new ArrayList<>();
			}
			// (assume 0 <= 7) is equivalent to (assume true)
			return oldStates;

		} else if ((ovf = affExpr.getOneVarForm()) != null) {
			final OctValue min;
			final OctValue max;
			if (ovf.negVar) {
				// (-v <= c) is equal to (v >= -c)
				min = new OctValue(c.negate());
				max = OctValue.INFINITY;
			} else {
				min = OctValue.INFINITY;
				max = new OctValue(c);
			}
			oldStates.forEach(state -> state.assumeNumericVarInterval(ovf.var, min, max));
			return oldStates;

		} else if ((tvf = affExpr.getTwoVarForm()) != null) {
			final OctValue cOct = new OctValue(c);
			oldStates.forEach(state -> state.assumeNumericVarRelationLeConstant(tvf.var1, tvf.negVar1, tvf.var2,
					tvf.negVar2, cOct));
			return oldStates;

		} else {
			return oldStates; // safe over-approximation

		}
	}

	/**
	 * Collects all variables of a given Boogie {@link Expression};
	 *
	 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
	 *
	 */
	private static class VariableCollector extends BoogieVisitor {
		private final Set<IProgramVarOrConst> mVariables;
		private final IBoogieSymbolTableVariableProvider mVariableProvider;

		private VariableCollector(final Expression expression,
				final IBoogieSymbolTableVariableProvider variableProvider) {
			mVariables = new HashSet<>();
			mVariableProvider = variableProvider;
			processExpression(expression);
		}

		private Set<IProgramVarOrConst> getVariables() {
			return mVariables;
		}

		@Override
		protected void visit(final VariableLHS lhs) {
			mVariables.add(mVariableProvider.getBoogieVar(lhs.getIdentifier(), lhs.getDeclarationInformation(), false));
		}

		@Override
		protected void visit(final IdentifierExpression expr) {
			mVariables
					.add(mVariableProvider.getBoogieVar(expr.getIdentifier(), expr.getDeclarationInformation(), false));
		}
	}
}
