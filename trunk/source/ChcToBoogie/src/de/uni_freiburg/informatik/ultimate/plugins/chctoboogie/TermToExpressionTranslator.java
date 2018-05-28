//package de.uni_freiburg.informatik.ultimate.plugins.chctoboogie;
//
//import java.math.BigDecimal;
//import java.math.BigInteger;
//import java.util.ArrayDeque;
//import java.util.Deque;
//import java.util.HashSet;
//import java.util.function.Predicate;
//
//import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
//import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
//import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayAccessExpression;
//import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayStoreExpression;
//import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
//import de.uni_freiburg.informatik.ultimate.boogie.ast.BitvecLiteral;
//import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
//import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
//import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
//import de.uni_freiburg.informatik.ultimate.boogie.ast.IfThenElseExpression;
//import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
//import de.uni_freiburg.informatik.ultimate.boogie.ast.RealLiteral;
//import de.uni_freiburg.informatik.ultimate.boogie.ast.StringLiteral;
//import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
//import de.uni_freiburg.informatik.ultimate.core.model.models.IBoogieType;
//import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
//import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
//import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
//import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
//import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
//import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
//import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
//import de.uni_freiburg.informatik.ultimate.logic.Rational;
//import de.uni_freiburg.informatik.ultimate.logic.Sort;
//import de.uni_freiburg.informatik.ultimate.logic.Term;
//import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
//import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.BoogieConst;
//import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.BitvectorUtils;
//import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtSortUtils;
//import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
//
//public class TermToExpressionTranslator extends NonRecursive {
//	private final Predicate<Term> mPredicate;
//	private final boolean mOnlyOutermost;
//
//
//	private final Deque<Expression> mConverted = new ArrayDeque<>();
//
//	public TermToExpressionTranslator(final Predicate<Term> predicate) {
//		this(predicate, false);
//	}
//
//	public TermToExpressionTranslator(final Predicate<Term> predicate, final boolean onlyOutermost) {
//		mPredicate = predicate;
//		mOnlyOutermost = onlyOutermost;
//	}
//
//	public Expression getBoogieExpression(final Term term) {
//		if (term == null) {
//			throw new IllegalArgumentException();
//		}
////		mResult = new HashSet<>();
//		mVisitedSubterms = new HashSet<>();
//		run(new TermToExpressionWalker(term));
////		return mResult;
//		// TODO
//		return null;
//	}
//
//	IBoogieType getBoogieType(final Sort sort) {
//		return null;
//	}
//
//	void setResult(final Expression e) {
//		mConverted.addLast(e);
//	}
//
//	class TermToExpressionWalker extends TermWalker {
//
//		TermToExpressionWalker(final Term term) {
//			super(term);
//		}
//
//		@Override
//		public void walk(final NonRecursive walker, final ConstantTerm term) {
//			// initially copied from Term2Expression
//			final Object value = term.getValue();
//			final IBoogieType type = getBoogieType(term.getSort());
//			if (SmtSortUtils.isBitvecSort(term.getSort())) {
//				final BigInteger[] indices = term.getSort().getIndices();
//				if (indices.length != 1) {
//					throw new AssertionError("BitVec has exactly one index");
//				}
//
//				BigInteger decimalValue;
//				if (value.toString().startsWith("#x")) {
//					decimalValue = new BigInteger(value.toString().substring(2), 16);
//				} else if (value.toString().startsWith("#b")) {
//					decimalValue = new BigInteger(value.toString().substring(2), 2);
//				} else {
//					throw new UnsupportedOperationException("only hexadecimal values and boolean values supported yet");
//				}
//				final int length = indices[0].intValue();
//				final Expression res = new BitvecLiteral(null, type, String.valueOf(decimalValue), length);
//				setResult(res);
//				return;
//			}
//			if (value instanceof String) {
//				final StringLiteral res = new StringLiteral(null, type, value.toString());
//				setResult(res);
//				return;
//			} else if (value instanceof BigInteger) {
//				final Expression res = new IntegerLiteral(null, type, value.toString());
//				setResult(res);
//				return;
//
//			} else if (value instanceof BigDecimal) {
//				final Expression res = new RealLiteral(null, type, value.toString());
//				setResult(res);
//				return;
//			} else if (value instanceof Rational) {
//				if (SmtSortUtils.isIntSort(term.getSort())) {
//					final Expression res = new IntegerLiteral(null, type, value.toString());
//					setResult(res);
//					return;
//				} else if (SmtSortUtils.isRealSort(term.getSort())) {
//					final Expression res = new RealLiteral(null, type, value.toString());
//					setResult(res);
//					return;
//				} else {
//					throw new UnsupportedOperationException("unknown Sort");
//				}
//			} else {
//				throw new UnsupportedOperationException("unknown kind of Term");
//			}
//		}
//
//		@Override
//		public void walk(final NonRecursive walker, final AnnotatedTerm term) {
//			throw new UnsupportedOperationException();
////			if (mPredicate.test(term)) {
////				mResult.add(term);
////				if (mOnlyOutermost) {
////					// ignore subterms
////					return;
////				}
////			}
////			walker.enqueueWalker(new TermToExpressionWalker(term.getSubterm()));
//		}
//
//		@Override
//		public void walk(final NonRecursive walker, final ApplicationTerm term) {
//			final FunctionSymbol symb = term.getFunction();
//
//			if (symb.isIntern() && "select".equals(symb.getName())) {
//				return translateSelect(term);
//			} else if (symb.isIntern() && "store".equals(symb.getName())) {
//				return translateStore(term);
//			} else if (BitvectorUtils.isBitvectorConstant(symb)) {
//				return translateBitvectorConstant(term);
//			}
//
//			final Term[] termParams = term.getParameters();
//			final Expression[] params = new Expression[termParams.length];
//			for (int i = 0; i < termParams.length; i++) {
//				params[i] = translate(termParams[i]);
//			}
//			final IBoogieType type = mTypeSortTranslator.getType(symb.getReturnSort());
//			if (symb.getParameterSorts().length == 0) {
//				if (SmtUtils.isTrue(term)) {
//					final IBoogieType booleanType = mTypeSortTranslator.getType(SmtSortUtils.getBoolSort(mScript));
//					return new BooleanLiteral(null, booleanType, true);
//				}
//				if (SmtUtils.isFalse(term)) {
//					final IBoogieType booleanType = mTypeSortTranslator.getType(SmtSortUtils.getBoolSort(mScript));
//					return new BooleanLiteral(null, booleanType, false);
//				}
//				final BoogieConst boogieConst = mBoogie2SmtSymbolTable.getProgramConst(term);
//				if (boogieConst != null) {
//					return new IdentifierExpression(null, mTypeSortTranslator.getType(term.getSort()),
//							boogieConst.getIdentifier(), new DeclarationInformation(StorageClass.GLOBAL, null));
//				}
//				if (mBoogie2SmtSymbolTable.getSmtFunction2BoogieFunction().containsKey(symb.getName())) {
//					return translateWithSymbolTable(symb, type, termParams);
//				}
//				throw new IllegalArgumentException();
//			} else if ("ite".equals(symb.getName())) {
//				return new IfThenElseExpression(null, type, params[0], params[1], params[2]);
//			} else if (symb.isIntern()) {
//				if (symb.getParameterSorts().length > 0 &&
//						(SmtSortUtils.isBitvecSort(symb.getParameterSorts()[0]) || SmtSortUtils.isFloatingpointSort(symb.getReturnSort()))
//						&& !"=".equals(symb.getName()) && !"distinct".equals(symb.getName())) {
//					if ("extract".equals(symb.getName())) {
//						return translateBitvectorAccess(type, term);
//					} else if (mBoogie2SmtSymbolTable.getSmtFunction2BoogieFunction().containsKey(symb.getName())) {
//						return translateWithSymbolTable(symb, type, termParams);
//					} else {
//						throw new UnsupportedOperationException(
//								"translation of " + symb + " not yet implemented, please contact Matthias");
//					}
//				} else if (symb.getParameterSorts().length == 1) {
//					if ("not".equals(symb.getName())) {
//						final Expression param = translate(term.getParameters()[0]);
//						return new UnaryExpression(null, type, UnaryExpression.Operator.LOGICNEG, param);
//					} else if ("-".equals(symb.getName())) {
//						final Expression param = translate(term.getParameters()[0]);
//						return new UnaryExpression(null, type, UnaryExpression.Operator.ARITHNEGATIVE, param);
//					} else {
//						throw new IllegalArgumentException("unknown symbol " + symb);
//					}
//				} else {
//					if ("xor".equals(symb.getName())) {
//						return xor(params);
//					} else if ("mod".equals(symb.getName())) {
//						return mod(params);
//					}
//					final Operator op = getBinaryOperator(symb);
//					if (symb.isLeftAssoc()) {
//						return leftAssoc(op, type, params);
//					} else if (symb.isRightAssoc()) {
//						return rightAssoc(op, type, params);
//					} else if (symb.isChainable()) {
//						return chainable(op, type, params);
//					} else if (symb.isPairwise()) {
//						return pairwise(op, type, params);
//					} else {
//						throw new UnsupportedOperationException(
//								"don't know symbol" + " which is neither leftAssoc, rightAssoc, chainable, or pairwise.");
//					}
//				}
//			} else if (mBoogie2SmtSymbolTable.getSmtFunction2BoogieFunction().containsKey(symb.getName())) {
//				return translateWithSymbolTable(symb, type, termParams);
//			} else {
//				throw new UnsupportedOperationException(
//						"translation of " + symb + " not yet implemented, please contact Matthias");
//			}
//		}
//
//		private ArrayStoreExpression translateStore(final ApplicationTerm term) {
//			final Expression array = translate(term.getParameters()[0]);
//			final Expression index = translate(term.getParameters()[1]);
//			final Expression[] indices = { index };
//			final Expression value = translate(term.getParameters()[2]);
//			final IBoogieType type = mTypeSortTranslator.getType(term.getSort());
//			return new ArrayStoreExpression(null, type, array, indices, value);
//		}
//
//		/**
//		 * Translate a single select expression to an ArrayAccessExpression. If we have nested select expressions this leads
//		 * to nested ArrayAccessExpressions, hence arrays which do not occur in the boogie program.
//		 */
//		private ArrayAccessExpression translateSelect(final ApplicationTerm term) {
//			final Expression array = translate(term.getParameters()[0]);
//			final Expression index = translate(term.getParameters()[1]);
//			final Expression[] indices = { index };
//			final IBoogieType type = mTypeSortTranslator.getType(term.getSort());
//			return new ArrayAccessExpression(null, type, array, indices);
//		}
//
//		@Override
//		public void walk(final NonRecursive walker, final LetTerm term) {
//			throw new UnsupportedOperationException();
//		}
//
//		@Override
//		public void walk(final NonRecursive walker, final QuantifiedFormula term) {
//			throw new UnsupportedOperationException();
//		}
//
//		@Override
//		public void walk(final NonRecursive walker, final TermVariable term) {
//			if (mPredicate.test(term)) {
//				mResult.add(term);
//			}
//		}
//	}
//}
