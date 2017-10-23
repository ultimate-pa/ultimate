/*
 * Copyright (C) 2017 Marius Greitschus
 * Copyright (C) 2012-2015 Evren Ermis
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie;

import java.io.Serializable;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayStoreExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BitVectorAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BitvecLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.QuantifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StringLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Trigger;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.models.IBoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.BitvectorUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedHashMap;

/**
 * Translates SMT Terms to Boogie Expressions where occurring term variable names and corresponding Boogie variable
 * names are known.
 *
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public final class MappedTerm2Expression implements Serializable {

	private static final long serialVersionUID = -3407883192314998843L;

	private final Script mScript;

	private final ScopedHashMap<TermVariable, VarList> mQuantifiedVariables;

	private int mFreshIdentiferCounter;

	private final TypeSortTranslator mTypeSortTranslator;

	private final Boogie2SmtSymbolTable mBoogie2SmtSymbolTable;

	private final Set<IdentifierExpression> mFreeVariables;

	public MappedTerm2Expression(final TypeSortTranslator tsTranslation,
			final Boogie2SmtSymbolTable boogie2SmtSymbolTable, final ManagedScript maScript) {
		mTypeSortTranslator = tsTranslation;
		mBoogie2SmtSymbolTable = boogie2SmtSymbolTable;
		mScript = maScript.getScript();
		mFreeVariables = new HashSet<>();
		mFreshIdentiferCounter = 0;
		mQuantifiedVariables = new ScopedHashMap<>();
	}

	private String getFreshIdenfier() {
		mFreshIdentiferCounter++;
		return "freshIdentifier" + mFreshIdentiferCounter;
	}

	public Expression translate(final Term term, final Set<TermVariable> variableNameRetainment,
			final Map<TermVariable, String> alternateOldNames) {
		Expression result;
		if (term instanceof AnnotatedTerm) {
			result = translate((AnnotatedTerm) term, variableNameRetainment, alternateOldNames);
		} else if (term instanceof ApplicationTerm) {
			return translate((ApplicationTerm) term, variableNameRetainment, alternateOldNames);
		} else if (term instanceof ConstantTerm) {
			result = translate((ConstantTerm) term, variableNameRetainment, alternateOldNames);
		} else if (term instanceof LetTerm) {
			result = translate((LetTerm) term, variableNameRetainment, alternateOldNames);
		} else if (term instanceof QuantifiedFormula) {
			result = translate((QuantifiedFormula) term, variableNameRetainment, alternateOldNames);
		} else if (term instanceof TermVariable) {
			result = translate((TermVariable) term, variableNameRetainment, alternateOldNames);
		} else {
			throw new UnsupportedOperationException("unknown kind of Term");
		}
		assert result != null;
		return result;
	}

	private static Expression translate(final AnnotatedTerm term, final Set<TermVariable> variableMapRetainment,
			final Map<TermVariable, String> alternateOldNames) {
		throw new UnsupportedOperationException("annotations not supported yet" + term);
	}

	private Expression translate(final ApplicationTerm term, final Set<TermVariable> variableRewriteMap,
			final Map<TermVariable, String> alternateOldNames) {
		final FunctionSymbol symb = term.getFunction();

		if (symb.isIntern() && "select".equals(symb.getName())) {
			return translateSelect(term, variableRewriteMap, alternateOldNames);
		} else if (symb.isIntern() && "store".equals(symb.getName())) {
			return translateStore(term, variableRewriteMap, alternateOldNames);
		} else if (BitvectorUtils.isBitvectorConstant(symb)) {
			return translateBitvectorConstant(term);
		}

		final Term[] termParams = term.getParameters();
		final Expression[] params = new Expression[termParams.length];
		for (int i = 0; i < termParams.length; i++) {
			params[i] = translate(termParams[i], variableRewriteMap, alternateOldNames);
		}
		final IBoogieType type = mTypeSortTranslator.getType(symb.getReturnSort());
		if (symb.getParameterSorts().length == 0) {
			if (SmtUtils.isTrue(term)) {
				final IBoogieType booleanType = mTypeSortTranslator.getType(SmtSortUtils.getBoolSort(mScript));
				return new BooleanLiteral(null, booleanType, true);
			}
			if (SmtUtils.isFalse(term)) {
				final IBoogieType booleanType = mTypeSortTranslator.getType(SmtSortUtils.getBoolSort(mScript));
				return new BooleanLiteral(null, booleanType, false);
			}
			final BoogieConst boogieConst = mBoogie2SmtSymbolTable.getProgramConst(term);
			if (boogieConst != null) {
				return new IdentifierExpression(null, mTypeSortTranslator.getType(term.getSort()),
						boogieConst.getIdentifier(), new DeclarationInformation(StorageClass.GLOBAL, null));
			}
			if (mBoogie2SmtSymbolTable.getSmtFunction2BoogieFunction().containsKey(symb.getName())) {
				return translateWithSymbolTable(symb, type, termParams, variableRewriteMap, alternateOldNames);
			}
			throw new IllegalArgumentException();
		} else if ("ite".equals(symb.getName())) {
			return new IfThenElseExpression(null, type, params[0], params[1], params[2]);
		} else if (symb.isIntern()) {
			if (symb.getParameterSorts().length > 0
					&& (SmtSortUtils.isBitvecSort(symb.getParameterSorts()[0])
							|| SmtSortUtils.isFloatingpointSort(symb.getReturnSort()))
					&& !"=".equals(symb.getName()) && !"distinct".equals(symb.getName())) {
				if ("extract".equals(symb.getName())) {
					return translateBitvectorAccess(type, term, variableRewriteMap, alternateOldNames);
				} else if (mBoogie2SmtSymbolTable.getSmtFunction2BoogieFunction().containsKey(symb.getName())) {
					return translateWithSymbolTable(symb, type, termParams, variableRewriteMap, alternateOldNames);
				} else {
					throw new UnsupportedOperationException(
							"translation of " + symb + " not yet implemented, please contact Matthias");
				}
			} else if (symb.getParameterSorts().length == 1) {
				if ("not".equals(symb.getName())) {
					final Expression param = translate(term.getParameters()[0], variableRewriteMap, alternateOldNames);
					return new UnaryExpression(null, type, UnaryExpression.Operator.LOGICNEG, param);
				} else if ("-".equals(symb.getName())) {
					final Expression param = translate(term.getParameters()[0], variableRewriteMap, alternateOldNames);
					return new UnaryExpression(null, type, UnaryExpression.Operator.ARITHNEGATIVE, param);
				} else {
					throw new IllegalArgumentException("unknown symbol " + symb);
				}
			} else {
				if ("xor".equals(symb.getName())) {
					return xor(params);
				} else if ("mod".equals(symb.getName())) {
					return mod(params);
				}
				final Operator op = getBinaryOperator(symb);
				if (symb.isLeftAssoc()) {
					return leftAssoc(op, type, params);
				} else if (symb.isRightAssoc()) {
					return rightAssoc(op, type, params);
				} else if (symb.isChainable()) {
					return chainable(op, type, params);
				} else if (symb.isPairwise()) {
					return pairwise(op, type, params);
				} else {
					throw new UnsupportedOperationException(
							"don't know symbol" + " which is neither leftAssoc, rightAssoc, chainable, or pairwise.");
				}
			}
		} else if (mBoogie2SmtSymbolTable.getSmtFunction2BoogieFunction().containsKey(symb.getName())) {
			return translateWithSymbolTable(symb, type, termParams, variableRewriteMap, alternateOldNames);
		} else {
			throw new UnsupportedOperationException(
					"translation of " + symb + " not yet implemented, please contact Matthias");
		}
	}

	private Expression translateBitvectorAccess(final IBoogieType type, final ApplicationTerm term,
			final Set<TermVariable> variableNameRetainment, final Map<TermVariable, String> alternateOldNames) {
		assert "extract".equals(term.getFunction().getName()) : "no extract";
		assert term.getParameters().length == 1;
		assert term.getFunction().getIndices().length == 2;
		final Expression bitvector = translate(term.getParameters()[0], variableNameRetainment, alternateOldNames);
		final int start = term.getFunction().getIndices()[1].intValueExact();
		final int end = term.getFunction().getIndices()[0].intValueExact();
		return new BitVectorAccessExpression(null, type, bitvector, end, start);
	}

	/**
	 * Use symbol table to translate a SMT function application into a Boogie function application.
	 *
	 * @param alternateOldNames
	 */
	private Expression translateWithSymbolTable(final FunctionSymbol symb, final IBoogieType type,
			final Term[] termParams, final Set<TermVariable> variableNameRetainment,
			final Map<TermVariable, String> alternateOldNames) {
		final String identifier = mBoogie2SmtSymbolTable.getSmtFunction2BoogieFunction().get(symb.getName());
		final Expression[] arguments = new Expression[termParams.length];
		for (int i = 0; i < termParams.length; i++) {
			arguments[i] = translate(termParams[i], variableNameRetainment, alternateOldNames);
		}
		return new FunctionApplication(null, type, identifier, arguments);
	}

	/**
	 * Translate term in case it is a bitvector constant as defined as an extension of the BV logic.
	 */
	private Expression translateBitvectorConstant(final ApplicationTerm term) {
		assert term.getSort().getIndices().length == 1;
		final String name = term.getFunction().getName();
		assert name.startsWith("bv");
		final String decimalValue = name.substring(2, name.length());
		final IBoogieType type = mTypeSortTranslator.getType(term.getSort());
		final BigInteger length = term.getSort().getIndices()[0];
		return new BitvecLiteral(null, type, decimalValue, length.intValue());
	}

	private static Expression mod(final Expression[] params) {
		if (params.length != 2) {
			throw new AssertionError("mod has two parameters");
		}
		return new BinaryExpression(null, BoogieType.TYPE_INT, Operator.ARITHMOD, params[0], params[1]);
	}

	private ArrayStoreExpression translateStore(final ApplicationTerm term,
			final Set<TermVariable> variableNameRetainment, final Map<TermVariable, String> alternateOldNames) {
		final Expression array = translate(term.getParameters()[0], variableNameRetainment, alternateOldNames);
		final Expression index = translate(term.getParameters()[1], variableNameRetainment, alternateOldNames);
		final Expression[] indices = { index };
		final Expression value = translate(term.getParameters()[2], variableNameRetainment, alternateOldNames);
		final IBoogieType type = mTypeSortTranslator.getType(term.getSort());
		return new ArrayStoreExpression(null, type, array, indices, value);
	}

	/**
	 * Translate a single select expression to an ArrayAccessExpression. If we have nested select expressions this leads
	 * to nested ArrayAccessExpressions, hence arrays which do not occur in the boogie program.
	 *
	 * @param alternateOldNames
	 */
	private ArrayAccessExpression translateSelect(final ApplicationTerm term,
			final Set<TermVariable> variableRewriteMap, final Map<TermVariable, String> alternateOldNames) {
		final Expression array = translate(term.getParameters()[0], variableRewriteMap, alternateOldNames);
		final Expression index = translate(term.getParameters()[1], variableRewriteMap, alternateOldNames);
		final Expression[] indices = { index };
		final IBoogieType type = mTypeSortTranslator.getType(term.getSort());
		return new ArrayAccessExpression(null, type, array, indices);
	}

	/**
	 * Translate a nested sequence of select expressions to a single ArrayAccessExpression. (see translateSelect why
	 * this might be useful)
	 *
	 * @param alternateOldNames
	 */
	private ArrayAccessExpression translateArray(final ApplicationTerm term,
			final Set<TermVariable> variableNameRetainment, final Map<TermVariable, String> alternateOldNames) {
		final List<Expression> reverseIndices = new ArrayList<>();
		ApplicationTerm localTerm = term;
		while ("select".equals(localTerm.getFunction().getName())
				&& (localTerm.getParameters()[0] instanceof ApplicationTerm)) {
			assert localTerm.getParameters().length == 2;
			final Expression index = translate(localTerm.getParameters()[1], variableNameRetainment, alternateOldNames);
			reverseIndices.add(index);
			localTerm = (ApplicationTerm) localTerm.getParameters()[0];
		}
		assert localTerm.getParameters().length == 2;
		final Expression index = translate(localTerm.getParameters()[1], variableNameRetainment, alternateOldNames);
		reverseIndices.add(index);

		final Expression array = translate(localTerm.getParameters()[0], variableNameRetainment, alternateOldNames);
		final Expression[] indices = new Expression[reverseIndices.size()];
		for (int i = 0; i < indices.length; i++) {
			indices[i] = reverseIndices.get(indices.length - 1 - i);
		}
		final IBoogieType type = mTypeSortTranslator.getType(localTerm.getSort());
		return new ArrayAccessExpression(null, type, array, indices);
	}

	private Expression translate(final ConstantTerm term, final Set<TermVariable> variableNameRetainment,
			final Map<TermVariable, String> alternateOldNames) {
		final Object value = term.getValue();
		final IBoogieType type = mTypeSortTranslator.getType(term.getSort());
		if (SmtSortUtils.isBitvecSort(term.getSort())) {
			final BigInteger[] indices = term.getSort().getIndices();
			if (indices.length != 1) {
				throw new AssertionError("BitVec has exactly one index");
			}

			BigInteger decimalValue;
			if (value.toString().startsWith("#x")) {
				decimalValue = new BigInteger(value.toString().substring(2), 16);
			} else if (value.toString().startsWith("#b")) {
				decimalValue = new BigInteger(value.toString().substring(2), 2);
			} else {
				throw new UnsupportedOperationException("only hexadecimal values and boolean values supported yet");
			}
			final int length = indices[0].intValue();
			return new BitvecLiteral(null, type, String.valueOf(decimalValue), length);
		}
		if (value instanceof String) {
			return new StringLiteral(null, type, value.toString());
		} else if (value instanceof BigInteger) {
			return new IntegerLiteral(null, type, value.toString());
		} else if (value instanceof BigDecimal) {
			return new RealLiteral(null, type, value.toString());
		} else if (value instanceof Rational) {
			if (SmtSortUtils.isIntSort(term.getSort())) {
				return new IntegerLiteral(null, type, value.toString());
			} else if (SmtSortUtils.isRealSort(term.getSort())) {
				return new RealLiteral(null, type, value.toString());
			} else {
				throw new UnsupportedOperationException("unknown Sort");
			}
		} else {
			throw new UnsupportedOperationException("unknown kind of Term");
		}
	}

	private static Expression translate(final LetTerm term, final Set<TermVariable> variableNameRetainment,
			final Map<TermVariable, String> alternateOldNames) {
		throw new IllegalArgumentException("unlet Term first");
	}

	private Expression translate(final QuantifiedFormula term, final Set<TermVariable> variableNameRetainment,
			final Map<TermVariable, String> alternateOldNames) {
		mQuantifiedVariables.beginScope();
		final VarList[] parameters = new VarList[term.getVariables().length];
		int offset = 0;
		for (final TermVariable tv : term.getVariables()) {
			final IBoogieType boogieType = mTypeSortTranslator.getType(tv.getSort());
			final String[] identifiers = { tv.getName() };
			final ASTType astType = new PrimitiveType(null, boogieType, boogieType.toString());
			final VarList varList = new VarList(null, identifiers, astType);
			parameters[offset] = varList;
			mQuantifiedVariables.put(tv, varList);
			offset++;
		}
		final IBoogieType type = mTypeSortTranslator.getType(term.getSort());
		assert term.getQuantifier() == QuantifiedFormula.FORALL || term.getQuantifier() == QuantifiedFormula.EXISTS;
		final boolean isUniversal = term.getQuantifier() == QuantifiedFormula.FORALL;
		final String[] typeParams = new String[0];
		Attribute[] attributes;
		Term subTerm = term.getSubformula();
		if (subTerm instanceof AnnotatedTerm) {
			assert ":pattern".equals(((AnnotatedTerm) subTerm).getAnnotations()[0].getKey());
			final Annotation[] annotations = ((AnnotatedTerm) subTerm).getAnnotations();
			// FIXME: does not have to be the case, allow several annotations
			assert annotations.length == 1 : "expecting only one annotation at a time";
			final Annotation annotation = annotations[0];
			final Object value = annotation.getValue();
			assert value instanceof Term[] : "expecting Term[]" + value;
			subTerm = ((AnnotatedTerm) subTerm).getSubterm();
			final Term[] pattern = (Term[]) value;
			if (pattern.length == 0) {
				attributes = new Attribute[0];
			} else {
				final Expression[] triggers = new Expression[pattern.length];
				for (int i = 0; i < pattern.length; i++) {
					triggers[i] = translate(pattern[i], variableNameRetainment, alternateOldNames);
				}
				final Trigger trigger = new Trigger(null, triggers);
				attributes = new Attribute[1];
				attributes[0] = trigger;
			}
		} else {
			attributes = new Attribute[0];
		}
		final Expression subformula = translate(subTerm, variableNameRetainment, alternateOldNames);
		final QuantifierExpression result =
				new QuantifierExpression(null, type, isUniversal, typeParams, parameters, attributes, subformula);
		mQuantifiedVariables.endScope();
		return result;
	}

	private Expression translate(final TermVariable term, final Set<TermVariable> variableNameRetainment,
			final Map<TermVariable, String> alternateOldNames) {
		final Expression result;
		final IBoogieType type = mTypeSortTranslator.getType(term.getSort());

		if (alternateOldNames.containsKey(term)) {
			result = new IdentifierExpression(null, type, alternateOldNames.get(term),
					new DeclarationInformation(StorageClass.IMPLEMENTATION, null));
		} else if (variableNameRetainment.contains(term)) {
			result = new IdentifierExpression(null, type, term.getName(),
					new DeclarationInformation(StorageClass.IMPLEMENTATION, null));
		} else {
			if (mQuantifiedVariables.containsKey(term)) {
				final VarList varList = mQuantifiedVariables.get(term);
				assert varList.getIdentifiers().length == 1;
				final String id = varList.getIdentifiers()[0];
				result = new IdentifierExpression(null, type, translateIdentifier(id),
						new DeclarationInformation(StorageClass.QUANTIFIED, null));
			} else if (mBoogie2SmtSymbolTable.getProgramVar(term) == null) {
				// Case where term contains some auxilliary variable that was
				// introduced during model checking.
				// TODO: Matthias: I think we want closed expressions, we should
				// quantify auxilliary variables
				result = new IdentifierExpression(null, type, getFreshIdenfier(),
						new DeclarationInformation(StorageClass.QUANTIFIED, null));
				mFreeVariables.add((IdentifierExpression) result);
			} else {
				final IProgramVar pv = mBoogie2SmtSymbolTable.getProgramVar(term);
				final BoogieASTNode astNode = mBoogie2SmtSymbolTable.getAstNode(pv);
				assert astNode != null : "There is no AstNode for the IProgramVar " + pv;
				final ILocation loc = astNode.getLocation();
				final DeclarationInformation declInfo = mBoogie2SmtSymbolTable.getDeclarationInformation(pv);
				if (pv instanceof LocalBoogieVar) {
					result = new IdentifierExpression(loc, type,
							translateIdentifier(((LocalBoogieVar) pv).getIdentifier()), declInfo);
				} else if (pv instanceof BoogieNonOldVar) {
					result = new IdentifierExpression(loc, type,
							translateIdentifier(((BoogieNonOldVar) pv).getIdentifier()), declInfo);
				} else if (pv instanceof BoogieOldVar) {
					assert pv.isGlobal();
					final Expression nonOldExpression = new IdentifierExpression(loc, type,
							translateIdentifier(((BoogieOldVar) pv).getIdentifierOfNonOldVar()), declInfo);
					result = new UnaryExpression(loc, type, UnaryExpression.Operator.OLD, nonOldExpression);
				} else if (pv instanceof BoogieConst) {
					result = new IdentifierExpression(loc, type,
							translateIdentifier(((BoogieConst) pv).getIdentifier()), declInfo);
				} else {
					throw new AssertionError("unsupported kind of variable " + pv.getClass().getSimpleName());
				}
			}
		}
		return result;
	}

	/*
	 * TODO escape all sequences that are not allowed in Boogie
	 */
	private String translateIdentifier(final String id) {
		return id.replace(" ", "_").replace("(", "_").replace(")", "_").replace("+", "PLUS").replace("-", "MINUS")
				.replace("*", "MUL");
	}

	private static Operator getBinaryOperator(final FunctionSymbol symb) {
		if ("and".equals(symb.getName())) {
			return Operator.LOGICAND;
		} else if ("or".equals(symb.getName())) {
			return Operator.LOGICOR;
		} else if ("=>".equals(symb.getName())) {
			return Operator.LOGICIMPLIES;
		} else if ("=".equals(symb.getName()) && "bool".equals(symb.getParameterSort(0).getName())) {
			return Operator.LOGICIFF;
		} else if ("=".equals(symb.getName())) {
			return Operator.COMPEQ;
		} else if ("distinct".equals(symb.getName())) {
			return Operator.COMPNEQ;
		} else if ("<=".equals(symb.getName())) {
			return Operator.COMPLEQ;
		} else if (">=".equals(symb.getName())) {
			return Operator.COMPGEQ;
		} else if ("<".equals(symb.getName())) {
			return Operator.COMPLT;
		} else if (">".equals(symb.getName())) {
			return Operator.COMPGT;
		} else if ("+".equals(symb.getName())) {
			return Operator.ARITHPLUS;
		} else if ("-".equals(symb.getName())) {
			return Operator.ARITHMINUS;
		} else if ("*".equals(symb.getName())) {
			return Operator.ARITHMUL;
		} else if ("/".equals(symb.getName())) {
			return Operator.ARITHDIV;
		} else if ("div".equals(symb.getName())) {
			return Operator.ARITHDIV;
		} else if ("mod".equals(symb.getName())) {
			return Operator.ARITHMOD;
		} else if ("ite".equals(symb.getName())) {
			throw new UnsupportedOperationException("not yet implemented");
		} else if ("abs".equals(symb.getName())) {
			throw new UnsupportedOperationException("not yet implemented");
		} else {
			throw new IllegalArgumentException("unknown symbol " + symb);
		}
	}

	private static Expression leftAssoc(final Operator op, final IBoogieType type, final Expression[] params) {
		Expression result = params[0];
		for (int i = 0; i < params.length - 1; i++) {
			result = new BinaryExpression(null, type, op, result, params[i + 1]);
		}
		return result;
	}

	private static Expression rightAssoc(final Operator op, final IBoogieType type, final Expression[] params) {
		Expression result = params[params.length - 1];
		for (int i = params.length - 1; i > 0; i--) {
			result = new BinaryExpression(null, type, op, params[i - 1], result);
		}
		return result;
	}

	private static Expression chainable(final Operator op, final IBoogieType type, final Expression[] params) {
		assert type == BoogieType.TYPE_BOOL;
		Expression result = new BinaryExpression(null, type, op, params[0], params[1]);
		Expression chain;
		for (int i = 1; i < params.length - 1; i++) {
			chain = new BinaryExpression(null, type, op, params[i], params[i + 1]);
			result = new BinaryExpression(null, BoogieType.TYPE_BOOL, Operator.LOGICAND, result, chain);
		}
		return result;
	}

	private static Expression pairwise(final Operator op, final IBoogieType type, final Expression[] params) {
		assert type == BoogieType.TYPE_BOOL;
		Expression result = new BinaryExpression(null, type, op, params[0], params[1]);
		Expression neq;
		for (int i = 0; i < params.length - 1; i++) {
			for (int j = i + 1; j < params.length - 1; j++) {
				if (i == 0 && j == 1) {
					continue;
				}
				neq = new BinaryExpression(null, type, op, params[j], params[j + 1]);
				result = new BinaryExpression(null, BoogieType.TYPE_BOOL, Operator.LOGICAND, result, neq);
			}
		}
		return result;
	}

	private static Expression xor(final Expression[] params) {
		final IBoogieType type = BoogieType.TYPE_BOOL;
		final Operator iff = Operator.LOGICIFF;
		final UnaryExpression.Operator neg = UnaryExpression.Operator.LOGICNEG;
		Expression result = params[0];
		for (int i = 0; i < params.length - 1; i++) {
			result = new BinaryExpression(null, type, iff, params[i + 1], result);
			result = new UnaryExpression(null, type, neg, result);
		}
		return result;
	}

}