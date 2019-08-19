/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayStoreExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BitVectorAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BitvecLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.QuantifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Trigger;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.models.IBoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.util.datastructures.BitvectorConstant.SupportedBitvectorOperations;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedHashMap;

/**
 * Translate a Boogie Expression into an SMT Term. Use the here defined interface IndentifierResolver to translate
 * identifier expressions.
 *
 * @author Matthias Heizmann, Thomas Lang
 *
 */
public class Expression2Term {

	private final Script mScript;
	private final TypeSortTranslator mTypeSortTranslator;
	private final IOperationTranslator mOperationTranslator;
	private final Boogie2SmtSymbolTable mBoogie2SmtSymbolTable;
	private final ManagedScript mVariableManager;
	private final boolean mOverapproximateFunctions = false;

	private final ScopedHashMap<String, TermVariable> mQuantifiedVariables = new ScopedHashMap<>();
	private IIdentifierTranslator[] mSmtIdentifierProviders;
	private Map<String, ILocation> mOverapproximations = null;
	private Collection<TermVariable> mAuxVars = null;

	/**
	 * Count the height of current old(.) expressions. As long as this is strictly greater than zero we are have to
	 * consider all global vars as oldvars.
	 */
	private int mOldContextScopeDepth = 0;

	private final IUltimateServiceProvider mServices;
	private static final String OVERAPPROXIMATION = "overapproximation";

	public Expression2Term(final IUltimateServiceProvider services, final Script script,
			final TypeSortTranslator typeSortTranslator, final Boogie2SmtSymbolTable boogie2SmtSymbolTable,
			final IOperationTranslator operationTranslator, final ManagedScript variableManager) {
		super();
		mServices = services;
		mScript = script;
		mTypeSortTranslator = typeSortTranslator;
		mBoogie2SmtSymbolTable = boogie2SmtSymbolTable;
		mOperationTranslator = operationTranslator;
		mVariableManager = variableManager;
	}

	public SingleTermResult translateToTerm(final IIdentifierTranslator[] identifierTranslators,
			final Expression expression) {
		assert mSmtIdentifierProviders == null : getClass().getSimpleName() + " in use";
		assert mQuantifiedVariables.isEmpty() : getClass().getSimpleName() + " in use";
		assert mOverapproximations == null : getClass().getSimpleName() + " in use";
		assert mAuxVars == null : getClass().getSimpleName() + " in use";
		mSmtIdentifierProviders = identifierTranslators;
		mAuxVars = new ArrayList<>();
		mOverapproximations = new HashMap<>();
		final Term term = translate(expression);
		final SingleTermResult result = new SingleTermResult(mOverapproximations, mAuxVars, term);
		mSmtIdentifierProviders = null;
		mAuxVars = null;
		mOverapproximations = null;
		return result;
	}

	public MultiTermResult translateToTerms(final IIdentifierTranslator[] identifierTranslators,
			final Expression[] expressions) {
		assert mSmtIdentifierProviders == null : getClass().getSimpleName() + " in use";
		assert mQuantifiedVariables.isEmpty() : getClass().getSimpleName() + " in use";
		assert mOverapproximations == null : getClass().getSimpleName() + " in use";
		assert mAuxVars == null : getClass().getSimpleName() + " in use";
		mSmtIdentifierProviders = identifierTranslators;
		mAuxVars = new ArrayList<>();
		mOverapproximations = new HashMap<>();
		final Term[] terms = new Term[expressions.length];
		for (int i = 0; i < expressions.length; i++) {
			terms[i] = translate(expressions[i]);
		}
		final MultiTermResult result = new MultiTermResult(mOverapproximations, mAuxVars, terms);
		mSmtIdentifierProviders = null;
		mAuxVars = null;
		mOverapproximations = null;
		return result;
	}

	private Term getSmtIdentifier(final String id, final DeclarationInformation declInfo, final boolean isOldContext,
			final BoogieASTNode boogieASTNode) {
		if (mQuantifiedVariables.containsKey(id)) {
			return mQuantifiedVariables.get(id);
		}
		for (final IIdentifierTranslator it : mSmtIdentifierProviders) {
			final Term term = it.getSmtIdentifier(id, declInfo, isOldContext, boogieASTNode);
			if (term != null) {
				return term;
			}
		}
		throw new AssertionError("found no translation for id " + id);
	}

	/**
	 * We are in a context where we have to consider all global vars as oldvars if mOldContextScopeDepth is > 0.
	 *
	 * @return
	 */
	private boolean isOldContext() {
		return mOldContextScopeDepth > 0;
	}

	private Term translate(final Expression exp) {
		if (exp instanceof ArrayAccessExpression) {
			final ArrayAccessExpression arrexp = (ArrayAccessExpression) exp;
			final Expression[] indices = arrexp.getIndices();
			Term result = translate(arrexp.getArray());
			for (int i = 0; i < indices.length; i++) {
				final Term indexiTerm = translate(indices[i]);
				result = SmtUtils.select(mScript, result, indexiTerm);
			}
			return result;

		} else if (exp instanceof ArrayStoreExpression) {
			final ArrayStoreExpression arrexp = (ArrayStoreExpression) exp;
			final Expression[] indices = arrexp.getIndices();
			assert indices.length > 0;
			// arrayBeforeIndex[i] represents the array, where all indices
			// before the i'th index have already been selected
			final Term[] arrayBeforeIndex = new Term[indices.length];
			final Term[] indexTerm = new Term[indices.length];
			arrayBeforeIndex[0] = translate(arrexp.getArray());
			for (int i = 0; i < indices.length - 1; i++) {
				indexTerm[i] = translate(indices[i]);
				arrayBeforeIndex[i + 1] = SmtUtils.select(mScript, arrayBeforeIndex[i], indexTerm[i]);
			}
			indexTerm[indices.length - 1] = translate(indices[indices.length - 1]);
			Term result = translate(arrexp.getValue());
			for (int i = indices.length - 1; i >= 0; i--) {
				result = SmtUtils.store(mScript, arrayBeforeIndex[i], indexTerm[i], result);
			}
			assert (result != null);
			assert resultContainsNoNull(result);
			return result;

		} else if (exp instanceof BinaryExpression) {
			final BinaryExpression binexp = (BinaryExpression) exp;
			final BinaryExpression.Operator op = binexp.getOperator();
			// Sort sort = mSmt2Boogie.getSort(binexp.getLeft().getType());
			if (op == BinaryExpression.Operator.COMPNEQ) {
				final String equalityFuncname = mOperationTranslator.opTranslation(BinaryExpression.Operator.COMPEQ,
						binexp.getLeft().getType(), binexp.getRight().getType());
				final String negationFuncname =
						mOperationTranslator.opTranslation(UnaryExpression.Operator.LOGICNEG, BoogieType.TYPE_BOOL);
				final BigInteger[] indices = new BigInteger[0];
				return SmtUtils.termWithLocalSimplification(mScript, negationFuncname, indices, null,
						SmtUtils.termWithLocalSimplification(mScript, equalityFuncname, indices, null,
								translate(binexp.getLeft()), translate(binexp.getRight())));
			}
			final String funcname =
					mOperationTranslator.opTranslation(op, binexp.getLeft().getType(), binexp.getRight().getType());
			final BigInteger[] indices = null;
			return SmtUtils.termWithLocalSimplification(mScript, funcname, indices, null, translate(binexp.getLeft()),
					translate(binexp.getRight()));
		} else if (exp instanceof UnaryExpression) {
			final UnaryExpression unexp = (UnaryExpression) exp;
			final UnaryExpression.Operator op = unexp.getOperator();
			if (op == UnaryExpression.Operator.OLD) {
				mOldContextScopeDepth++;
				final Term term = translate(unexp.getExpr());
				mOldContextScopeDepth--;
				return term;
			}
			final String funcname = mOperationTranslator.opTranslation(op, unexp.getExpr().getType());
			final BigInteger[] indices = null;
			return SmtUtils.termWithLocalSimplification(mScript, funcname, indices, null, translate(unexp.getExpr()));
		} else if (exp instanceof RealLiteral) {
			final Term result = mOperationTranslator.realTranslation((RealLiteral) exp);
			assert result != null;
			return result;

		} else if (exp instanceof BitvecLiteral) {
			final Term result = mOperationTranslator.bitvecTranslation((BitvecLiteral) exp);
			assert result != null;
			return result;

		} else if (exp instanceof BitVectorAccessExpression) {
			final BigInteger[] indices = new BigInteger[2];
			indices[0] = BigInteger.valueOf(((BitVectorAccessExpression) exp).getEnd() - 1);
			indices[1] = BigInteger.valueOf(((BitVectorAccessExpression) exp).getStart());

			final Term result =
					mScript.term("extract", indices, null, translate(((BitVectorAccessExpression) exp).getBitvec()));
			assert result != null;
			return result;

		} else if (exp instanceof BooleanLiteral) {
			final Term result = mOperationTranslator.booleanTranslation((BooleanLiteral) exp);
			assert result != null;
			return result;

		} else if (exp instanceof FunctionApplication) {
			return translateFunctionApplication(((FunctionApplication) exp));
		} else if (exp instanceof IdentifierExpression) {
			final IdentifierExpression var = (IdentifierExpression) exp;
			assert var.getDeclarationInformation() != null : " no declaration information";
			final Term result =
					getSmtIdentifier(var.getIdentifier(), var.getDeclarationInformation(), isOldContext(), exp);
			assert result != null;
			return result;

		} else if (exp instanceof IntegerLiteral) {
			final Term result = mOperationTranslator.integerTranslation((IntegerLiteral) exp);
			assert result != null;
			return result;

		} else if (exp instanceof IfThenElseExpression) {
			final IfThenElseExpression ite = (IfThenElseExpression) exp;
			final Term cond = translate(ite.getCondition());
			final Term thenPart = translate(ite.getThenPart());
			final Term elsePart = translate(ite.getElsePart());
			final Term result = Util.ite(mScript, cond, thenPart, elsePart);
			assert result != null;
			return result;

		} else if (exp instanceof QuantifierExpression) {
			// throw new
			// UnsupportedOperationException("QuantifierExpression not implemented yet");
			final QuantifierExpression quant = (QuantifierExpression) exp;
			final String[] typeParams = quant.getTypeParams();
			final VarList[] variables = quant.getParameters();
			int numvars = typeParams.length;
			for (int i = 0; i < variables.length; i++) {
				numvars += variables[i].getIdentifiers().length;
			}
			final TermVariable[] vars = new TermVariable[numvars];
			// TODO is this really unused code
			// HashMap<String,Term> newVars = new HashMap<String, Term>();
			int offset = 0;
			// for (int j = 0; j < typeParams.length; j++) {
			// vars[offset] = mScript.createTermVariable("q" +
			// quoteId(typeParams[j]), intSort);
			// typeStack.push(vars[offset]);
			// offset++;
			// }
			mQuantifiedVariables.beginScope();
			for (int i = 0; i < variables.length; i++) {
				final IBoogieType type = variables[i].getType().getBoogieType();
				final Sort sort = mTypeSortTranslator.getSort(type, exp);
				for (int j = 0; j < variables[i].getIdentifiers().length; j++) {
					final String identifier = variables[i].getIdentifiers()[j];
					final String smtVarName = "q" + Boogie2SMT.quoteId(variables[i].getIdentifiers()[j]);
					vars[offset] = mScript.variable(smtVarName, sort);
					mQuantifiedVariables.put(identifier, vars[offset]);
					offset++;
				}
			}
			final Term form = translate(quant.getSubformula());

			final Attribute[] attrs = quant.getAttributes();
			int numTrigs = 0;
			for (final Attribute a : attrs) {
				if (a instanceof Trigger) {
					numTrigs++;
				}
			}
			final Term[][] triggers = new Term[numTrigs][];
			offset = 0;
			for (final Attribute a : attrs) {
				if (a instanceof Trigger) {
					final Expression[] trigs = ((Trigger) a).getTriggers();
					final Term[] smttrigs = new Term[trigs.length];
					for (int i = 0; i < trigs.length; i++) {
						final Term trig = translate(trigs[i]);
						// if (trig instanceof ITETerm
						// && ((ITETerm)trig).getTrueCase() == ONE
						// && ((ITETerm)trig).getFalseCase() == ZERO)
						// smttrigs[i] = ((ITETerm) trig).getCondition();
						// else
						smttrigs[i] = trig;
					}
					triggers[offset++] = smttrigs;
				}
			}
			// throw new
			// UnsupportedOperationException("QuantifierExpression not implemented yet");
			// identStack.pop();
			// for (int j = 0; j < typeParams.length; j++) {
			// typeStack.pop();
			// }
			mQuantifiedVariables.endScope();

			Term result = null;
			try {
				result = quant.isUniversal() ? mScript.quantifier(Script.FORALL, vars, form, triggers)
						: mScript.quantifier(Script.EXISTS, vars, form, triggers);
			} catch (final SMTLIBException e) {
				if (e.getMessage().equals("Cannot create quantifier in quantifier-free logic")) {
					Boogie2SMT.reportUnsupportedSyntax(exp, "Setting does not support quantifiers", mServices);
					throw e;
				}
				throw new AssertionError();
			}
			assert resultContainsNoNull(result);
			return result;
		} else {
			throw new AssertionError("Unsupported expression " + exp);
		}
	}

	private Term translateFunctionApplication(final FunctionApplication func) {
		final Term result;
		final Map<String, Expression[]> attributes = mBoogie2SmtSymbolTable.getAttributes(func.getIdentifier());
		final String overapproximation =
				Boogie2SmtSymbolTable.checkForAttributeDefinedIdentifier(attributes, OVERAPPROXIMATION);
		if (mOverapproximateFunctions || overapproximation != null) {
			final Sort resultSort = mTypeSortTranslator.getSort(func.getType(), func);
			final TermVariable auxVar = mVariableManager.constructFreshTermVariable(func.getIdentifier(), resultSort);
			mAuxVars.add(auxVar);
			mOverapproximations.put(overapproximation, func.getLocation());
			result = auxVar;
		} else {

			final IBoogieType[] argumentTypes = new IBoogieType[func.getArguments().length];
			for (int i = 0; i < func.getArguments().length; i++) {
				argumentTypes[i] = func.getArguments()[i].getType();
			}

			final Sort[] params = new Sort[func.getArguments().length];
			for (int i = 0; i < func.getArguments().length; i++) {
				params[i] = mTypeSortTranslator.getSort(func.getArguments()[i].getType(), func);
			}

			final Term[] parameters = new Term[func.getArguments().length];
			for (int i = 0; i < func.getArguments().length; i++) {
				parameters[i] = translate(func.getArguments()[i]);
			}

			final String funcSymb = mOperationTranslator.funcApplication(func.getIdentifier(), argumentTypes);
			if (funcSymb == null) {
				throw new IllegalArgumentException("unknown function" + func.getIdentifier());
			}

			final BigInteger[] indices = Boogie2SmtSymbolTable.checkForIndices(attributes);
			final SupportedBitvectorOperations sbo = ExpressionFactory.getSupportedBitvectorOperation(funcSymb);
			if (sbo == null) {
				result = mScript.term(funcSymb, indices, null, parameters);
			} else {
				// simplification is overkill for non-bv operations
				result = SmtUtils.termWithLocalSimplification(mScript, funcSymb, indices, null, parameters);
			}
		}
		return result;
	}

	private boolean resultContainsNoNull(final Term result) {
		// toString crashes if the result contains a null element
		return result.toString() != null;
	}

	abstract static class TranslationResult {
		private final Map<String, ILocation> mOverappoximations;
		private final Collection<TermVariable> mAuxiliaryVars;

		public TranslationResult(final Map<String, ILocation> overapproximations,
				final Collection<TermVariable> auxiliaryVars) {
			super();
			assert auxiliaryVars != null;
			mOverappoximations = overapproximations;
			mAuxiliaryVars = auxiliaryVars;
		}

		public Map<String, ILocation> getOverappoximations() {
			return mOverappoximations;
		}

		public Collection<TermVariable> getAuxiliaryVars() {
			return mAuxiliaryVars;
		}
	}

	public static class SingleTermResult extends TranslationResult {
		private final Term mTerm;

		public SingleTermResult(final Map<String, ILocation> overapproximations,
				final Collection<TermVariable> auxiliaryVars, final Term term) {
			super(overapproximations, auxiliaryVars);
			mTerm = term;
		}

		public Term getTerm() {
			return mTerm;
		}
	}

	public static class MultiTermResult extends TranslationResult {
		private final Term[] mTerms;

		public MultiTermResult(final Map<String, ILocation> overapproximations,
				final Collection<TermVariable> auxiliaryVars, final Term[] terms) {
			super(overapproximations, auxiliaryVars);
			mTerms = terms;
		}

		public Term[] getTerms() {
			return mTerms;
		}
	}

	@FunctionalInterface
	public interface IIdentifierTranslator {
		Term getSmtIdentifier(String id, DeclarationInformation declInfo, boolean isOldContext,
				BoogieASTNode boogieASTNode);
	}
}
