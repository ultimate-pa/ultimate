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
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.boogie.BitvectorFactory;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
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
import de.uni_freiburg.informatik.ultimate.boogie.ast.StringLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructConstructor;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Trigger;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WildcardExpression;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.models.IBoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.BitvectorConstant.BvOp;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedHashMap;

/**
 * Translate a Boogie Expression into an SMT Term. Uses the interface {@link IIdentifierTranslator} to translate
 * identifier expressions.
 *
 * @author Matthias Heizmann, Thomas Lang
 */
public class Expression2Term {
	private static final String ERROR_UNSUPPORTED_EXPRESSION = "Unsupported expression ";
	private static final String OVERAPPROXIMATION = "overapproximation";

	private final IUltimateServiceProvider mServices;
	private final Script mScript;
	private final TypeSortTranslator mTypeSortTranslator;
	private final IOperationTranslator mOperationTranslator;
	private final Boogie2SmtSymbolTable mBoogie2SmtSymbolTable;
	private final ManagedScript mVariableManager;
	private final boolean mOverapproximateFunctions = false;

	private final ScopedHashMap<String, TermVariable> mQuantifiedVariables = new ScopedHashMap<>();
	private IIdentifierTranslator[] mSmtIdentifierProviders;
	private Map<String, ILocation> mOverapproximations;
	private Collection<TermVariable> mAuxVars;

	/**
	 * Count the height of current old(.) expressions. As long as this is strictly greater than zero we are have to
	 * consider all global vars as oldvars.
	 */
	private int mOldContextScopeDepth = 0;

	public Expression2Term(final IUltimateServiceProvider services, final Script script,
			final TypeSortTranslator typeSortTranslator, final Boogie2SmtSymbolTable boogie2SmtSymbolTable,
			final IOperationTranslator operationTranslator, final ManagedScript variableManager) {
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
		assert declInfo != null : "no declaration information";

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
		final Term result = switch (exp) {
		// Literals
		case final BitvecLiteral bvLit -> mOperationTranslator.bitvecTranslation(bvLit);
		case final BooleanLiteral boolLit -> mOperationTranslator.booleanTranslation(boolLit);
		case final IntegerLiteral intLit -> mOperationTranslator.integerTranslation(intLit);
		case final RealLiteral realLit -> mOperationTranslator.realTranslation(realLit);

		// Other supported expressions
		case final ArrayAccessExpression arrexp -> translateArrayAccess(arrexp);
		case final ArrayStoreExpression arrexp -> translateArrayStore(arrexp);
		case final BinaryExpression binexp -> translateBinaryExpression(binexp);
		case final BitVectorAccessExpression bvAccess -> translateBitVectorAccess(bvAccess);
		case final FunctionApplication funApp -> translateFunctionApplication(funApp);
		case final IdentifierExpression var ->
				getSmtIdentifier(var.getIdentifier(), var.getDeclarationInformation(), isOldContext(), exp);
		case final IfThenElseExpression ite -> translateIfThenElse(ite);
		case final QuantifierExpression quant -> translateQuantifierExpression(quant);
		case final UnaryExpression unexp -> translateUnaryExpression(unexp);

		// Unsupported expressions
		case final WildcardExpression wild -> throw new AssertionError(ERROR_UNSUPPORTED_EXPRESSION + exp);
		case final StructAccessExpression structAccess -> throw new AssertionError(ERROR_UNSUPPORTED_EXPRESSION + exp);
		case final StringLiteral stringLit -> throw new AssertionError(ERROR_UNSUPPORTED_EXPRESSION + exp);
		case final StructConstructor structConstr -> throw new AssertionError(ERROR_UNSUPPORTED_EXPRESSION + exp);
		};

		assert result != null : "failed to translate " + exp.getClass().getSimpleName() + ": " + exp;
		assert resultContainsNoNull(result);
		return result;
	}

	private Term translateArrayAccess(final ArrayAccessExpression arrexp) {
		Term result = translate(arrexp.getArray());
		for (final Expression index : arrexp.getIndices()) {
			final Term indexiTerm = translate(index);
			result = SmtUtils.select(mScript, result, indexiTerm);
		}
		return result;
	}

	private Term translateArrayStore(final ArrayStoreExpression arrexp) {
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
		return result;
	}

	private Term translateBinaryExpression(final BinaryExpression binexp) {
		final BinaryExpression.Operator op = binexp.getOperator();
		if (op == BinaryExpression.Operator.COMPNEQ) {
			final String equalityFuncname = mOperationTranslator.opTranslation(BinaryExpression.Operator.COMPEQ,
					binexp.getLeft().getType(), binexp.getRight().getType());
			final String negationFuncname =
					mOperationTranslator.opTranslation(UnaryExpression.Operator.LOGICNEG, BoogieType.TYPE_BOOL);
			return SmtUtils.unfTerm(mScript, negationFuncname, null, null, SmtUtils.unfTerm(mScript, equalityFuncname,
					null, null, translate(binexp.getLeft()), translate(binexp.getRight())));
		}
		final String funcname =
				mOperationTranslator.opTranslation(op, binexp.getLeft().getType(), binexp.getRight().getType());
		return SmtUtils.unfTerm(mScript, funcname, null, null, translate(binexp.getLeft()),
				translate(binexp.getRight()));
	}

	private Term translateBitVectorAccess(final BitVectorAccessExpression bvAccess) {
		final BigInteger[] bvIndices = new BigInteger[2];
		bvIndices[0] = BigInteger.valueOf(bvAccess.getEnd() - 1L);
		bvIndices[1] = BigInteger.valueOf(bvAccess.getStart());
		return mScript.term(SMTLIBConstants.EXTRACT, SmtUtils.toStringArray(bvIndices), null,
				translate(bvAccess.getBitvec()));
	}

	private Term translateFunctionApplication(final FunctionApplication func) {
		final Map<String, Expression[]> attributes = mBoogie2SmtSymbolTable.getAttributes(func.getIdentifier());
		final String overapproximation =
				Boogie2SmtSymbolTable.checkForAttributeDefinedIdentifier(attributes, OVERAPPROXIMATION);
		if (mOverapproximateFunctions || overapproximation != null) {
			final Sort resultSort = mTypeSortTranslator.getSort(func.getType(), func);
			final TermVariable auxVar = mVariableManager.constructFreshTermVariable(func.getIdentifier(), resultSort);
			mAuxVars.add(auxVar);
			mOverapproximations.put(overapproximation, func.getLocation());
			return auxVar;
		}

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

		final String[] indices = Boogie2SmtSymbolTable.checkForIndices(attributes);
		final BvOp sbo = BitvectorFactory.getSupportedBitvectorOperation(funcSymb);
		if (sbo == null) {
			return mScript.term(funcSymb, indices, null, parameters);
		}
		// simplification is overkill for non-bv operations
		return SmtUtils.unfTerm(mScript, funcSymb, indices, null, parameters);

	}

	private Term translateIfThenElse(final IfThenElseExpression ite) {
		final Term cond = translate(ite.getCondition());
		final Term thenPart = translate(ite.getThenPart());
		final Term elsePart = translate(ite.getElsePart());
		return SmtUtils.ite(mScript, cond, thenPart, elsePart);
	}

	private Term translateQuantifierExpression(final QuantifierExpression quant) {
		final String[] typeParams = quant.getTypeParams();
		final VarList[] variables = quant.getParameters();
		int numvars = typeParams.length;
		for (final VarList variable : variables) {
			numvars += variable.getIdentifiers().length;
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
		for (final VarList variable : variables) {
			final IBoogieType type = variable.getType().getBoogieType();
			final Sort sort = mTypeSortTranslator.getSort(type, quant);
			for (int j = 0; j < variable.getIdentifiers().length; j++) {
				final String identifier = variable.getIdentifiers()[j];
				final String smtVarName = "q" + Boogie2SMT.quoteId(variable.getIdentifiers()[j]);
				vars[offset] = mScript.variable(smtVarName, sort);
				mQuantifiedVariables.put(identifier, vars[offset]);
				offset++;
			}
		}
		final Term form = translate(quant.getSubformula());

		final int numTrigs = (int) Arrays.stream(quant.getAttributes()).filter(Trigger.class::isInstance).count();
		final Term[][] triggers = new Term[numTrigs][];

		offset = 0;
		for (final Attribute a : quant.getAttributes()) {
			if (a instanceof final Trigger trigger) {
				final Expression[] trigs = trigger.getTriggers();
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
				triggers[offset] = smttrigs;
				offset++;
			}
		}
		// identStack.pop();
		// for (int j = 0; j < typeParams.length; j++) {
		// typeStack.pop();
		// }
		mQuantifiedVariables.endScope();

		try {
			final int quantifier = quant.isUniversal() ? Script.FORALL : Script.EXISTS;
			return mScript.quantifier(quantifier, vars, form, triggers);
		} catch (final SMTLIBException e) {
			if ("Cannot create quantifier in quantifier-free logic".equals(e.getMessage())) {
				Boogie2SMT.reportUnsupportedSyntax(quant, "Setting does not support quantifiers", mServices);
			}
			throw e;
		}
	}

	private Term translateUnaryExpression(final UnaryExpression unexp) {
		final UnaryExpression.Operator op = unexp.getOperator();
		if (op == UnaryExpression.Operator.OLD) {
			mOldContextScopeDepth++;
			final Term term = translate(unexp.getExpr());
			mOldContextScopeDepth--;
			return term;
		}
		final String unaryFunc = mOperationTranslator.opTranslation(op, unexp.getExpr().getType());
		return SmtUtils.unfTerm(mScript, unaryFunc, null, null, translate(unexp.getExpr()));
	}

	private static boolean resultContainsNoNull(final Term result) {
		// toString crashes if the result contains a null element
		return result.toString() != null;
	}

	public record SingleTermResult(Map<String, ILocation> overapproximations, Collection<TermVariable> auxiliaryVars,
			Term term) {
		// simple record
	}

	public record MultiTermResult(Map<String, ILocation> overapproximations, Collection<TermVariable> auxiliaryVars,
			Term[] terms) {
		// simple record
	}

	@FunctionalInterface
	public interface IIdentifierTranslator {
		Term getSmtIdentifier(String id, DeclarationInformation declInfo, boolean isOldContext,
				BoogieASTNode boogieASTNode);
	}
}
