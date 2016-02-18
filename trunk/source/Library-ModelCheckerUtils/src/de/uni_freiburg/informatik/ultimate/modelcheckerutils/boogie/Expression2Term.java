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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.boogie.type.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayStoreExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BitVectorAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BitvecLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.QuantifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Trigger;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.util.ScopedHashMap;

/**
 * Translate a Boogie Expression into an SMT Term. Use the here defined
 * interface IndentifierResolver to translate identifier expressions.
 * 
 * @author Matthias Heizmann, Thomas Lang
 * 
 */
public class Expression2Term {

	public interface IdentifierTranslator {
		public Term getSmtIdentifier(String id, DeclarationInformation declInfo, boolean isOldContext,
				BoogieASTNode boogieASTNode);
	}

	private final Script m_Script;
	private final TypeSortTranslator m_TypeSortTranslator;
	private final IOperationTranslator m_OperationTranslator;
	private final Boogie2SmtSymbolTable m_Boogie2SmtSymbolTable;
	private final VariableManager m_VariableManager;
	private final boolean m_OverapproximateFunctions = false;
	
	private final ScopedHashMap<String, TermVariable> m_QuantifiedVariables = new ScopedHashMap<>();
	private IdentifierTranslator[] m_SmtIdentifierProviders;
	private Map<String, ILocation> m_Overapproximations = null;
	private Collection<TermVariable> m_AuxVars = null;

	/**
	 * Count the height of current old(.) expressions. As long as this is
	 * strictly greater than zero we are have to consider all global vars as
	 * oldvars.
	 */
	private int m_OldContextScopeDepth = 0;

	private final IUltimateServiceProvider mServices;
	private static final String s_Overapproximation = "overapproximation";

	public Expression2Term(IUltimateServiceProvider services, Script script, 
			TypeSortTranslator typeSortTranslator, 
			Boogie2SmtSymbolTable boogie2SmtSymbolTable, IOperationTranslator operationTranslator, VariableManager variableManager) {
		super();
		mServices = services;
		m_Script = script;
		m_TypeSortTranslator = typeSortTranslator;
		m_Boogie2SmtSymbolTable = boogie2SmtSymbolTable;
		m_OperationTranslator = operationTranslator;
		m_VariableManager = variableManager;
	}

	public SingleTermResult translateToTerm(IdentifierTranslator[] identifierTranslators, Expression expression) {
		assert m_SmtIdentifierProviders == null : getClass().getSimpleName() + " in use";
		assert m_QuantifiedVariables.isEmpty() : getClass().getSimpleName() + " in use";
		assert m_Overapproximations == null : getClass().getSimpleName() + " in use";
		assert m_AuxVars == null : getClass().getSimpleName() + " in use";
		m_SmtIdentifierProviders = identifierTranslators;
		m_AuxVars = new ArrayList<>();
		m_Overapproximations = new HashMap<String, ILocation>();
		Term term = translate(expression);
		SingleTermResult result = new SingleTermResult(m_Overapproximations, m_AuxVars, term);
		m_SmtIdentifierProviders = null;
		m_AuxVars = null;
		m_Overapproximations = null;
		return result; 
	}

	public MultiTermResult translateToTerms(IdentifierTranslator[] identifierTranslators, Expression[] expressions) {
		assert m_SmtIdentifierProviders == null : getClass().getSimpleName() + " in use";
		assert m_QuantifiedVariables.isEmpty() : getClass().getSimpleName() + " in use";
		assert m_Overapproximations == null : getClass().getSimpleName() + " in use";
		assert m_AuxVars == null : getClass().getSimpleName() + " in use";
		m_SmtIdentifierProviders = identifierTranslators;
		m_AuxVars = new ArrayList<>();
		m_Overapproximations = new HashMap<String, ILocation>();
		Term[] terms = new Term[expressions.length];
		for (int i = 0; i < expressions.length; i++) {
			terms[i] = translate(expressions[i]);
		}
		MultiTermResult result = new MultiTermResult(m_Overapproximations, m_AuxVars, terms);
		m_SmtIdentifierProviders = null;
		m_AuxVars = null;
		m_Overapproximations = null;
		return result; 
	}

	Term getSmtIdentifier(String id, DeclarationInformation declInfo, boolean isOldContext, BoogieASTNode boogieASTNode) {
		if (m_QuantifiedVariables.containsKey(id)) {
			return m_QuantifiedVariables.get(id);
		} else {
			for (IdentifierTranslator it : m_SmtIdentifierProviders) {
				Term term = it.getSmtIdentifier(id, declInfo, isOldContext, boogieASTNode);
				if (term != null) {
					return term;
				}
			}
			throw new AssertionError("found no translation for id " + id);
		}
	}

	/**
	 * We are in a context where we have to consider all global vars as oldvars
	 * if m_OldContextScopeDepth is > 0.
	 * 
	 * @return
	 */
	private boolean isOldContext() {
		return m_OldContextScopeDepth > 0;
	}

	private Term translate(Expression exp) {
		if (exp instanceof ArrayAccessExpression) {
			ArrayAccessExpression arrexp = (ArrayAccessExpression) exp;
			Expression[] indices = arrexp.getIndices();
			Term result = translate(arrexp.getArray());
			for (int i = 0; i < indices.length; i++) {
				Term indexiTerm = translate(indices[i]);
				result = m_Script.term("select", result, indexiTerm);
			}
			return result;

		} else if (exp instanceof ArrayStoreExpression) {
			ArrayStoreExpression arrexp = (ArrayStoreExpression) exp;
			Expression[] indices = arrexp.getIndices();
			assert indices.length > 0;
			// arrayBeforeIndex[i] represents the array, where all indices
			// before the i'th index have already been selected
			Term[] arrayBeforeIndex = new Term[indices.length];
			Term[] indexTerm = new Term[indices.length];
			arrayBeforeIndex[0] = translate(arrexp.getArray());
			for (int i = 0; i < indices.length - 1; i++) {
				indexTerm[i] = translate(indices[i]);
				arrayBeforeIndex[i + 1] = m_Script.term("select", arrayBeforeIndex[i], indexTerm[i]);
			}
			indexTerm[indices.length - 1] = translate(indices[indices.length - 1]);
			Term result = translate(arrexp.getValue());
			for (int i = indices.length - 1; i >= 0; i--) {
				result = m_Script.term("store", arrayBeforeIndex[i], indexTerm[i], result);
			}
			assert (result != null);
			assert (result.toString() instanceof Object);
			return result;

		} else if (exp instanceof BinaryExpression) {
			BinaryExpression binexp = (BinaryExpression) exp;
			BinaryExpression.Operator op = binexp.getOperator();
			// Sort sort = m_Smt2Boogie.getSort(binexp.getLeft().getType());
            if (op == BinaryExpression.Operator.COMPNEQ) {
				String equalityFuncname = m_OperationTranslator.opTranslation(
						BinaryExpression.Operator.COMPEQ, binexp.getLeft().getType(), binexp.getRight().getType());
				String negationFuncname = m_OperationTranslator.opTranslation(
						UnaryExpression.Operator.LOGICNEG, PrimitiveType.boolType);
				BigInteger[] indices = new BigInteger[0];
            	return SmtUtils.termWithLocalSimplification(m_Script, 
            			negationFuncname, indices,
            			SmtUtils.termWithLocalSimplification(m_Script, 
            			equalityFuncname, indices, 
					    translate(binexp.getLeft()), translate(binexp.getRight())));
            } else {
				String funcname = m_OperationTranslator.opTranslation(
						op, binexp.getLeft().getType(), binexp.getRight().getType());
				BigInteger[] indices = null;
			    return SmtUtils.termWithLocalSimplification(m_Script, 
			    		funcname, indices,
					    translate(binexp.getLeft()), translate(binexp.getRight()));
            }
		} else if (exp instanceof UnaryExpression) {
			UnaryExpression unexp = (UnaryExpression) exp;
			UnaryExpression.Operator op = unexp.getOperator();
			if (op == UnaryExpression.Operator.OLD) {
				m_OldContextScopeDepth++;
				Term term = translate(unexp.getExpr());
				m_OldContextScopeDepth--;
				return term;
			} else {
				String funcname = m_OperationTranslator.opTranslation(op, unexp.getExpr().getType());
				BigInteger[] indices = null;
				return SmtUtils.termWithLocalSimplification(m_Script, funcname, indices, translate(unexp.getExpr()));
			}
		} else if (exp instanceof RealLiteral) {
			Term result = m_OperationTranslator.realTranslation((RealLiteral) exp);
			assert result != null;
			return result;

		} else if (exp instanceof BitvecLiteral) {
			Term result = m_OperationTranslator.bitvecTranslation((BitvecLiteral) exp);
			assert result != null;
			return result;

		} else if (exp instanceof BitVectorAccessExpression) {
			BigInteger[] indices = new BigInteger[2];
			indices[0] = new BigInteger(new Integer(((BitVectorAccessExpression) exp).getEnd() - 1).toString());
			indices[1] = new BigInteger(new Integer(((BitVectorAccessExpression) exp).getStart()).toString());

			Term result = m_Script.term("extract", indices, null, translate(((BitVectorAccessExpression) exp).getBitvec()));
			assert result != null;
			return result;

		} else if (exp instanceof BooleanLiteral) {
			Term result = m_OperationTranslator.booleanTranslation((BooleanLiteral) exp);
			assert result != null;
			return result;

		} else if (exp instanceof FunctionApplication) {
			FunctionApplication func = ((FunctionApplication) exp);
			final Term result;
			Map<String, Expression[]> attributes = m_Boogie2SmtSymbolTable.getAttributes(func.getIdentifier());
			String overapproximation = Boogie2SmtSymbolTable.checkForAttributeDefinedIdentifier(attributes, s_Overapproximation );
			if (m_OverapproximateFunctions || overapproximation != null) {
				Sort resultSort = m_TypeSortTranslator.getSort(exp.getType(), exp);
				TermVariable auxVar = m_VariableManager.constructFreshTermVariable(func.getIdentifier(), resultSort);
				m_AuxVars.add(auxVar);
				m_Overapproximations.put(overapproximation, exp.getLocation());
				result = auxVar;
			} else {
				BigInteger[] indices = Boogie2SmtSymbolTable.checkForIndices(attributes);
				IType[] argumentTypes = new IType[func.getArguments().length];
				for (int i = 0; i < func.getArguments().length; i++) {
					argumentTypes[i] = func.getArguments()[i].getType();
				}

				Sort[] params = new Sort[func.getArguments().length];
				for (int i = 0; i < func.getArguments().length; i++) {
					params[i] = m_TypeSortTranslator.getSort(func.getArguments()[i].getType(), exp);
				}
				
				Term[] parameters = new Term[func.getArguments().length];
				for (int i = 0; i < func.getArguments().length; i++) {
					parameters[i] = translate(func.getArguments()[i]);
				}

				String funcSymb = m_OperationTranslator.funcApplication(func.getIdentifier(), argumentTypes);
				if (funcSymb == null) {
					throw new IllegalArgumentException("unknown function" + func.getIdentifier());
				}
//				result = m_Script.term(funcSymb, indices, null, parameters);
				// overkill, this should be called only for bitvector operations.
				result = SmtUtils.termWithLocalSimplification(m_Script, funcSymb, indices, parameters);
			}
			return result;
		} else if (exp instanceof IdentifierExpression) {
			IdentifierExpression var = (IdentifierExpression) exp;
			assert var.getDeclarationInformation() != null : " no declaration information";
			Term result = getSmtIdentifier(var.getIdentifier(), var.getDeclarationInformation(), isOldContext(), exp);
			assert result != null;
			return result;

		} else if (exp instanceof IntegerLiteral) {
			Term result = m_OperationTranslator.integerTranslation((IntegerLiteral) exp);
			assert result != null;
			return result;

		} else if (exp instanceof IfThenElseExpression) {
			IfThenElseExpression ite = (IfThenElseExpression) exp;
			Term cond = translate(ite.getCondition());
			Term thenPart = translate(ite.getThenPart());
			Term elsePart = translate(ite.getElsePart());
			Term result = Util.ite(m_Script, cond, thenPart, elsePart);
			assert result != null;
			return result;

		} else if (exp instanceof QuantifierExpression) {
			// throw new
			// UnsupportedOperationException("QuantifierExpression not implemented yet");
			QuantifierExpression quant = (QuantifierExpression) exp;
			String[] typeParams = quant.getTypeParams();
			VarList[] variables = quant.getParameters();
			int numvars = typeParams.length;
			for (int i = 0; i < variables.length; i++)
				numvars += variables[i].getIdentifiers().length;
			TermVariable[] vars = new TermVariable[numvars];
			// TODO is this really unused code
			// HashMap<String,Term> newVars = new HashMap<String, Term>();
			int offset = 0;
			// for (int j = 0; j < typeParams.length; j++) {
			// vars[offset] = m_Script.createTermVariable("q" +
			// quoteId(typeParams[j]), intSort);
			// typeStack.push(vars[offset]);
			// offset++;
			// }
			m_QuantifiedVariables.beginScope();
			for (int i = 0; i < variables.length; i++) {
				IType type = variables[i].getType().getBoogieType();
				Sort sort = m_TypeSortTranslator.getSort(type, exp);
				for (int j = 0; j < variables[i].getIdentifiers().length; j++) {
					String identifier = variables[i].getIdentifiers()[j];
					String smtVarName = "q" + Boogie2SMT.quoteId(variables[i].getIdentifiers()[j]);
					vars[offset] = m_Script.variable(smtVarName, sort);
					m_QuantifiedVariables.put(identifier, vars[offset]);
					offset++;
				}
			}
			Term form = translate(quant.getSubformula());

			Attribute[] attrs = quant.getAttributes();
			int numTrigs = 0;
			for (Attribute a : attrs) {
				if (a instanceof Trigger)
					numTrigs++;
			}
			Term[][] triggers = new Term[numTrigs][];
			offset = 0;
			for (Attribute a : attrs) {
				if (a instanceof Trigger) {
					Expression[] trigs = ((Trigger) a).getTriggers();
					Term[] smttrigs = new Term[trigs.length];
					for (int i = 0; i < trigs.length; i++) {
						Term trig = translate(trigs[i]);
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
			m_QuantifiedVariables.endScope();

			Term result = null;
			try {
				result = quant.isUniversal() ? m_Script.quantifier(Script.FORALL, vars, form, triggers) : m_Script
						.quantifier(Script.EXISTS, vars, form, triggers);
			} catch (SMTLIBException e) {
				if (e.getMessage().equals("Cannot create quantifier in quantifier-free logic")) {
					Boogie2SMT.reportUnsupportedSyntax(exp, "Setting does not support quantifiers", mServices);
					throw e;
				} else {
					throw new AssertionError();
				}
			}
			assert (result.toString() instanceof Object);
			return result;
		} else {
			throw new AssertionError("Unsupported expression " + exp);
		}
	}
	
	abstract class TranslationResult {
		private final Map<String, ILocation> m_Overappoximations;
		private final Collection<TermVariable> m_AuxiliaryVars;
		public TranslationResult(Map<String, ILocation> overapproximations,
				Collection<TermVariable> auxiliaryVars) {
			super();
			assert auxiliaryVars != null;
			m_Overappoximations = overapproximations;
			m_AuxiliaryVars = auxiliaryVars;
		}
		public Map<String, ILocation> getOverappoximations() {
			return m_Overappoximations;
		}
		public Collection<TermVariable> getAuxiliaryVars() {
			return m_AuxiliaryVars;
		}
	}
	
	public class SingleTermResult extends TranslationResult {
		private final Term m_Term;
		public SingleTermResult(Map<String, ILocation> overapproximations,
				Collection<TermVariable> auxiliaryVars, Term term) {
			super(overapproximations, auxiliaryVars);
			m_Term = term;
		}
		public Term getTerm() {
			return m_Term;
		}
	}
	
	public class MultiTermResult extends TranslationResult {
		private final Term[] m_Terms;
		public MultiTermResult(Map<String, ILocation> overapproximations,
				Collection<TermVariable> auxiliaryVars, Term[] terms) {
			super(overapproximations, auxiliaryVars);
			m_Terms = terms;
		}
		public Term[] getTerms() {
			return m_Terms;
		}
	}
}
