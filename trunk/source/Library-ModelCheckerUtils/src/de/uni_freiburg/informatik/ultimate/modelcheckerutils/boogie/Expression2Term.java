package de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie;

import de.uni_freiburg.informatik.ultimate.boogie.type.PrimitiveType;
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
import de.uni_freiburg.informatik.ultimate.util.ScopedHashMap;


/**
 * Translate a Boogie Expression into an SMT Term. 
 * Use the here defined interface IndentifierResolver to translate identifier
 * expressions.
 * @author Matthias Heizmann
 *
 */
public class Expression2Term {
	
	public interface IdentifierTranslator {
		public Term getSmtIdentifier(String id, DeclarationInformation declInfo, boolean isOldContext, BoogieASTNode boogieASTNode);
	}
	
	private final ScopedHashMap<String, TermVariable> m_QuantifiedVariables = 
			new ScopedHashMap<String, TermVariable>();
	
	private final Script m_Script;
	private final TypeSortTranslator m_TypeSortTranslator;
	private final IdentifierTranslator[] m_SmtIdentifierProviders;
	private final Term[] m_Result;
	
	/**
	 * Count the height of current old(.) expressions. As long as this is
	 * strictly greater than zero we are have to consider all global vars as
	 * oldvars.   
	 */
	private int m_OldContextScopeDepth = 0;
	

	
	public Expression2Term(IdentifierTranslator[] identifierTranslators, 
			Script script, 
			TypeSortTranslator typeSortTranslator, Expression... expressions) {
		super();
		m_Script = script;
		m_TypeSortTranslator = typeSortTranslator;
		m_SmtIdentifierProviders = identifierTranslators;
		m_Result = new Term[expressions.length];
		for (int i=0; i<expressions.length; i++) {
			m_Result[i] = translate(expressions[i]);
		}
	}
	
	
	public Term getTerm() {
		if (m_Result.length != 1) {
			throw new AssertionError("you translated not exactly one expression");
		}
		return m_Result[0];
	}
	
	public Term[] getTerms() {
		return m_Result;
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
			assert (result.toString() instanceof Object);
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

			if (op == BinaryExpression.Operator.COMPEQ) {
				// if
				// (binexp.getLeft().getType().equals(PrimitiveType.boolType))
				return m_Script.term("=", translate(binexp.getLeft()), translate(binexp.getRight()));
				// else
				// return script.equals(translateTerm(binexp.getLeft()),
				// translateTerm(binexp.getRight()));
			} else if (op == BinaryExpression.Operator.COMPGEQ) {
				return m_Script.term(">=", translate(binexp.getLeft()), translate(binexp.getRight()));
			} else if (op == BinaryExpression.Operator.COMPGT) {
				return m_Script.term(">", translate(binexp.getLeft()), translate(binexp.getRight()));
			} else if (op == BinaryExpression.Operator.COMPLEQ) {
				return m_Script.term("<=", translate(binexp.getLeft()), translate(binexp.getRight()));
			} else if (op == BinaryExpression.Operator.COMPLT) {
				return m_Script.term("<", translate(binexp.getLeft()), translate(binexp.getRight()));
			} else if (op == BinaryExpression.Operator.COMPNEQ) {
				if (binexp.getLeft().getType().equals(PrimitiveType.boolType)) {
					return m_Script.term("xor", translate(binexp.getLeft()), translate(binexp.getRight()));
				} else {
					return Util.not(m_Script,
							m_Script.term("=", translate(binexp.getLeft()), translate(binexp.getRight())));
				}
				// } else if (op == BinaryExpression.Operator.COMPPO ){
				// return script.atom(partOrder,
				// translateTerm(binexp.getLeft()),
				// translateTerm(binexp.getRight()));
			} else if (op == BinaryExpression.Operator.LOGICAND) {
				return Util.and(m_Script, translate(binexp.getLeft()), translate(binexp.getRight()));
			} else if (op == BinaryExpression.Operator.LOGICOR) {
				return Util.or(m_Script, translate(binexp.getLeft()), translate(binexp.getRight()));
			} else if (op == BinaryExpression.Operator.LOGICIMPLIES) {
				return Util.implies(m_Script, translate(binexp.getLeft()), translate(binexp.getRight()));
			} else if (op == BinaryExpression.Operator.LOGICIFF) {
				return m_Script.term("=", translate(binexp.getLeft()), translate(binexp.getRight()));
			} else if (op == BinaryExpression.Operator.ARITHDIV) {
				IType lhsType = binexp.getLeft().getType();
				if (lhsType instanceof PrimitiveType) {
					PrimitiveType primType = (PrimitiveType) lhsType;
					if (primType.getTypeCode() == PrimitiveType.INT) {
						return m_Script.term("div", translate(binexp.getLeft()), translate(binexp.getRight()));
					} else if (primType.getTypeCode() == PrimitiveType.REAL) {
						return m_Script.term("/", translate(binexp.getLeft()), translate(binexp.getRight()));
					} else {
						throw new AssertionError("ARITHDIV of this type not allowed");
					}
				} else {
					throw new AssertionError("ARITHDIV of this type not allowed");
				}
			} else if (op == BinaryExpression.Operator.ARITHMINUS) {
				return m_Script.term("-", translate(binexp.getLeft()), translate(binexp.getRight()));
			} else if (op == BinaryExpression.Operator.ARITHMOD) {
				return m_Script.term("mod", translate(binexp.getLeft()), translate(binexp.getRight()));
			} else if (op == BinaryExpression.Operator.ARITHMUL) {
				return m_Script.term("*", translate(binexp.getLeft()), translate(binexp.getRight()));
			} else if (op == BinaryExpression.Operator.ARITHPLUS) {
				return m_Script.term("+", translate(binexp.getLeft()), translate(binexp.getRight()));
			} else if (op == BinaryExpression.Operator.BITVECCONCAT) {
				/* TODO */
				throw new UnsupportedOperationException("BITVECCONCAT not implemented");
			} else {
				throw new AssertionError("Unsupported binary expression " + exp);
			}

		} else if (exp instanceof UnaryExpression) {
			UnaryExpression unexp = (UnaryExpression) exp;
			UnaryExpression.Operator op = unexp.getOperator();
			if (op == UnaryExpression.Operator.LOGICNEG) {
				return Util.not(m_Script, translate(unexp.getExpr()));
			} else if (op == UnaryExpression.Operator.ARITHNEGATIVE) {
				// FunctionSymbol fun_symb = script.getFunction("-", intSort);
				return m_Script.term("-", translate(unexp.getExpr()));
			} else if (op == UnaryExpression.Operator.OLD) {
				m_OldContextScopeDepth++;
				Term term = translate(unexp.getExpr());
				m_OldContextScopeDepth--;
				return term;
			} else
				throw new AssertionError("Unsupported unary expression " + exp);

		} else if (exp instanceof RealLiteral) {
			Term result = m_Script.decimal(((RealLiteral) exp).getValue());
			assert result != null;
			return result;

		} else if (exp instanceof BitvecLiteral) {
			// TODO
			throw new UnsupportedOperationException("BitvecLiteral not implemented");

		} else if (exp instanceof BitVectorAccessExpression) {
			// TODO
			throw new UnsupportedOperationException("BitVectorAccess not implemented");

		} else if (exp instanceof BooleanLiteral) {
			Term result = ((BooleanLiteral) exp).getValue() ? m_Script.term("true") : m_Script.term("false");
			assert result != null;
			return result;

		} else if (exp instanceof FunctionApplication) {
			FunctionApplication func = ((FunctionApplication) exp);
			// if (itefunctions.contains(func.getIdentifier())) {
			// Formula cond = translateFormula(func.getArguments()[0]);
			// Term t = translateTerm(func.getArguments()[1]);
			// Term e = translateTerm(func.getArguments()[2]);
			// /* Special case: If-then-else */
			// return script.ite(cond, t, e);
			// }
			Sort[] params = new Sort[func.getArguments().length];
			for (int i = 0; i < func.getArguments().length; i++) {
				params[i] = m_TypeSortTranslator.getSort(func.getArguments()[i].getType(), exp);
			}
			String funcSymb = func.getIdentifier();
			Term[] parameters = new Term[func.getArguments().length];
			for (int i = 0; i < func.getArguments().length; i++) {
				parameters[i] = translate(func.getArguments()[i]);
			}
			Term result = m_Script.term(funcSymb, parameters);
			assert (result.toString() instanceof Object);
			return result;

		} else if (exp instanceof IdentifierExpression) {
			IdentifierExpression var = (IdentifierExpression) exp;
			assert var.getDeclarationInformation() != null : " no declaration information";
			Term result = getSmtIdentifier(var.getIdentifier(), var.getDeclarationInformation(), isOldContext(), exp);
			assert result != null;
			return result;

		} else if (exp instanceof IntegerLiteral) {
			Term result = m_Script.numeral(((IntegerLiteral) exp).getValue());
			assert result != null;
			return result;

		} else if (exp instanceof IfThenElseExpression) {
			IfThenElseExpression ite = (IfThenElseExpression) exp;
			Term cond = translate(ite.getCondition());
			Term thenPart = translate(ite.getThenPart());
			Term elsePart = translate(ite.getElsePart());
			Term result = m_Script.term("ite", cond, thenPart, elsePart);
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
					Boogie2SMT.reportUnsupportedSyntax(exp, "Setting does not support quantifiers");
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
}
