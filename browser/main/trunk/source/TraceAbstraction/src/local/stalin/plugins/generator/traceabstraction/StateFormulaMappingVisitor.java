package local.stalin.plugins.generator.traceabstraction;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import local.stalin.logic.ApplicationTerm;
import local.stalin.logic.Formula;
import local.stalin.logic.ITETerm;
import local.stalin.logic.NumeralTerm;
import local.stalin.logic.PredicateAtom;
import local.stalin.logic.ProgramVariableTerm;
import local.stalin.logic.RationalTerm;
import local.stalin.logic.Term;
import local.stalin.logic.TermVariable;
import local.stalin.logic.VariableTerm;
import local.stalin.logic.FormulaWalker.SymbolVisitor;
import local.stalin.plugins.generator.rcfgbuilder.smt.BoogieVar2SmtVar;

/**
 * Replaces constant symbols by constant symbols according to the following
 * scheme.
 * <p>
 * The input is:
 * <ul>
 * <li> constants2VarNames is mapping from SMT constants (where the constants 
 * don't have nice names e.g because the were created to represent indexed
 * variables) to Boogie variable identifiers
 * <li> constants2OldVarNames is mapping from SMT constants to Boogie
 * old-variable identifiers
 * <li> boogieVar2SmtVar contains a mapping from Boogie variable identifiers
 * to SMT constants (where the constants have a succinct and meaningful name )
 * </ul>
 * If the StateFormulaMappingVisitor is applied to a constant <i>c</i> then
 * <ul>  
 * <li> <i>c</i> is replaced by the corresponding constant specified in
 *  boogieVar2SmtVar if <i>c</i> a key of constants2VarNames
 * <li> otherwise <i>c</i> is replaced by the corresponding constant specified
 *  in boogieVar2SmtVar if <i>c</i> a key of constants2OldVarNames
 * <li>  otherwise it is not replaced
 * </ul>
 * 
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class StateFormulaMappingVisitor implements SymbolVisitor {

	Map<ApplicationTerm, String> m_Constants2VarNames;
	Map<ApplicationTerm, String> m_Constants2OldVarNames;
//	Theory m_Theory;

	private final BoogieVar2SmtVar m_VariableMapping;
	
	Set<String> m_Vars;
	Set<String> m_OldVars;
	
	
	public StateFormulaMappingVisitor(
//						Theory theory,
						BoogieVar2SmtVar boogieVar2SmtVar,
						Map<ApplicationTerm, String> constants2VarNames,
						Map<ApplicationTerm, String> constants2OldVarNames)
	{
//		m_Theory = theory;
		m_VariableMapping = boogieVar2SmtVar;
		m_Constants2VarNames = constants2VarNames;
		m_Constants2OldVarNames = constants2OldVarNames;
		m_Vars = new HashSet<String>();
		m_OldVars = new HashSet<String>();
	}

	public void initialize() {
		m_Vars = new HashSet<String>();
		m_OldVars = new HashSet<String>();
	}
	
	public Set<String> getVars() {
		return m_Vars;
	}
	
	public Set<String> getOldVars() {
		return m_OldVars;
	}
	
	
	
	@Override
	public void done(Term input) {}

	@Override
	public void done(PredicateAtom pa) {}

	@Override
	public void endscope(TermVariable tv) {}

	@Override
	public void endscopes(TermVariable[] tvs) {}

	@Override
	public void let(TermVariable tv, Term mval) {}

	@Override
	public Formula predicate(PredicateAtom pa) {
		return null;
	}
	
	@Override
	public void quantifier(TermVariable[] tvs) {}

	@Override
	public Term term (Term input) {
		if (input instanceof ApplicationTerm) {
			ApplicationTerm indexedConstant = (ApplicationTerm) input;
			if (m_Constants2VarNames.containsKey(input)) {
				String varName = m_Constants2VarNames.get(input);
				m_Vars.add(varName);
				ApplicationTerm constant =	m_VariableMapping.getVariable(
											varName, indexedConstant.getSort());
				return constant;
			}
			else if (m_Constants2OldVarNames.containsKey(input)) {
				String oldVarName = m_Constants2OldVarNames.get(input);
				m_OldVars.add(oldVarName);
				ApplicationTerm constant =	m_VariableMapping.getOldVariable(
										oldVarName, indexedConstant.getSort());
				return constant;
			}
			else {
				return null;
			}
		}
		else if (input instanceof ITETerm) {
			return null;
		}
		else if (input instanceof NumeralTerm) {
			return input;
		}
		else if (input instanceof ProgramVariableTerm) {
			return input;
		}
		else if (input instanceof RationalTerm) {
			return input;
		}
		else if (input instanceof VariableTerm) {
			return input;
		}
		else {
			throw new IllegalArgumentException("unknown type of Term");
		}
	}

	@Override
	public boolean unflet() {
		return false;
	}

	@Override
	public boolean unlet() {
		return false;
	}
	
}
