package local.stalin.plugins.generator.traceabstraction;

import java.io.PrintWriter;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import org.apache.log4j.Logger;

import local.stalin.automata.nwalibrary.NestedRun;
import local.stalin.automata.nwalibrary.NestedWord;
import local.stalin.core.api.StalinServices;
import local.stalin.logic.ApplicationTerm;
import local.stalin.logic.Formula;
import local.stalin.logic.FormulaUnFleterer;
import local.stalin.logic.SMTLibBase;
import local.stalin.logic.TermVariable;
import local.stalin.logic.Theory;
import local.stalin.plugins.generator.rcfgbuilder.CallAnnot;
import local.stalin.plugins.generator.rcfgbuilder.IProgramState;
import local.stalin.plugins.generator.rcfgbuilder.TransAnnot;
import local.stalin.plugins.generator.rcfgbuilder.TransFormula;

public class NestedSsaBuilder {
	
	private static Logger s_Logger = 
		StalinServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	
	final Theory m_Theory;
	final Map<ApplicationTerm, String> m_Constants2VarNames =
									new HashMap<ApplicationTerm, String>();
	final Map<ApplicationTerm, String> m_Constants2OldVarNames =
									new HashMap<ApplicationTerm, String>();
	final Formula[] m_ssa;
	final NestedWord<TransAnnot> m_counterexample;
	final Stack<Map<String,ApplicationTerm>> currentVersionStack =
									new Stack<Map<String,ApplicationTerm>>();
	Map<String,ApplicationTerm> currentVarVersion;
	final Stack<Integer> startOfCallingContextStack =
									new Stack<Integer>();
	final Map<String,ApplicationTerm> currentGlobalVarVersion =
									new HashMap<String,ApplicationTerm>();
	final Map<String,ApplicationTerm> currentOldVarVersion =
									new HashMap<String,ApplicationTerm>();
	Integer startOfCallingContext;
	final Set<String> m_GlobalVars;
	final Map<Integer,Formula> localVarAssignment =
									new HashMap<Integer,Formula>();
	final Map<Integer,Formula> globalOldVarAssignment =
									new HashMap<Integer,Formula>();
	
	final PrintWriter m_IterationPW;
	final boolean m_Dump2File;
	
	

	public NestedSsaBuilder(SmtManager smtManager,
							NestedWord<TransAnnot> counterexample,
							PrintWriter iterationPW,
							boolean dump2File) {
		m_Theory = smtManager.getTheory();
		m_counterexample = counterexample;
		m_ssa = new Formula[counterexample.length()];
		m_GlobalVars = smtManager.getGlobalVars().keySet();
		m_IterationPW = iterationPW;
		m_Dump2File = dump2File;
	}
	
	private static String quoteMinusOne(int index) {
		if (index >= 0) {
			return Integer.toString(index);
		}
		else if (index == -1) {
			return "init";
		}
		else {
			throw new IllegalArgumentException();
		}
	}

	private static ApplicationTerm getVarVersion(Theory theory,
													  String varName,
													  TermVariable tv,
													  int index) {
		String name = "v_"+SMTLibBase.quoteId(varName)+"_"+quoteMinusOne(index);
		return SmtManager.getConstant(theory, name, tv.getSort());
	}
	
	private static ApplicationTerm getOldVarVersion(Theory theory,
														 String varName,
														 TermVariable tv,
														 int index) {
		String name = "v_"+SMTLibBase.quoteId(varName)+"_"+quoteMinusOne(index)+"Old";
		return SmtManager.getConstant(theory, name, tv.getSort());
	}
	


	private ApplicationTerm getCurrentVarVersion(String varName,
															TermVariable tv) {
		if (m_GlobalVars.contains(varName)) {
			if (currentGlobalVarVersion.containsKey(varName)) {
				return currentGlobalVarVersion.get(varName);
			}
			else {
				return getVarVersion(m_Theory, varName, tv, -1);
			}
		}
		else { //case varName is no global var
			if (currentVarVersion.containsKey(varName)) {
				return currentVarVersion.get(varName);
			}
			else {
				return getVarVersion(m_Theory, varName, tv, startOfCallingContext);
			}
		}
	}
	
	private ApplicationTerm getCurrentOldVarVersion(String varName,
															TermVariable tv) {
		// we do not use a special old variable in the lowest calling context
		if (startOfCallingContext == -1) {
			return getVarVersion(m_Theory, varName, tv, startOfCallingContext);
		}
		else {
			return currentOldVarVersion.get(varName);
		}
	}
	
	
	private ApplicationTerm setCurrentOldVarVersion(String varName, 
															TermVariable tv) {
		ApplicationTerm var = 
					getOldVarVersion(m_Theory,varName,tv,startOfCallingContext);
		currentOldVarVersion.put(varName,var);
		return var; 
	}
	
	private ApplicationTerm setCurrentVarVersion(String varName, int index,
															TermVariable tv) {
		ApplicationTerm var = getVarVersion(m_Theory, varName, tv, index);
		if (m_GlobalVars.contains(varName)) {
			currentGlobalVarVersion.put(varName, var);
		}
		else {
			currentVarVersion.put(varName,var);
		}
		return var; 
	}
	
	
	

	
	
	public void buildSSA() {
		startOfCallingContext = -1;
		currentVarVersion = new HashMap<String,ApplicationTerm>();
		
		for (int i=0; i<m_counterexample.length(); i++) {
			TransAnnot symbol = m_counterexample.getSymbolAt(i);
			
			TransFormula tf = symbol.getTransitionFormula();
			
			VariableVersioneer tfVV = new VariableVersioneer(tf);
			tfVV.versionInVars();
			tfVV.versionOldVars();
			
			if (m_counterexample.isCallPosition(i)) {
				CallAnnot call = (CallAnnot) symbol;
				TransFormula OldVarEq = call.getOldVarsEquality();
				VariableVersioneer initOldVarsVV = 
											new VariableVersioneer(OldVarEq);
				VariableVersioneer initGlobalVarsVV = 
											new VariableVersioneer(OldVarEq);
				startOfCallingContextStack.push(startOfCallingContext);
				startOfCallingContext = i;
				initOldVarsVV.computeOldVarUpdate();
				globalOldVarAssignment.put(i, initOldVarsVV.getVersioneeredFormula());
				initGlobalVarsVV.versionOldVars();
				initGlobalVarsVV.versionAssignedVars(i);
				m_ssa[i] = initGlobalVarsVV.getVersioneeredFormula();
				currentVersionStack.push(currentVarVersion);
				currentVarVersion = new HashMap<String,ApplicationTerm>();
			}
			if (m_counterexample.isReturnPosition(i)) {
				currentVarVersion = currentVersionStack.pop();
				startOfCallingContext = startOfCallingContextStack.pop();
			}
			tfVV.versionAssignedVars(i);
			tfVV.replaceRemaningTermVariables(i);
			if (m_counterexample.isCallPosition(i)) {
				localVarAssignment.put(i, tfVV.getVersioneeredFormula());
			}
			else {
				m_ssa[i] = tfVV.getVersioneeredFormula();
			}
//			s_Logger.debug("Formula"+i+": "+m_ssa[i]);
//			FormulaUnFleterer unflet = new FormulaUnFleterer(m_Theory);
//			s_Logger.debug("UnFletedFormula"+i+": "+unflet.unflet(m_ssa[i]));
		}
		if (m_Dump2File) {
			dumpSSA();
		}
	}
	
	public Map<ApplicationTerm, String> getConstants2VarNames() {
		return m_Constants2VarNames;
	}

	public Map<ApplicationTerm, String> getConstants2OldVarNames() {
		return m_Constants2OldVarNames;
	}

	public Formula[] getSSA() {
		return m_ssa;
	}
	
	public Map<Integer, Formula> getLocalVarAssignment() {
		return localVarAssignment;
	}


	public Map<Integer, Formula> getGlobalOldVarAssignment() {
		return globalOldVarAssignment;
	}
	
	
	
	private void dumpSSA() {
		String line;
		int indentation = 0;
		FormulaUnFleterer unflet = new FormulaUnFleterer(m_Theory);
		try {
			line = "===== Nested SSA =====";
			s_Logger.debug(line);
			m_IterationPW.println(line);
			for (int i=0; i<m_ssa.length; i++) {
//				line = CegarLoop.addIndentation(indentation, 
//						"Location " + i + ": " + m_run.getStateAtPosition(translatedPosition).getContent().getLocationName());
//				s_Logger.debug(line);
//				m_IterationPW.println(line);
				if (m_counterexample.isCallPosition(i)) {
					indentation++;
					line = CegarLoop.addIndentation(indentation, 
							"LocalVariableAssignment"+i+": "+unflet.unflet(localVarAssignment.get(i)).toString());
					s_Logger.debug(line);
					m_IterationPW.println(line);
					line = CegarLoop.addIndentation(indentation, 
							"GlobalOld-VariableAssignment"+i+": "+unflet.unflet(globalOldVarAssignment.get(i)).toString());
					s_Logger.debug(line);
					m_IterationPW.println(line);
					line = CegarLoop.addIndentation(indentation, 
							"GlobalVariableAssignment"+i+": "+unflet.unflet(m_ssa[i]).toString());
					s_Logger.debug(line);
					m_IterationPW.println(line);
				} else if (m_counterexample.isReturnPosition(i)) {
					line = CegarLoop.addIndentation(indentation, 
							"LocalVariableAssignment"+i+": "+unflet.unflet(m_ssa[i]).toString());
					s_Logger.debug(line);
					m_IterationPW.println(line);
					indentation--;
				} else 	{
					line = CegarLoop.addIndentation(indentation, 
						"Formula "+i+": "+unflet.unflet(m_ssa[i]).toString());
					s_Logger.debug(line);
					m_IterationPW.println(line);
				}
			}
			m_IterationPW.println("");
			m_IterationPW.println("");
		} finally {
			m_IterationPW.flush();
		}
	}
	
	
	
	
	
	
	
	
	
	private class VariableVersioneer {
		private final Map<String,TermVariable> m_inVars;
		private final Map<String,TermVariable> m_outVars;
		private final Map<String,TermVariable> m_oldVars;
		private final Set<String> m_assignedVars;
		private final Set<TermVariable> m_vars;
		private Formula m_formula;
		private Set<TermVariable> letedVars = new HashSet<TermVariable>();
		
		public VariableVersioneer(TransFormula tf) {
			m_inVars = tf.getInVars();
			m_outVars = tf.getOutVars();
			m_oldVars = tf.getOldVars();
			m_assignedVars = tf.getAssignedVars();
			m_vars = tf.getVars();	
			m_formula = tf.getFormula();
		}
		
		public void versionInVars() {
			for (String name : m_inVars.keySet()) {
				TermVariable tv = m_inVars.get(name);
				ApplicationTerm var = getCurrentVarVersion(name,tv);
				m_formula = m_Theory.let(tv, var, m_formula);
				letedVars.add(tv);
				m_Constants2VarNames.put(var, name);
			}
		}
		
		public void versionOldVars() {
			for (String name : m_oldVars.keySet()) {
				TermVariable tv = m_oldVars.get(name);
				ApplicationTerm var = getCurrentOldVarVersion(name,tv);
				m_formula = m_Theory.let(tv, var, m_formula);
				letedVars.add(tv);
				m_Constants2OldVarNames.put(var, name);
			}
		}
		
		public void versionAssignedVars(int currentPos) {
			for (String name : m_assignedVars) {
				TermVariable tv = m_outVars.get(name);
				ApplicationTerm var = setCurrentVarVersion(name,currentPos,tv);
				m_formula = m_Theory.let(tv, var, m_formula);
				letedVars.add(tv);
				m_Constants2VarNames.put(var, name);
			}
		}
		
		public void replaceRemaningTermVariables(int currentPos) {
			for (TermVariable tv : m_vars) {
				if (!letedVars.contains(tv)) {
					String name = currentPos + "fresh_" + tv.getName();
					ApplicationTerm var = 
							SmtManager.getConstant(m_Theory,name,tv.getSort());
					m_formula = m_Theory.let(tv, var, m_formula);
				}
			}

		}
		
		public void computeOldVarUpdate() {
			for (String name : m_outVars.keySet()) {
				TermVariable tv = m_outVars.get(name);
				ApplicationTerm var = getCurrentVarVersion(name,tv);
				m_formula = m_Theory.let(tv, var, m_formula);
				letedVars.add(tv);
				m_Constants2VarNames.put(var, name);
			}
			
			for (String name : m_oldVars.keySet()) {
				TermVariable tv = m_oldVars.get(name);
				ApplicationTerm var = setCurrentOldVarVersion(name,tv);
				m_formula = m_Theory.let(tv, var, m_formula);
				letedVars.add(tv);
				m_Constants2OldVarNames.put(var, name);
			}
		}
		
		public Formula getVersioneeredFormula() {
			return (new FormulaUnFleterer(m_Theory)).unflet(m_formula);
		}

	}
	

}
