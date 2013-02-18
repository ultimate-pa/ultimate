package local.stalin.plugins.generator.traceabstraction;

import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import local.stalin.SMTInterface.SMTInterface;
import local.stalin.automata.nwalibrary.NestedRun;
import local.stalin.automata.nwalibrary.NestedWord;
import local.stalin.core.api.StalinServices;
import local.stalin.logic.ApplicationTerm;
import local.stalin.logic.Atom;
import local.stalin.logic.Formula;
import local.stalin.logic.FormulaUnFleterer;
import local.stalin.logic.FormulaWalker;
import local.stalin.logic.Theory;
import local.stalin.plugins.generator.rcfgbuilder.IProgramState;
import local.stalin.plugins.generator.rcfgbuilder.ProgramPoint;
import local.stalin.plugins.generator.rcfgbuilder.StateFormula;
import local.stalin.plugins.generator.rcfgbuilder.TransAnnot;
import local.stalin.plugins.generator.rcfgbuilder.smt.BoogieVar2SmtVar;

import org.apache.log4j.Logger;

public class NestedInterpolantsBuilder {
	
	private static Logger s_Logger = 
		StalinServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	
	final Theory m_Theory;
	final SMTInterface m_SmtInterface;
	final BoogieVar2SmtVar m_BoogieVar2SmtVar;
	final Formula[] m_ssa;
	final Map<Integer,Formula> m_localVarAssignment;
	final Map<Integer,Formula> m_globalOldVarAssignment;
	final StateFormulaMappingVisitor m_sfmv;

	final NestedWord<TransAnnot> m_NestedWord;
	final NestedRun<TransAnnot, IProgramState> m_run;
	final boolean m_Interprocedural;
	final boolean InterpolAllLoc;
	final Set<ProgramPoint> m_cutpoints;
	final Formula[] m_NestedInterpolants;
	final PrintWriter m_IterationPW;
	final int m_Iteration;
	int m_InterpolationProblem = 0;
	final boolean m_Dump2File;
	final String m_DumpPath;
	
	private StateFormula[] m_Interpolants;
	private int m_Satisfiable = -25;

	public NestedInterpolantsBuilder(SmtManager smtManager,
									 NestedRun<TransAnnot, IProgramState> run,
									 Formula[] ssa,
									 Map<Integer,Formula> localVarAssignment,
									 Map<Integer,Formula> globalOldVarAssignment,
									 Map<ApplicationTerm, String> const2VarNames,
									 Map<ApplicationTerm, String> const2OldVarNames,
									 boolean interprocedural,
									 boolean interpolateAllLocations,
									 Set<ProgramPoint> cutpoints,
									 int iteration,
									 boolean dump2File,
									 String dumpPath,
									 PrintWriter iterationPW) {
		m_Theory = smtManager.getTheory();
		m_SmtInterface = smtManager.getSmtInterface();
		m_BoogieVar2SmtVar = smtManager.getBoogieVar2SmtVar();
		m_NestedWord = run.getNestedWord();
		m_run = run;
		m_ssa = ssa;
		m_localVarAssignment = localVarAssignment;
		m_globalOldVarAssignment = globalOldVarAssignment;
		m_Interprocedural = interprocedural;
		m_cutpoints = cutpoints;
		InterpolAllLoc = interpolateAllLocations;
		m_NestedInterpolants = new Formula[m_ssa.length+1];
		m_sfmv = new StateFormulaMappingVisitor(m_BoogieVar2SmtVar,const2VarNames,const2OldVarNames);
		m_Iteration = iteration;
		m_Dump2File = dump2File;
		m_DumpPath = dumpPath;
		m_IterationPW = iterationPW;
		m_Interpolants = computeNestedInterpolants();
	}
	
	public StateFormula[] getNestedInterpolants() {
		assert (m_Interpolants == null || 
				m_Satisfiable == SMTInterface.SMT_UNSAT);
		assert (m_Interpolants != null || 
				m_Satisfiable == SMTInterface.SMT_SAT || 
				m_Satisfiable == SMTInterface.SMT_UNKNOWN);
		return m_Interpolants;
	}
	
	public int isInputSatisfiable() {
		return m_Satisfiable;
	}
	
	private List<Integer> getInterpolProbStartPositions() {
		 
		List<Integer> interpolProbStartPos = new LinkedList<Integer>();
		if (m_Interprocedural) {
			for (int i=0; i<m_run.getLength()-1; i++) {
				if (m_run.isCallPosition(i) && !m_run.isPendingCall(i)) {
					interpolProbStartPos.add(i);
				}
			}
			if (interpolProbStartPos.isEmpty() || interpolProbStartPos.get(0)!=0) {
				interpolProbStartPos.add(0, 0);
			}
		}
		else {
			interpolProbStartPos.add(0);
		}
		return interpolProbStartPos;
	}
	
	
	private StateFormula[] computeNestedInterpolants() {
		
		m_NestedInterpolants[0] = Atom.TRUE;
		m_NestedInterpolants[m_NestedInterpolants.length-1] = Atom.FALSE;
		
		List<Integer> interpolProbStartPositions = getInterpolProbStartPositions();
		
		for (Integer k: interpolProbStartPositions) {
			boolean isSat = computeInterpolantSubsequence(k);
			if (isSat) {
				if (k==0) {
					return null;
				}
				else {
					throw new AssertionError();
				}
			}
		}
		
		for (int i=0; i<m_NestedInterpolants.length; i++) {
			s_Logger.debug("NestedInterpol"+i+": "+m_NestedInterpolants[i]);
		}
		
		StateFormula[] result = computeStateFormulas();
		if (m_Dump2File) {
			dumpNestedStateFormulas(result, m_run, m_IterationPW);
		}
		return result;
	}
	
	
	private StateFormula[] computeStateFormulas() {
		int n = m_ssa.length;
		StateFormula[] result = new StateFormula[n+1];

		FormulaWalker walker = new FormulaWalker(m_sfmv, m_Theory);

		//position 0 of result
		result[0] = new StateFormula(Atom.TRUE, new HashSet<String>(0), new HashSet<String>(0));
		//position 1 to position n-1 of result
		for (int i = 1; i<n+1; i++) {
			if (m_NestedInterpolants[i] == null) {
				result[i] = new StateFormula(null,null,null);
			}
			else if (m_NestedInterpolants[i] == m_NestedInterpolants[i-1]){
				result[i] = result[i-1];
			}
			else {
				m_sfmv.initialize();
				Formula renamedInterpolant = 
									walker.process(m_NestedInterpolants[i]);
				Set<String> vars = m_sfmv.getVars();
				Set<String> oldVars = m_sfmv.getOldVars();
				result[i] =	new StateFormula(renamedInterpolant, vars, oldVars);
			}
		}
		return result;
	}

	

	

	private boolean computeInterpolantSubsequence(int k) {
		int endPos;
		if (k==0) {
			endPos = m_ssa.length-1;
		}
		else {
			assert (m_NestedWord.isCallPosition(k) && 
					!m_NestedWord.isPendingCall(k));
			endPos = m_NestedWord.getReturnPosition(k);
		}
		ArrayList<Formula> interpolProb = new ArrayList<Formula>();
		ArrayList<Integer> indexTranslation = new ArrayList<Integer>();
		Formula interproceduralLinkPendingCalls = Atom.TRUE;
		int j=0;
		interpolProb.add(j, getFormulaforPos(k));
		for (int i=k+1; i<= endPos; i++) {
			Formula iFormu = getFormulaforPos(i);
			if (m_NestedWord.isPendingCall(i)) {
				interproceduralLinkPendingCalls = m_Theory.and(interproceduralLinkPendingCalls, m_globalOldVarAssignment.get(i));
			}
			if (isInterpolatedPosition(i)) {
				j++;
				indexTranslation.add(i);
				interpolProb.add(j,iFormu);
			}
			else {
				Formula jFormu = interpolProb.get(j);
				interpolProb.set(j,m_Theory.and(jFormu,iFormu));
			}
		}
		Formula lastFormula = interpolProb.get(j);
		
		if (k !=0 ) {
			Formula precond = m_NestedInterpolants[k];
			Formula postcond = m_NestedInterpolants[endPos+1];
			Formula negPostcond = m_Theory.not(postcond);
			lastFormula = m_Theory.and(lastFormula, precond);
			lastFormula = m_Theory.and(lastFormula, negPostcond);
		}
		else {
			lastFormula = m_Theory.and(lastFormula, interproceduralLinkPendingCalls);
		}
		interpolProb.set(j,lastFormula);
		assert (interpolProb.size()-1 == indexTranslation.size());
		
		Formula[] interpolInput = interpolProb.toArray(new Formula[0]);

		if (m_Dump2File) {
			String line;
			line = "=====InterpolationProblem starting from position " + k;
			s_Logger.debug(line);
			m_IterationPW.println(line);
			dumpInterpolationInput(k, interpolInput, indexTranslation, m_run, m_Theory, m_IterationPW);
			SmtManager.dumpInterpolProblem(interpolInput, m_Iteration, k, m_DumpPath, m_Theory);
		}

		Formula[] interpolOutput;
		
		if (interpolInput.length == 1) {
			int sat = m_SmtInterface.checkSatisfiable(interpolInput[0]);
			if (sat == SMTInterface.SMT_UNSAT) {
				interpolOutput = new Formula[0];
			}
			else {
				interpolOutput = null;
			}
		}
		else if (interpolInput.length > 1) {
			interpolOutput = 
				m_SmtInterface.computeInterpolants(interpolInput, null);
		}
		else {
			throw new AssertionError();
		}
		
		if (interpolOutput == null) {
			m_Satisfiable = 
				m_SmtInterface.checkSatisfiable(conjunction(interpolInput));
			return true;
		}
		m_Satisfiable = SMTInterface.SMT_UNSAT;
		
		if (m_Dump2File) {
			dumpInterpolationOutput(k, interpolOutput, indexTranslation, m_run, m_IterationPW);
		}
		
		//TODO remove this debugging stuff
//		Formula[] test = m_NestedInterpolants; 
		for (int jj = 0; jj<indexTranslation.size(); jj++) {
			m_NestedInterpolants[indexTranslation.get(jj)] = interpolOutput[jj];
			//test[indexTranslation.get(jj)] = interpolOutput[jj];

		}
		return false;
	}
	
	//FIXME wrong - fixed?
	private boolean isInterpolatedPosition(int i) {
		if (InterpolAllLoc) {
			return true;
		}
		//interpolate for cutpoint positions
		if (m_cutpoints.contains(m_run.getStateAtPosition(i).getContent().getProgramPoint())) {
			return true;
		}
		//interpolate before calls
		if (m_NestedWord.isCallPosition(i)) {
			return true;
		}
		//interpolate after returns
		if (i>0 && m_NestedWord.isReturnPosition(i-1)) {
			return true;
		}
		return false;
	}
	

	private Formula getFormulaforPos(int i) {
		Formula iFormu = m_ssa[i];
		if (m_NestedWord.isReturnPosition(i)) {
			int callPos = m_NestedWord.getCallPosition(i);
			iFormu = m_Theory.and(iFormu, m_localVarAssignment.get(callPos));
			iFormu = m_Theory.and(iFormu, m_globalOldVarAssignment.get(callPos));
		}
		else if (m_NestedWord.isPendingCall(i)) {
			iFormu = m_Theory.and(iFormu, m_localVarAssignment.get(i));
		}
		return iFormu;
	}
	
	
	
	private static void dumpInterpolationInput(
			int offset,
			Formula[] interpolInput,
			List<Integer> indexTranslation,
			NestedRun<TransAnnot,IProgramState> run,
			Theory theory,
			PrintWriter pW) {
		String line;
		int indentation = 0;
		int translatedPosition;
		FormulaUnFleterer unflet = new FormulaUnFleterer(theory);
		try {
			line = "==Interpolation Input";
			s_Logger.debug(line);
			pW.println(line);
			for (int j=0; j<interpolInput.length; j++) {
				if (j==0) {
					translatedPosition = offset;
				}
				else {
					translatedPosition = indexTranslation.get(j-1);
				}
				line = CegarLoopSequential.addIndentation(indentation, 
						"Location " + translatedPosition + ": " + run.getStateAtPosition(translatedPosition).getContent().getProgramPoint());
				s_Logger.debug(line);
				pW.println(line);
				if (run.isCallPosition(translatedPosition)) {
					indentation++;
				}
				line = CegarLoopSequential.addIndentation(indentation, 
						unflet.unflet(interpolInput[j]).toString());
				s_Logger.debug(line);
				pW.println(line);
				if (run.isReturnPosition(translatedPosition)) {
					indentation--;
				}
			}
			if (offset != 0) {
				int returnSuccPos = run.getNestedWord().getReturnPosition(offset)+1;
				line = CegarLoopSequential.addIndentation(indentation, 
						"Location " + returnSuccPos + ": " + run.getStateAtPosition(returnSuccPos).getContent().getProgramPoint());
				s_Logger.debug(line);
				pW.println(line);
			}
			pW.println("");
			pW.println("");
		} finally {
			pW.flush();
		}
	}
	
	
	private static void dumpInterpolationOutput(
			int offset,
			Formula[] interpolOutput,
			List<Integer> indexTranslation,
			NestedRun<TransAnnot,IProgramState> run,
			PrintWriter pW) {
		assert (interpolOutput.length == indexTranslation.size());
		String line;
		int indentation = 0;
		int translatedPosition;
		try {
			line = "==Interpolation Output";
			s_Logger.debug(line);
			pW.println(line);
			for (int j=0; j<interpolOutput.length; j++) {
				translatedPosition = indexTranslation.get(j);
				if (translatedPosition>1 && run.isCallPosition(translatedPosition-1)) {
					indentation++;
				}
				line = CegarLoopSequential.addIndentation(indentation, 
						"InterpolOutput"+translatedPosition+": "+interpolOutput[j]);
				s_Logger.debug(line);
				pW.println(line);
				if (run.isReturnPosition(translatedPosition)) {
					indentation--;
				}
			}
			pW.println("");
			pW.println("");
		} finally {
			pW.flush();
		}
	}
	
	
	private static void dumpNestedStateFormulas(
			StateFormula[] stateFormulas,
			NestedRun<TransAnnot,IProgramState> run,
			PrintWriter pW) {
		assert (stateFormulas.length == run.getLength());
		String line;
		int indentation = 0;
		try {
			line = "==NestedInterpolants";
			s_Logger.debug(line);
			pW.println(line);
			for (int j=0; j<stateFormulas.length; j++) {
				line = CegarLoopSequential.addIndentation(indentation, 
						j+": "+stateFormulas[j]);
				s_Logger.debug(line);
				pW.println(line);
				if (j!= stateFormulas.length-1) {
					if (run.isCallPosition(j)) {
						indentation++;
					}
					if (run.isReturnPosition(j)) {
						indentation--;
					}
				}
			}
		} finally {
			pW.flush();
		}
	}
	
	
	private Formula conjunction(Formula[] formulas) {
		Formula result = Atom.TRUE;
		for (Formula f : formulas) {
			result = m_Theory.and(result, f);
		}
		return result;
	}
	
}
