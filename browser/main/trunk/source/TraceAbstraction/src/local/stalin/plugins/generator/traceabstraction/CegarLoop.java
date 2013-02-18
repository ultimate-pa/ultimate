package local.stalin.plugins.generator.traceabstraction;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Collection;

import local.stalin.SMTInterface.SMTInterface;
import local.stalin.automata.nwalibrary.IState;
import local.stalin.automata.nwalibrary.NestedRun;
import local.stalin.automata.nwalibrary.NestedWord;
import local.stalin.core.api.StalinServices;
import local.stalin.logic.Formula;
import local.stalin.logic.FormulaUnFleterer;
import local.stalin.model.INode;
import local.stalin.plugins.generator.rcfgbuilder.IProgramState;
import local.stalin.plugins.generator.rcfgbuilder.ProgramPoint;
import local.stalin.plugins.generator.rcfgbuilder.RootNode;
import local.stalin.plugins.generator.rcfgbuilder.StateFormula;
import local.stalin.plugins.generator.rcfgbuilder.TransAnnot;
import local.stalin.plugins.generator.traceabstraction.TAPreferences.Artifact;


import org.apache.log4j.Logger;


public abstract class CegarLoop {
	
	protected final static Logger s_Logger = 
		StalinServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	
	public enum Result { CORRECT, INCORRECT, TIMEOUT , UNKNOWN }
	
	protected final RootNode m_RootNode;
	protected final SmtManager m_SmtManager;
	
	protected final TAPreferences m_Pref;

	private final int m_MaxIterations;
	protected final int m_WatchIteration;
	
	protected final Artifact m_Artifact;
	protected final boolean m_HoareAnnotation;

	//debugging options
	protected final boolean m_DumpFormulas;
	protected final String m_DumpPath;
	
		
	protected int m_Iteration = 0;
	protected PrintWriter m_IterationPW;
	protected int m_SatProblem = 0;
	
	public int m_BiggestAbstractionIteration = 0;
	public int m_BiggestAbstractionSize = 0;
	public int m_InitialAbstractionSize = 0;
	public int m_NumberOfErrorLocations = 0;
	
	
	
	

	
	
	public int getIteration() {
		return m_Iteration;
	}

	public CegarLoop(RootNode rootNode,
			SmtManager smtManager,
			TAPreferences taPrefs) {
		m_RootNode = rootNode;
		m_SmtManager = smtManager;
		m_Pref = taPrefs;
		m_MaxIterations = taPrefs.maxIterations();
		m_WatchIteration = taPrefs.watchIteration();
		m_Artifact = taPrefs.artifact();
		m_HoareAnnotation = taPrefs.computeHoareAnnotation();
		m_DumpFormulas = taPrefs.dumpFormulas();
		m_DumpPath = taPrefs.dumpPath();
	}
	
	protected abstract void getInitialAbstraction();
	protected abstract boolean isAbstractionCorrect();
	protected abstract int isCounterexampleFeasible();
	protected abstract void constructInterpolantAutomaton();
	protected abstract void refineAbstraction();
	
	protected abstract void computeCFGHoareAnnotation();
	protected abstract INode getArtifact();
	
	public final Result iterate() {
		m_Iteration = 0;
		s_Logger.info("======== Iteration " + m_Iteration + "============");
		if (m_DumpFormulas || m_Pref.dumpAutomata()) {
			dumpInitinalize();
		}
		getInitialAbstraction();
		boolean initalAbstractionCorrect = isAbstractionCorrect();
		if (initalAbstractionCorrect) {
			return Result.CORRECT;
		}
		for (m_Iteration=1; m_Iteration<=m_MaxIterations; m_Iteration++) {
			s_Logger.info("======== Iteration " + m_Iteration + "============");
			m_SmtManager.setIteration(m_Iteration);
			m_SatProblem = -66;
			if (m_DumpFormulas || m_Pref.dumpAutomata()) {
				dumpInitinalize();
			}
			int isCounterexampleFeasible = isCounterexampleFeasible();
			if (isCounterexampleFeasible == SMTInterface.SMT_SAT) {
				return Result.INCORRECT;
			}
			if (isCounterexampleFeasible == SMTInterface.SMT_UNKNOWN) {
				return Result.UNKNOWN;
			}
			constructInterpolantAutomaton();
			refineAbstraction();
			boolean isAbstractionCorrect = isAbstractionCorrect();
			if (isAbstractionCorrect) {
				return Result.CORRECT;
			}
		}
		return Result.TIMEOUT;
	}
	
	
	
	
	
	
	private void dumpInitinalize() {
		File file = 
			new File(m_DumpPath + "/" + "iteration" + m_Iteration + ".txt");
		FileWriter fileWriter;
		try {
			fileWriter = new FileWriter(file);
			m_IterationPW = new PrintWriter(fileWriter);
		} catch (IOException e) {
			e.printStackTrace();
		} 
	}
	
	
	protected static void dumpNestedRun(NestedRun<TransAnnot,IProgramState> run,
			PrintWriter pW) {
		NestedWord<TransAnnot> counterexample = run.getNestedWord();
		ArrayList<IState<TransAnnot, IProgramState>> stateSequence = 
			run.getStateSequence();
		String line;
		int indentation = 0;
		try {
			line = "===============Run of potential Counterexample==========";
			pW.println(line);
			for (int i=0; i<counterexample.length(); i++) {

				line = addIndentation(indentation,
						"Location"+i+": " +
						stateSequence.get(i).getContent().getProgramPoint());
				s_Logger.debug(line);
				pW.println(line);
				if (counterexample.isCallPosition(i)) {
					indentation++;
				}
				line = addIndentation(indentation,
						"Statement"+i+": "+
						counterexample.getSymbolAt(i).getPrettyPrintedStatements());
				s_Logger.debug(line);
				pW.println(line);
				if (counterexample.isReturnPosition(i)) {
					indentation--;
				}
			}
			pW.println("ErrorLocation");
			pW.println("");
			pW.println("");
		} finally {
			pW.flush();
		}
	}
	
	
	
	private void dumpSsa(Formula[] ssa) {
		FormulaUnFleterer unflet = new FormulaUnFleterer(m_SmtManager.getTheory());
		try {
			m_IterationPW.println(
					"===============SSA of potential Counterexample==========");
			for (int i=0; i<ssa.length; i++) {
				m_IterationPW.println(
						"UnFletedFormula" + i + ": " +	unflet.unflet(ssa[i]));
			}
			m_IterationPW.println("");
			m_IterationPW.println("");
		} finally {
			m_IterationPW.flush();
		}
	}

	
	private void dumpStateFormulas(StateFormula[] interpolants) {
		try {
			m_IterationPW.println(
			"===============Interpolated StateFormulas==========");
			for (int i=0; i<interpolants.length; i++) {
				m_IterationPW.println(
						"Interpolant" + i + ": " +	interpolants[i]);
			}
			m_IterationPW.println("");
			m_IterationPW.println("");
		} finally {
			m_IterationPW.flush();
		}
	}
	
	
	static String addIndentation(int indentation, String s) {
		StringBuilder sb = new StringBuilder("");
		for (int i=0; i<indentation; i++) {
			sb.append("    ");
		}
		sb.append(s);
		return sb.toString();
	}

	

	
	static void dumpBackedges(ProgramPoint repLocName, int position,
			IState<TransAnnot,IProgramState> state,
			Collection<IState<TransAnnot,IProgramState>> linPredStates,
			TransAnnot transition,
			IState<TransAnnot,IProgramState> succState,
			IProgramState sf1,IProgramState sf2,
			int result,
			int iteration, int satProblem, PrintWriter iterationPW) {
		try {
			iterationPW.println(repLocName + " occured once again at position " + position + ". Added backedge");
			iterationPW.println("from:   " + state);
			iterationPW.println("labeled with:   " + transition.getPrettyPrintedStatements());
			iterationPW.println("to:   " + succState);
			if (linPredStates != null) {
				iterationPW.println("for each linPredStates:   " + linPredStates);
			}
			if (result == 1729) {
				iterationPW.println("because ");
			}
			else {
				assert ( result == SMTInterface.SMT_UNSAT);
				iterationPW.println("because Iteration" + 
					iteration+"_SatProblem" + satProblem+" says:");
			}
			iterationPW.println("  " + sf1);
			iterationPW.println("implies");
			iterationPW.println("  " + sf2);
			iterationPW.println("");
		} finally {
			iterationPW.flush();
		}
	}
	
	
}
