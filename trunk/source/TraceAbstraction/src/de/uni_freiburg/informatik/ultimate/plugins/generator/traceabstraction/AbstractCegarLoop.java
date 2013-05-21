package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AtsDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.AtsDefinitionPrinter.Labeling;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.ILocation;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ParallelComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.TAPreferences.Artifact;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.TAPreferences.InterpolatedLocs;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.AnnotateAndAsserter;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceChecker;


/**
 * CEGAR loop of a trace abstraction. Can be used to check safety and 
 * termination of sequential and concurrent programs.
 * Defines roughly the structure of the CEGAR loop, concrete algorithms are
 * implemented in classes which extend this one.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public abstract class AbstractCegarLoop {
	
	protected final static Logger s_Logger = 
		UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	
	/**
	 * Result of CEGAR loop iteration <ul>
	 * <li> SAFE: there is no feasible trace to an error location
	 * <li> UNSAFE: there is a feasible trace to an error location 
	 * (the underlying program has at least one execution which violates its 
	 * specification)
	 * <li> UNKNOWN: we found a trace for which we could not decide feasibility
	 * or we found an infeasible trace but were not able to exclude it in 
	 * abstraction refinement.
	 * <li> TIMEOUT: 
	 */
	public enum Result { SAFE, UNSAFE, TIMEOUT , UNKNOWN }
	
	/**
	 * Unique m_Name of this CEGAR loop to distinguish this instance from other
	 * instances in a complex verification task.
	 * Important only for debugging and debugging output written to files.
	 */
	private final String m_Name;

	
	/**
	 * Node of a recursive control flow graph which stores additional 
	 * information about the 
	 */
	protected final RootNode m_RootNode;
	
	
	/**
	 * Intermediate layer to encapsulate communication with SMT solvers. 
	 */
	protected final SmtManager m_SmtManager;
	
	
	
	/**
	 * Intermediate layer to encapsulate preferences.
	 */
	protected final TAPreferences m_Pref;
	
	/**
	 * Set of error location whose reachability is analyzed by this CEGAR loop.
	 */
	protected final Collection<ProgramPoint> m_ErrorLocs;

	/**
	 * Current Iteration of this CEGAR loop.
	 */
	protected int m_Iteration = 0;
	
	
	/**
	 * Accepting run of the abstraction obtained in this iteration. 
	 */
	protected IRun<CodeBlock, IPredicate> m_Counterexample;
	
	
	/**
	 * Abstraction of this iteration. The language of m_Abstraction is a set
	 * of traces which is <ul>
	 * <li> a superset of the feasible program traces.
	 * <li> a subset of the traces which respect the control flow of of the
	 * program.
	 */
	protected IAutomaton<CodeBlock, IPredicate> m_Abstraction;
	
	
	/**
	 * TraceChecker of this iteration.
	 */
	protected TraceChecker m_TraceChecker;
	

	/**
	 * Interpolant automaton of this iteration.
	 */
	protected NestedWordAutomaton<CodeBlock, IPredicate> m_InterpolAutomaton;
	
	
	/**
	 * Failure path. Only computed in the last iteration of the CEGAR loop.
	 */
	protected List<CodeBlock> m_FailurePath;
	
	
	
	// used for the collection of statistics
	public int m_BiggestAbstractionIteration = 0;
	public int m_BiggestAbstractionSize = 0;
	public int m_InitialAbstractionSize = 0;
	public int m_NumberOfErrorLocations = 0;
	
	
	// used for debugging only
	protected IAutomaton<CodeBlock, IPredicate> m_ArtifactAutomaton;
	protected PrintWriter m_IterationPW;
	protected final Labeling m_PrintAutomataLabeling = Labeling.TOSTRING;

	public long m_DeadEndRemovalTime;
	public long m_MinimizationTime;
	public int m_StatesRemovedByMinimization;

	
	
	public AbstractCegarLoop(String name, RootNode rootNode,
			SmtManager smtManager,
			TAPreferences taPrefs,
			Collection<ProgramPoint> errorLocs) {
		this.m_Name = name;
		this.m_RootNode = rootNode;
		this.m_SmtManager = smtManager;
		this.m_Pref = taPrefs;
		this.m_ErrorLocs = errorLocs;
	}
	
	

	/**
	 * Construct the automaton m_Abstraction such that the language recognized
	 * by m_Abstation is a superset of the language of the program.
	 * The initial abstraction in our implementations will usually be an
	 * automaton that has the same graph as the program.
	 */
	protected abstract void getInitialAbstraction() throws OperationCanceledException;
	
	
	/**
	 * Return true iff the m_Abstraction does not accept any trace. 
	 * @throws OperationCanceledException 
	 */
	protected abstract boolean isAbstractionCorrect() throws OperationCanceledException;
	
	
	/**
	 * Determine if the trace of m_Counterexample is a feasible sequence of
	 * CodeBlocks. Return <ul>
	 * <li> SAT if the trace is feasible
	 * <li> UNSAT if the trace is infeasible
	 * <li> UNKNOWN if the algorithm was not able to determine the feasibility.
	 * </ul>    
	 */
	protected abstract LBool isCounterexampleFeasible();
	
	
	/**
	 * Construct an automaton m_InterpolantAutomaton which <ul>
	 * <li> accepts the trace of m_Counterexample,
	 * <li> accepts only infeasible traces.
	 * </ul>
	 */
	protected abstract void constructInterpolantAutomaton();
	
	
	/**
	 * Construct a new automaton m_Abstraction such that <ul> 
	 * <li> the language of the new m_Abstraction is (not necessary strictly)
	 * smaller than the language of the old m_Abstraction
	 * <li> the new m_Abstraction accepts all feasible traces of the old 
	 * m_Abstraction  (only infeasible traces are removed)
	 * <ul>
	 * @return true iff the trace of m_Counterexample (which was accepted by the
	 * old m_Abstraction) is not accepted by the m_Abstraction.
	 */
	protected abstract boolean refineAbstraction() throws OperationCanceledException;
	
	
	/**
	 * Add Hoare annotation to the control flow graph. Use the information 
	 * computed so far annotate the ProgramPoints of the control flow graph
	 * with invariants.
	 */
	protected abstract void computeCFGHoareAnnotation();
	
	
	
	/**
	 * Return the Artifact whose computation was requested. This artifact
	 * can be either the control flow graph, an abstraction, an interpolant
	 * automaton, or a negated interpolant automaton. The artifact is only used
	 * for debugging.
	 * @return The root node of the artifact after it was transformed to an
	 * ULTIMATE model.
	 */
	public abstract IElement getArtifact();


	
	public int getIteration() {
		return m_Iteration;
	}
	
	public List<CodeBlock> getFailurePath() {
		return m_FailurePath;
	}
	
	public SmtManager getSmtManager() {
		return m_SmtManager;
	}
	
	public String errorLocs() {
		return m_ErrorLocs.toString();
	}
	
	
	
	public final Result iterate() {
		s_Logger.info("Interprodecural is " + m_Pref.interprocedural());		
		s_Logger.info("Solver is " + m_Pref.solver());
		s_Logger.info("Hoare is " + m_Pref.computeHoareAnnotation());
		s_Logger.info("Compute interpolants for " + m_Pref.interpolatedLocs());
		s_Logger.info("Backedges2True is " + m_Pref.edges2True());
		s_Logger.info("Backedges is " + m_Pref.interpolantAutomaton());
		s_Logger.info("Determinization is " + m_Pref.determinization());
		s_Logger.info("Difference is " + m_Pref.differenceSenwa());
		s_Logger.info("Minimize is " + m_Pref.minimize());

		
		m_Iteration = 0;
		s_Logger.info("======== Iteration " + m_Iteration + "==of CEGAR loop == " + m_Name + "========");
		
		// intialize dump of debugging output to files if necessary
		if (m_Pref.dumpFormulas() || m_Pref.dumpAutomata()) {
			dumpInitinalize();
		}
		try {
			getInitialAbstraction();
		} catch (OperationCanceledException e1) {
			s_Logger.warn("Verification cancelled");
			return Result.TIMEOUT;
		}
		
		
		if (m_Iteration <= m_Pref.watchIteration() && 
				(m_Pref.artifact() == Artifact.ABSTRACTION || m_Pref.artifact() == Artifact.RCFG)) {
			m_ArtifactAutomaton = m_Abstraction;
		}
		if (m_Pref.dumpAutomata()) {
			new AtsDefinitionPrinter<String,String>(m_Pref.dumpPath()+"/"+m_Name+"_Abstraction"+m_Iteration,
					m_PrintAutomataLabeling,"",m_Abstraction);
		}
		m_InitialAbstractionSize = m_Abstraction.size();
		m_BiggestAbstractionSize = m_Abstraction.size();
		m_NumberOfErrorLocations = m_ErrorLocs.size();
		
		
		
		boolean initalAbstractionCorrect;
		try {
			initalAbstractionCorrect = isAbstractionCorrect();
		} catch (OperationCanceledException e1) {
			s_Logger.warn("Verification cancelled");
			return Result.TIMEOUT;
		}
		if (initalAbstractionCorrect) {
			return Result.SAFE;
		}
		
		
		
		for (m_Iteration=1; m_Iteration<=m_Pref.maxIterations(); m_Iteration++){
			s_Logger.info("====== " + errorLocs() + "== Iteration " + m_Iteration + "============");
			m_SmtManager.setIteration(m_Iteration);
			if (m_Pref.dumpFormulas() || m_Pref.dumpAutomata()) {
				dumpInitinalize();
			}

			
			
			LBool isCounterexampleFeasible = isCounterexampleFeasible();
			if (isCounterexampleFeasible == Script.LBool.SAT) {
				return Result.UNSAFE;
			}
			if (isCounterexampleFeasible == Script.LBool.UNKNOWN) {
				return Result.UNKNOWN;
			}
			

			
			
			constructInterpolantAutomaton();
			
			s_Logger.info("Interpolant Automaton has "+m_InterpolAutomaton.getStates().size() +" states");
			
			if (m_Iteration <= m_Pref.watchIteration() && m_Pref.artifact() == Artifact.INTERPOLANT_AUTOMATON) {
				m_ArtifactAutomaton = m_InterpolAutomaton;
			}
			if (m_Pref.dumpAutomata()) {
				writeAutomatonToFile(m_InterpolAutomaton, "InterpolantAutomaton_Iteration"+m_Iteration);
			}
			
			
			
			
			try {
				boolean progress = refineAbstraction();
				if (!progress) {
					s_Logger.warn("No progress! Counterexample is still accepted by refined abstraction.");
					assert (m_Pref.interpolatedLocs() == InterpolatedLocs.GUESS) :
							"Craig interpolation && no progress   ==>   bug!";
					m_FailurePath = AnnotateAndAsserter.constructFailureTrace(m_Counterexample.getWord(), null);
					return Result.UNKNOWN;
				}
			} catch (OperationCanceledException e) {
				s_Logger.warn("Verification cancelled");
				return Result.TIMEOUT;
			}
			
			s_Logger.info("Abstraction has " + m_Abstraction.sizeInformation());
			s_Logger.info("Interpolant automaton has " + m_InterpolAutomaton.sizeInformation());
			

			if (m_Pref.computeHoareAnnotation()) {
				assert (m_SmtManager.checkInductivity(m_Abstraction, false, true));
			}

			if (m_Iteration <= m_Pref.watchIteration() && m_Pref.artifact() == Artifact.ABSTRACTION) {
				m_ArtifactAutomaton = m_Abstraction;
			}
			
			if (m_Pref.dumpAutomata()) {
				writeAutomatonToFile(m_Abstraction, "Abstraction_Iteration"+m_Iteration);
				String filename = m_Pref.dumpPath()+"/Abstraction"+m_Iteration;
				new AtsDefinitionPrinter<String,String>(filename,m_PrintAutomataLabeling,"",m_Abstraction);
			}
			
			if (m_BiggestAbstractionSize < m_Abstraction.size()){
				m_BiggestAbstractionSize = m_Abstraction.size();
				m_BiggestAbstractionIteration = m_Iteration;
			}
			
			
			
			
			
			boolean isAbstractionCorrect;
			try {
				isAbstractionCorrect = isAbstractionCorrect();
			} catch (OperationCanceledException e) {
				s_Logger.warn("Verification cancelled");
				return Result.TIMEOUT;
			}
			if (isAbstractionCorrect) {
				return Result.SAFE;
			}
		}
		return Result.TIMEOUT;
	}
	



	
	
	
	private void writeAutomatonToFile(
			IAutomaton<CodeBlock, IPredicate> automaton, String filename) {
		new AtsDefinitionPrinter<String,String>(m_Pref.dumpPath()+"/"+filename, m_PrintAutomataLabeling,
													"",automaton);
	}
	
	
	
	
	
	


	
	
	
	
	
	
	
	private void dumpInitinalize() {
		File file = 
			new File(m_Pref.dumpPath() + "/" + m_Name + "_iteration" + m_Iteration + ".txt");
		FileWriter fileWriter;
		try {
			fileWriter = new FileWriter(file);
			m_IterationPW = new PrintWriter(fileWriter);
		} catch (IOException e) {
			e.printStackTrace();
		} 
	}

	/*
	 * TODO unify sequential and concurrent
	 */
	protected static void dumpNestedRun(IRun<CodeBlock,IPredicate> run,
			PrintWriter pW) {
		NestedWord<CodeBlock> counterexample = NestedWord.nestedWord(run.getWord());
		ArrayList<IPredicate> stateSequence = null;
		if (run instanceof NestedRun) {
			stateSequence = ((NestedRun) run).getStateSequence();
		}
		String line;
		int indentation = 0;
		try {
			line = "===============Run of potential Counterexample==========";
			pW.println(line);
			for (int i=0; i<counterexample.length(); i++) {

				if (run instanceof NestedRun) { 
					line = addIndentation(indentation,
							"Location"+i+": " +
							((ISLPredicate) stateSequence.get(i)).getProgramPoint());
					s_Logger.debug(line);
					pW.println(line);
				}
				
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
	
	
	
	private void dumpSsa(Term[] ssa) {
		FormulaUnLet unflet = new FormulaUnLet();
		try {
			m_IterationPW.println(
					"===============SSA of potential Counterexample==========");
			for (int i=0; i<ssa.length; i++) {
				m_IterationPW.println(
						"UnFletedTerm" + i + ": " +	unflet.unlet(ssa[i]));
			}
			m_IterationPW.println("");
			m_IterationPW.println("");
		} finally {
			m_IterationPW.flush();
		}
	}

	
	private void dumpStateFormulas(IPredicate[] interpolants) {
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
	
	

	

	
	
	



	public static String addIndentation(int indentation, String s) {
		StringBuilder sb = new StringBuilder("");
		for (int i=0; i<indentation; i++) {
			sb.append("    ");
		}
		sb.append(s);
		return sb.toString();
	}

	

	
	static void dumpBackedges(ProgramPoint repLocName, int position,
			IPredicate state,
			Collection<IPredicate> linPredStates,
			CodeBlock transition,
			IPredicate succState,
			IPredicate sf1,IPredicate sf2,
			LBool result,
			int iteration, int satProblem, PrintWriter iterationPW) {
		try {
			iterationPW.println(repLocName + " occured once again at position " + position + ". Added backedge");
			iterationPW.println("from:   " + state);
			iterationPW.println("labeled with:   " + transition.getPrettyPrintedStatements());
			iterationPW.println("to:   " + succState);
			if (linPredStates != null) {
				iterationPW.println("for each linPredStates:   " + linPredStates);
			}
			if (satProblem == -1) {
				iterationPW.println("because ");
			}
			else {
				assert ( result == Script.LBool.UNSAT);
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
	
	
	
	public static List<ILocation> trace2path(List<CodeBlock> word) {
		List<ILocation> failurePath = new ArrayList<ILocation>();
		for (int i=0; i<word.size(); i++) {
			CodeBlock codeBlock = word.get(i);
			addToFailurePath(codeBlock, i , failurePath);
		}
		return failurePath;
	}
	
	/**
	 * Recursive method used by getFailurePath
	 */
	private static void addToFailurePath(CodeBlock codeBlock, int pos, 
												List<ILocation> failurePath) {
		if (codeBlock instanceof Call) {
			Statement st = ((Call) codeBlock).getCallStatement();
			failurePath.add(st.getLocation());
		} else if (codeBlock instanceof Return) {
			Statement st = ((Return) codeBlock).getCallStatement();
			failurePath.add(st.getLocation());
		} else if (codeBlock instanceof Summary) {
			Statement st = ((Summary) codeBlock).getCallStatement();
			failurePath.add(st.getLocation());
		} else if (codeBlock instanceof StatementSequence) {
			List<Statement> stmtsOfTrans = ((StatementSequence) codeBlock).getStatements();
			for (Statement st : stmtsOfTrans) {
				failurePath.add(st.getLocation());
			}
		} else if (codeBlock instanceof SequentialComposition) {
			SequentialComposition seqComp = (SequentialComposition) codeBlock;
			for (CodeBlock cb : seqComp.getCodeBlocks()) {
				addToFailurePath(cb, pos, failurePath);
			}
		} else if (codeBlock instanceof ParallelComposition) {
			throw new UnsupportedOperationException();
		} else {
			throw new IllegalArgumentException("unkown code block");
		}
	}
	
	
}
