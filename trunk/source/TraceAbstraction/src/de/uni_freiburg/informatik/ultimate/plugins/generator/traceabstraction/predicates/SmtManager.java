package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.ReasonUnknown;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.ComputeFreeVariables;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.logic.simplification.SimplifyDDA;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Smt2Boogie;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.InterproceduralSequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.TransFormula;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.TransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.PreferenceValues.Solver;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.DestructiveEqualityResolution;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.HoareAnnotation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager.TermVarsProc;
import de.uni_freiburg.informatik.ultimate.util.ScopedHashMap;

public class SmtManager {
	
	private static Logger s_Logger = 
		UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	
	enum Status { IDLE, TRACECHECK, CODEBLOCKCHECK1, 
		CODEBLOCKCHECK2, EDGECHECK };
	
	Status m_Status = Status.IDLE; 
	
	final Smt2Boogie m_Smt2Boogie;
	private final Script m_Script;
	private final Map<String,ASTType> m_GlobalVars;
	private final ModifiableGlobalVariableManager m_ModifiableGlobals;
	private final boolean m_DumpFormulaToFile;
	private final String m_DumpPath;
	private int m_Iteration;
	private int m_satProbNumber;
	
	private ScopedHashMap<String, Term> m_IndexedConstants;
	Set<BoogieVar> m_AssignedVars;

	private int m_TrivialSatQueries = 0;
	private int m_NontrivialSatQueries = 0;

	private int m_TrivialCoverQueries = 0;
	private int m_NontrivialCoverQueries = 0;
	
	int m_LazyEdgeCheckQueries = 0;
	int m_TrivialEdgeCheckQueries = 0;
	int m_NontrivialEdgeCheckQueries = 0;
	
	private int m_VarSetMinimalSolverQueries = 0;
	private long m_VarSetMinimalComputationTime = 0;
	
	long m_SatCheckTime = 0;
	private long m_SatCheckSolverTime = 0;
	private long m_TraceCheckTime = 0;
	private long m_InterpolQuriesTime = 0;
	private int m_InterpolQueries = 0;

	private int m_FreshVariableCouter = 0;
	
	
	protected int m_SerialNumber;

	private long m_TraceCheckStartTime = Long.MIN_VALUE;



	
	
	protected static Term m_DontCareTerm;
	protected static Term m_EmptyStackTerm;
	protected static String[] m_NoProcedure = new String[0];
	protected static Set<BoogieVar> m_EmptyVars = new HashSet<BoogieVar>(0);
	
	public SmtManager(Smt2Boogie smt2Boogie,
					Solver solver, 
					Map<String,ASTType> globalVars,
					ModifiableGlobalVariableManager modifiableGlobals, 
					boolean dumpFormulaToFile,
					String dumpPath) {
		m_DontCareTerm = new AuxilliaryTerm("don't care");
		m_EmptyStackTerm = new AuxilliaryTerm("emptyStack");
		m_Smt2Boogie = smt2Boogie;
		m_Script = m_Smt2Boogie.getScript();
		m_GlobalVars = globalVars;
		m_ModifiableGlobals =  modifiableGlobals;
		m_DumpFormulaToFile = dumpFormulaToFile;
		m_DumpPath = dumpPath;
	}
	
	public boolean isIdle() {
		return m_Status == Status.IDLE;
	}
	
	
	public Smt2Boogie getBoogieVar2SmtVar() {
		return m_Smt2Boogie;
	}


	public Script getScript() {
		return m_Script;
	}
	
	private Term False() {
		return m_Script.term("false");
	}
	
	private Term True() {
		return m_Script.term("true");
	}
	
	public static Term getDontCareTerm() {
		return m_DontCareTerm;
	}
	

	public Map<String, ASTType> getGlobalVars() {
		return m_GlobalVars;
	}

	public int getNontrivialSatQueries() {
		return m_NontrivialSatQueries;
	}
	
	public int getTrivialSatQueries() {
		return m_TrivialSatQueries;
	}
	
	public long getSatCheckSolverTime() {
		return m_SatCheckSolverTime;
	}
	
	public long getInterpolQuriesTime() {
		return m_InterpolQuriesTime;
	}

	public int getInterpolQueries() {
		return m_InterpolQueries;
	}
	
	public long getTraceCheckTime() {
		return m_TraceCheckTime;
	}
	
	public long getSatCheckTime() {
		return m_SatCheckTime;
	}
	
	public int getTrivialEdgeCheckQueries() {
		return m_TrivialEdgeCheckQueries;
	}
	
	public int getLazyEdgeCheckQueries() {
		return m_LazyEdgeCheckQueries;
	}

	public int getNontrivialEdgeCheckQueries() {
		return m_NontrivialEdgeCheckQueries;
	}
	
	public int getTrivialCoverQueries() {
		return m_TrivialCoverQueries;
	}

	public int getNontrivialCoverQueries() {
		return m_NontrivialCoverQueries;
	}

	
	public int getVarSetMinimalSolverQueries() {
		return m_VarSetMinimalSolverQueries;
	}

	public long getVarSetMinimalComputationTime() {
		return m_VarSetMinimalComputationTime;
	}

	public void setIteration(int iteration) {
		m_Iteration = iteration;
		m_satProbNumber = 0;
	}
	
		
	public int getSatProbNumber() {
		return m_satProbNumber;
	}
	
	
	
	/**
	 * Return a similar BoogieVar that is not an oldvar. Requires that this is
	 * an oldvar.
	 */
	public BoogieVar getNonOldVar(BoogieVar bv) {
		if (!bv.isOldvar()) {
			throw new AssertionError("Not an oldvar" + this);
		}
		BoogieVar result = m_Smt2Boogie.getGlobals().get(bv.getIdentifier());
		assert result != null;
		return result;
	}

	
	/**
	 * Return a similar BoogieVar that is an oldvar. Requires that this not
	 * an oldvar.
	 */
	public BoogieVar getOldVar(BoogieVar bv) {
		assert bv.isGlobal();
		if (bv.isOldvar()) {
			throw new AssertionError("Already an oldvar: " + this);
		}
		BoogieVar result = m_Smt2Boogie.getOldGlobals().get(bv.getIdentifier());
		assert result != null;
		return result;
	}
	

	/**
	 * For each oldVar in vars that is not modifiable by procedure proc:
	 * substitute the oldVar by the corresponding globalVar in term and
	 * remove the oldvar from vars.
	 */
	public Term substituteOldVarsOfNonModifiableGlobals(String proc, Set<BoogieVar> vars,  Term term) {
		final Set<BoogieVar> oldVarsOfmodifiableGlobals = 
				m_ModifiableGlobals.getOldVarsAssignment(proc).getAssignedVars();
		List<BoogieVar> replacedOldVars = new ArrayList<BoogieVar>();
		
		ArrayList<TermVariable> replacees = new ArrayList<TermVariable>();
		ArrayList<Term> replacers = new ArrayList<Term>();
		
		for (BoogieVar bv : vars) {
			if (bv.isOldvar()) {
				if (!oldVarsOfmodifiableGlobals.contains(bv)) {
					replacees.add(bv.getTermVariable());
					replacers.add(getNonOldVar(bv).getTermVariable());
					replacedOldVars.add(bv);
				}
			}
		}
		
		TermVariable[] substVars = replacees.toArray(new TermVariable[replacees.size()]);
		Term[] substValues = replacers.toArray(new Term[replacers.size()]);
		Term result = m_Script.let( substVars , substValues, term);
		result = (new FormulaUnLet()).unlet(result);
		
		for (BoogieVar bv  : replacedOldVars) {
			vars.remove(bv);
			vars.add(getNonOldVar(bv));
		}
		return result;
	}
	


	

	
	

	
	
//	private boolean varSetIsMinimal(Set<BoogieVar> boogieVars, 
//											Term formula, Term closedFormula) {
//		assert isIdle();
//		long startTime = System.nanoTime();
//		m_Script.push(1);
//		Term negated = m_Script.term("not", closedFormula);
//		assertTerm(negated);
//		for (BoogieVar bv : boogieVars) {
//			TermVariable[] vars = new TermVariable[1];
//			vars[0] = bv.getTermVariable();
//			Term[] values = new Term[1];
//			values[0] = bv.getPrimedConstant();
//			formula = m_Script.let(vars, values, formula);
//			formula = renameVarsToDefaultConstants(boogieVars, formula);
//		
//			m_Script.push(1);
//			assertTerm(formula);
//			LBool sat = m_Script.checkSat();
//			m_VarSetMinimalSolverQueries++;
//			if (sat == LBool.UNSAT) {
//				// variable was not necessary
//				m_Script.pop(2);
//				m_VarSetMinimalComputationTime += (System.nanoTime() - startTime);
//				return false;
//			} else if (sat == LBool.SAT) {
//				m_Script.pop(1);
//			} else if (sat == LBool.UNKNOWN) {
//				throw new AssertionError("if this case occurs, ask Matthias");
//			} else {
//				throw new AssertionError();
//			}
//		}
//		m_VarSetMinimalComputationTime += (System.nanoTime() - startTime);
//		m_Script.pop(1);
//		return true;
//	}
	
	
	
	
	
	
	
	public void startTraceCheck() {
		if (m_Status != Status.IDLE) {
			throw new AssertionError("SmtManager is busy");
		} else {
			assert m_TraceCheckStartTime == Long.MIN_VALUE;
			m_TraceCheckStartTime = System.nanoTime();
			m_Status = Status.TRACECHECK;
			m_IndexedConstants = new ScopedHashMap<String, Term>();
			m_Script.push(1);
		}
	}
	
	public void endTraceCheck() {
		if (m_Status != Status.TRACECHECK) {
			throw new AssertionError("SmtManager is not performing a traceCheck");
		} else {
			m_TraceCheckTime += (System.nanoTime() - m_TraceCheckStartTime);
			m_TraceCheckStartTime = Long.MIN_VALUE;
			m_Status = Status.IDLE;
			m_IndexedConstants = null;
			m_Script.pop(1);
		}
	}
	
	
	
	
	
//	public void push() {
//		if (m_IndexedConstants != null) {
//			throw new AssertionError("During Trace Abstration only one additional level on stack allowed");
//		}
//		else {
//			m_IndexedConstants = new HashMap<String, Term>();
//			m_Script.push(1);
//		}
//	}
//	public void pop() {
//		if (m_IndexedConstants == null) {
//			throw new AssertionError("Smt Manager has not pushed before");
//		}
//		else {
//			m_IndexedConstants = null;
//			m_Script.pop(1);
//		}
//	}
	
	LBool checkSatisfiable(Term f) {
        long startTime = System.nanoTime();
        LBool result = null;
        try {
        	assertTerm(f);
        } catch (SMTLIBException e) {
			if (e.getMessage().equals("Unsupported non-linear arithmetic")) {
				return LBool.UNKNOWN;
			}
			else {
				throw e;
			}
        }
        result = m_Script.checkSat();
		m_SatCheckSolverTime += (System.nanoTime() - startTime);
		m_NontrivialSatQueries++;
		if (result == LBool.UNKNOWN) {
			Object info = m_Script.getInfo(":reason-unknown");
			if (!(info instanceof ReasonUnknown)) {
				m_Script.getInfo(":reason-unknown");
			}
			ReasonUnknown reason = (ReasonUnknown) info;
			Object test = m_Script.getInfo(":reason-unknown");
			switch (reason) {
			case CRASHED:
				throw new AssertionError("Solver crashed");
			case MEMOUT:
				throw new AssertionError("Solver out of memory, " +
						"solver might be in inconsistent state");
			default:
				break;
			}
		} 
		return result;
	}
	
	public LBool assertTerm(Term term) {
        long startTime = System.nanoTime();
        LBool result = null;
        result = m_Script.assertTerm(term);
        m_SatCheckSolverTime += (System.nanoTime() - startTime);
        return result;
	}
	
	
	public Term[] computeInterpolants(Term[] interpolInput, int[] startOfSubtree) {
		long startTime = System.nanoTime();
		Term[] result = m_Script.getInterpolants(interpolInput, startOfSubtree);
		m_InterpolQuriesTime += (System.nanoTime() - startTime);
		m_InterpolQueries++;
		return result;
	}
	
	public Term[] computeInterpolants(Term[] interpolInput) {
		long startTime = System.nanoTime();
		Term[] result = m_Script.getInterpolants(interpolInput);
		m_InterpolQuriesTime += (System.nanoTime() - startTime);
		m_InterpolQueries++;
		return result;
	}

	
	public TermVarsProc and(IPredicate... preds) {
		Set<BoogieVar> vars = new HashSet<BoogieVar>();
		Set<String> procs = new HashSet<String>();
		Term term = m_Script.term("true");
		for (IPredicate p : preds) {
			if (isDontCare(p)) {
				return new TermVarsProc(m_DontCareTerm, m_EmptyVars, m_NoProcedure, m_DontCareTerm);
			}
			vars.addAll(p.getVars());
			procs.addAll(Arrays.asList(p.getProcedures()));
			term = Util.and(m_Script, term, p.getFormula());
		}
//		Term isImplied = Util.and(m_Script,sf1.getFormula(), Util.not(m_Script,sf2.getFormula()));
//		if (Util.checkSat(m_Script, isImplied) == LBool.UNSAT) {
//			resultFormula = sf1.getFormula();
//			return new Predicate(m_Script, sf1.getProgramPoint(),resultFormula,vars);
//		}
//		Term implies = Util.and(m_Script,Util.not(m_Script,sf1.getFormula()), sf2.getFormula());
//		if (Util.checkSat(m_Script, implies) == LBool.UNSAT) {
//			resultFormula = sf2.getFormula();
//			return new Predicate(m_Script, sf1.getProgramPoint(),resultFormula,vars);
//		}
//		resultFormula = Util.and(m_Script,sf1.getFormula(), sf2.getFormula());
//		formula = new SimplifyDDA(m_Script, s_Logger).getSimplifiedTerm(formula);
		Term closedTerm = SmtManager.computeClosedFormula(term, vars, m_Script);
		return new TermVarsProc(term, vars, procs.toArray(new String[0]), closedTerm);
	}
	
	
	
	public TermVarsProc or(IPredicate... preds) {
		Set<BoogieVar> vars = new HashSet<BoogieVar>();
		Set<String> procs = new HashSet<String>();
		Term term = m_Script.term("false");
		for (IPredicate p : preds) {
			if (isDontCare(p)) {
				return new TermVarsProc(m_DontCareTerm, m_EmptyVars, m_NoProcedure, m_DontCareTerm);
			}
			vars.addAll(p.getVars());
			procs.addAll(Arrays.asList(p.getProcedures()));
			term = Util.or(m_Script, term, p.getFormula());
		}
		Term closedTerm = SmtManager.computeClosedFormula(term, vars, m_Script);
		return new TermVarsProc(term, vars, procs.toArray(new String[0]), closedTerm);
	}


	
	public TermVarsProc not(IPredicate p) {
		if (isDontCare(p)) {
			return new TermVarsProc(m_DontCareTerm, m_EmptyVars, m_NoProcedure, m_DontCareTerm);
		}
		Term term = Util.not(m_Script,p.getFormula());
		Term closedTerm = Util.not(m_Script,p.getClosedFormula());
		return new TermVarsProc(term, p.getVars(), p.getProcedures(), closedTerm);
	}
	
	
	
	public Term simplify(Term term) {
		return new SimplifyDDA(m_Script, s_Logger).getSimplifiedTerm(term);
	}
	
//	public Predicate simplify(Predicate ps) {
//		return m_PredicateFactory.newPredicate(ps.getProgramPoint(), simplify(ps.getFormula()),ps.getVars());
//	}


	/**
	 * Check if ps1 is a subset of ps2.
	 * @param ps1 set of states represented as Predicate
	 * @param ps2 set of states resresented as Predicate
	 * @return SMT_UNSAT if the inclusion holds, 1729 if the inclusion trivially
	 * holds, SMT_SAT if the inclusion does not hold and SMT_UNKNOWN if the
     * theorem prover was not able to give an answer.

	 */
	public LBool isCovered(IPredicate ps1, IPredicate ps2) {
		long startTime = System.nanoTime();
		 
		if (isDontCare(ps1) || isDontCare(ps2)) {
			m_TrivialCoverQueries++;
			return Script.LBool.UNKNOWN;
		}		
		
		Term formula1 = ps1.getFormula();
		Term formula2 = ps2.getFormula();
		LBool result = null;
		// tivial case
		if (formula1 == False() || formula2 == True()) {
			m_TrivialCoverQueries++;
			result = Script.LBool.UNSAT;
		}
		else {
			m_Script.push(1);
			m_IndexedConstants = new ScopedHashMap<String, Term>();
			Term negImpl = Util.and(m_Script,formula1, Util.not(m_Script,formula2));

			if (m_DumpFormulaToFile) {
				dumpSatProblem(negImpl, m_Iteration, m_satProbNumber, m_DumpPath, m_Script);
				m_satProbNumber++;
			}

			//replace all vars by constants
			{
				TermVariable[] vars = new TermVariable[ps1.getVars().size()];
				Term[] values = new Term[vars.length];
				int i=0;
				for (BoogieVar var : ps1.getVars()) {
					vars[i] = var.getTermVariable();
					values[i] = getConstant(var);
					i++;
				}
				negImpl = m_Script.let(vars, values, negImpl);
			}
			
			{
				TermVariable[] vars = new TermVariable[ps2.getVars().size()];
				Term[] values = new Term[vars.length];
				int i=0;
				for (BoogieVar var : ps2.getVars()) {
					vars[i] = var.getTermVariable();
					values[i] = getConstant(var);
					i++;
				}
				negImpl = m_Script.let(vars, values, negImpl);
			}
			
			m_NontrivialCoverQueries++;
			result = this.checkSatisfiable(negImpl);
			m_IndexedConstants = null;
			m_Script.pop(1);
		}
		m_SatCheckTime += (System.nanoTime() - startTime);
		return result;
	}
	
	
	public LBool isCovered(Term formula1, Term formula2) {
		assert (m_Status == Status.IDLE);
		long startTime = System.nanoTime();
		 
		LBool result = null;
		// tivial case
		if (formula1 == False() || formula2 == True()) {
			m_TrivialCoverQueries++;
			result = Script.LBool.UNSAT;
		}
		else {
			m_Script.push(1);
			assertTerm(formula1);
			Term negFormula2 = m_Script.term("not", formula2);
			assertTerm(negFormula2);
			result = m_Script.checkSat();
			m_NontrivialCoverQueries++;
			m_Script.pop(1);
		}
		m_SatCheckTime += (System.nanoTime() - startTime);
		return result;
	}
	
	
	
	
	public LBool isInductive(IPredicate ps1, CodeBlock ta, IPredicate ps2) {
		return isInductive(ps1, ta, ps2, false);
	}
	
	//TODO less renaming possible e.g. keep var names in ps1
	/**
	 * Check if post(sf1,tf) is a subset of sf2.
	 * @param ps1 a set of states represented by a Predicate
	 * @param tf a transition relation represented by a TransFormula
	 * @param ps2 a set of states represented by a Predicate
	 * @return The result of a theorem prover query, where SMT_UNSAT means yes
	 * to our question, SMT_SAT means no to our question and SMT_UNKNOWN means
	 * that the theorem prover was not able give an answer to our question. 
	 */
	public LBool isInductive(IPredicate ps1, CodeBlock ta, IPredicate ps2, boolean expectUnsat) {
		long startTime = System.nanoTime();

		if (isDontCare(ps1) || isDontCare(ps2)) {
			m_TrivialSatQueries++;
			return Script.LBool.UNKNOWN;
		}
		
		if (ps1.getFormula() == False() || ps2.getFormula() == True()) {
			m_TrivialSatQueries++;
			return Script.LBool.UNSAT;
		}
		
		
//		if (simpleSelfloopCheck(ps1, ta, ps2)) {
//			m_TrivialSatQueries = m_TrivialSatQueries + 10000000;
//			return Script.LBool.UNSAT;
//		}
		
		m_Script.push(1);
		m_IndexedConstants = new ScopedHashMap<String, Term>();
		//OldVars not renamed
		//All variables get index 0 
		Term ps1renamed = formulaWithIndexedVars(ps1,new HashSet<BoogieVar>(0),
				4, 0, Integer.MIN_VALUE,null,-5,0);
		
		TransFormula tf = ta.getTransitionFormula();
		Set<BoogieVar> assignedVars = new HashSet<BoogieVar>();
		Term fTrans = formulaWithIndexedVars(tf, 0, 1, assignedVars);

		//OldVars not renamed
		//All variables get index 0 
		//assigned vars (locals and globals) get index 1
		//other vars get index 0
		Term ps2renamed = formulaWithIndexedVars(ps2, assignedVars,
				1, 0, Integer.MIN_VALUE,assignedVars,1,0);
		
		
		//We want to return true if (fState1 && fTrans)-> fState2 is valid
		//This is the case if (fState1 && fTrans && !fState2) is unsatisfiable
		Term f = Util.not(m_Script,ps2renamed);
		f = Util.and(m_Script,fTrans,f);
		f = Util.and(m_Script,ps1renamed, f);
		
//		f = new FormulaUnLet().unlet(f);
		if (m_DumpFormulaToFile) {
			dumpSatProblem(f,m_Iteration,m_satProbNumber,m_DumpPath,m_Script);
			m_satProbNumber++;
		}
		LBool result = this.checkSatisfiable(f);
		if (expectUnsat) {
			if (result == LBool.SAT) {
				s_Logger.error("From " + ps1.getFormula().toStringDirect());
				s_Logger.error("Statements " + ta.getPrettyPrintedStatements());
				s_Logger.error("To " +ps2.getFormula().toStringDirect());
				s_Logger.error("Not inductive!");
				
			}
			assert (result == Script.LBool.UNSAT || result == Script.LBool.UNKNOWN)
				: "internal statement not inductive";
		}
		m_IndexedConstants = null;
		m_Script.pop(1);
		m_SatCheckTime += (System.nanoTime() - startTime);
		testMyInternalDataflowCheck(ps1, ta, ps2, result);
		return result;
	}
	

	
	
//	public LBool startEdgeCheckStep1(Predicate p) {
//		if (m_Status != Status.IDLE) {
//			throw new AssertionError("SmtManager is busy");
//		} 
//		
//		if (p.isUnknown()) {
//			m_TrivialSatQueries++;
//			return Script.LBool.UNKNOWN;
//		}
//		
//		if (p.getFormula() == False()) {
//			m_TrivialSatQueries++;
//			return Script.LBool.UNSAT;
//		}
//		
//		
//		long startTime = System.nanoTime();
//		m_Script.push(1);
//		m_IndexedConstants = new ScopedHashMap<String, Term>();
//		m_Status = Status.CODEBLOCKCHECK1;
//		
//		//OldVars not renamed
//		//All variables get index 0 
//		Term ps1renamed = formulaWithIndexedVars(p, new HashSet<BoogieVar>(0),
//				4, 0, Integer.MIN_VALUE,null,-5,0);
//		LBool quickCheck = assertTerm(ps1renamed);
//		if (quickCheck == LBool.UNSAT) {
//			m_IndexedConstants = null;
//			m_Script.pop(1);
//			m_Status = Status.IDLE;
//			m_CodeBlockCheckTime += (System.nanoTime() - startTime);
//			return LBool.UNSAT;
//		}
//		else {
//			return null;
//		}
//	}
//	
//	public LBool startEdgeCheckStep2(CodeBlock cb) {
//		long startTime = System.nanoTime();
//		if (m_Status != Status.CODEBLOCKCHECK1) {
//			throw new AssertionError("SmtManager not prepared");
//		}
//		m_Status = Status.CODEBLOCKCHECK2;
//		TransFormula tf = cb.getTransitionFormula();
//		m_AssignedVars = new HashSet<BoogieVar>();
//		Term fTrans = formulaWithIndexedVars(tf, 0, 1, m_AssignedVars);
//		m_AssignedVars = Collections.unmodifiableSet(m_AssignedVars);
//		LBool quickCheck = assertTerm(fTrans);
////		if (quickCheck == LBool.UNSAT) {
////			m_IndexedConstants = null;
////			m_AssignedVars = null;
////			m_Script.pop(1);
////			status = Status.IDLE;
////			m_CodeBlockCheckTime += (System.nanoTime() - startTime);
////			return LBool.UNSAT;
////		}
////		else {
//		
//		m_CodeBlockCheckTime += (System.nanoTime() - startTime);
//		return null;
////		}		
//	}
//	
//	public LBool doEdgeCheckStep3(Predicate p) {
//		if (m_Status != Status.CODEBLOCKCHECK2) {
//			throw new AssertionError("SmtManager not prepared");
//		} 
//
//		if (p.isUnknown()) {
//			m_TrivialSatQueries++;
//			m_IndexedConstants = null;
//			m_Script.pop(1);
//			m_Status = Status.IDLE;
//			return Script.LBool.UNKNOWN;
//		}
//		
//		if (p.getFormula() == True()) {
//			m_TrivialSatQueries++;
//			m_TrivialSatQueries++;
//			m_IndexedConstants = null;
//			m_Script.pop(1);
//			m_Status = Status.IDLE;
//			return Script.LBool.UNSAT;
//		}
//		long startTime = System.nanoTime();
//		
//		//OldVars not renamed
//		//All variables get index 0 
//		//assigned vars (locals and globals) get index 1
//		//other vars get index 0
//		m_Script.push(1);
//		m_IndexedConstants.beginScope();
//		Term ps2renamed = formulaWithIndexedVars(p, m_AssignedVars,
//				1, 0, Integer.MIN_VALUE,m_AssignedVars,1,0);
//		LBool quickCheck = assertTerm(m_Script.term("not",ps2renamed));
//		LBool result;
//		if (quickCheck == LBool.UNSAT) {
//			result = quickCheck;
//		} else {
//			result = m_Script.checkSat();
//		}
//		m_Script.pop(1);
//		m_IndexedConstants.endScope();
//		m_Status = Status.CODEBLOCKCHECK2;
//		m_CodeBlockCheckTime += (System.nanoTime() - startTime);
//		return result;
//	}
//	
//	public void endEdgeCheck() {
//		if (m_Status != Status.CODEBLOCKCHECK2) {
//			throw new AssertionError("SmtManager not prepared");
//		} 
//		m_Script.pop(1);
//		m_IndexedConstants = null;
//		m_AssignedVars = null;
//		m_Status = Status.IDLE;
//	}
	

	
	
	
	public LBool isInductiveCall(IPredicate ps1, 
			Call ta, IPredicate ps2) {
		return isInductiveCall(ps1, ta, ps2, false);
	}

	public LBool isInductiveCall(IPredicate ps1, 
						Call ta, IPredicate ps2, boolean expectUnsat) {
		long startTime = System.nanoTime();
		 
		if (isDontCare(ps1) || isDontCare(ps2)) {
			m_TrivialSatQueries++;
			return Script.LBool.UNKNOWN;
		}
		
		if (ps1.getFormula() == False() || ps2.getFormula() == True()) {
			m_TrivialSatQueries++;
			return Script.LBool.UNSAT;
		}
		
		m_Script.push(1);
		m_IndexedConstants = new ScopedHashMap<String, Term>();
		// OldVars not renamed.
		// All variables get index 0.
		Term ps1renamed = formulaWithIndexedVars(ps1,new HashSet<BoogieVar>(0),
				4, 0, Integer.MIN_VALUE,null,-5, 0);
		
		TransFormula tf = ta.getTransitionFormula();
		Set<BoogieVar> assignedVars = new HashSet<BoogieVar>();
		Term fTrans = formulaWithIndexedVars(tf, 0, 1, assignedVars);

		// OldVars renamed to index 0
		// GlobalVars renamed to index 0
		// Other vars get index 1
		Term ps2renamed = formulaWithIndexedVars(ps2, new HashSet<BoogieVar>(0),
				4, 1, 0, null,23,0);
		
		
		//We want to return true if (fState1 && fTrans)-> fState2 is valid
		//This is the case if (fState1 && fTrans && !fState2) is unsatisfiable
		Term f = Util.not(m_Script,ps2renamed);
		f = Util.and(m_Script,fTrans,f);
		f = Util.and(m_Script,ps1renamed, f);
		
		if (m_DumpFormulaToFile) {
			dumpSatProblem(f,m_Iteration,m_satProbNumber,m_DumpPath,m_Script);
			m_satProbNumber++;
		}
		LBool result = this.checkSatisfiable(f);
		m_IndexedConstants = null;
		m_Script.pop(1);
		if (expectUnsat) {
			assert (result == Script.LBool.UNSAT || result == Script.LBool.UNKNOWN) 
				: "call statement not inductive";
		}
		m_SatCheckTime += (System.nanoTime() - startTime);
		testMyCallDataflowCheck(ps1, ta, ps2, result);
		return result;
	}
	
	
	public LBool isInductiveReturn(IPredicate ps1, 
			IPredicate psk, 
			Return ta, 
			IPredicate ps2) {
		return isInductiveReturn(ps1, psk, ta, ps2, false);
	}
	
	public LBool isInductiveReturn(IPredicate ps1, 
			IPredicate psk, 
			Return ta, 
			IPredicate ps2,
			boolean expectUnsat) {
		long startTime = System.nanoTime();
		
		if (isDontCare(ps1) || isDontCare(ps2) || isDontCare(psk)) {
			m_TrivialSatQueries++;
			return Script.LBool.UNKNOWN;
		}
		
		if (ps1.getFormula() == False() ||
				psk.getFormula() == False() ||
				ps2.getFormula() == True()) {
			m_TrivialSatQueries++;
			return Script.LBool.UNSAT;
		}
		
		
		m_Script.push(1);
		m_IndexedConstants = new ScopedHashMap<String, Term>();
		Call ca = ta.getCorrespondingCall();
		Set<BoogieVar> modifiableGlobals = m_ModifiableGlobals.
				getModifiedBoogieVars(ca.getCallStatement().getMethodName());
		
		TransFormula tfReturn = ta.getTransitionFormula();
		Set<BoogieVar> assignedVarsOnReturn = new HashSet<BoogieVar>();
		Term fReturn = formulaWithIndexedVars(tfReturn, 1, 2, assignedVarsOnReturn);
//		fReturn = (new FormulaUnLet()).unlet(fReturn);
		
		TransFormula tfCall = ca.getTransitionFormula();
		Set<BoogieVar> assignedVarsOnCall = new HashSet<BoogieVar>();
		Term fCall = formulaWithIndexedVars(tfCall, 0, 1, assignedVarsOnCall);
//		fCall = (new FormulaUnLet()).unlet(fCall);

		// oldVars not renamed
		// other variables get index 0
		Term pskrenamed = formulaWithIndexedVars(psk, new HashSet<BoogieVar>(0),
				23, 0, Integer.MIN_VALUE, null, 23, 0);

		
		// oldVars get index 0
		// modifiable globals get index 2
		// not modifiable globals get index 0
		// other variables get index 1
		Term ps1renamed = formulaWithIndexedVars(ps1, new HashSet<BoogieVar>(0),
				23, 1, 0, modifiableGlobals, 2, 0);
		
		// oldVars not renamed
		// modifiable globals get index 2
		// variables assigned on return get index 2
		// other variables get index 0
		Term ps2renamed = formulaWithIndexedVars(ps2, assignedVarsOnReturn,
				2, 0, Integer.MIN_VALUE, modifiableGlobals, 2, 0);
		
		
		//We want to return true if (fState1 && fTrans)-> fState2 is valid
		//This is the case if (fState1 && fTrans && !fState2) is unsatisfiable
		Term f = Util.not(m_Script,ps2renamed);
		f = Util.and(m_Script,fReturn,f);
		f = Util.and(m_Script,ps1renamed, f);
		f = Util.and(m_Script,fCall, f);
		f = Util.and(m_Script,pskrenamed, f);
		
		if (m_DumpFormulaToFile) {
			dumpSatProblem(f,m_Iteration,m_satProbNumber,m_DumpPath,m_Script);
			m_satProbNumber++;
		}
		LBool result = this.checkSatisfiable(f);
		m_Script.pop(1);
		m_IndexedConstants = null;
		if (expectUnsat) {
			if (result == LBool.SAT) {
				s_Logger.error("From " + ps1.getFormula().toStringDirect());
				s_Logger.error("Caller " + psk.getFormula().toStringDirect());
				s_Logger.error("Statements " + ta.getPrettyPrintedStatements());
				s_Logger.error("To " +ps2.getFormula().toStringDirect());
				s_Logger.error("Not inductive!");
			}
			assert (result == Script.LBool.UNSAT ||	result == Script.LBool.UNKNOWN)
				: "return statement not inductive";
		}
		m_SatCheckTime += (System.nanoTime() - startTime);
		
		testMyReturnDataflowCheck(ps1,psk,ta,ps2,result);
		return result;
	}
	



	/**
	 * Return formula of a program state where all variables are renamed 
	 * (substituted by a constant that has the new name) according to the
	 * following scheme:
	 * <ul>
	 * <li> Each variable v that is contained in varsWithSpecialIdx is 
	 *  renamed to v_specialIdx
	 * <li> Each variable v that is not contained in varsWithSpecialIdx is
	 *  renamed to v_defaultIdx
	 * <li> If oldVarIdx is Integer.MIN_VALUE, each oldVar v is renamed to
	 * v_OLD
	 * <li> If oldVarIdx is not Integer.MIN_VALUE, each oldVar v is renamed to
	 * v_oldVarIdx. This means v can get the same name as a non-oldVar!
	 * </ul> 

	 */
	private Term formulaWithIndexedVars(IPredicate ps, 
						Set<BoogieVar> varsWithSpecialIdx, int specialIdx,
						int defaultIdx,
						int oldVarIdx,
						Set<BoogieVar> globalsWithSpecialIdx, int globSpecialIdx,
						int globDefaultIdx) {
		Term psTerm = ps.getFormula();
		if (ps.getVars() == null) {
			return psTerm;
		}

		Map<TermVariable, Term> substitution = new HashMap<TermVariable, Term>();
		
		for (BoogieVar var : ps.getVars()) {
			Term cIndex;
			if (varsWithSpecialIdx.contains(var)) {
				 cIndex = getIndexedConstant(var,specialIdx);
			} else if (var.isOldvar()) {
				if (oldVarIdx == Integer.MIN_VALUE) {
					cIndex = getConstant(var);
				}
				else {
					cIndex = getIndexedConstant(this.getNonOldVar(var), oldVarIdx);
				}
			} else if (var.isGlobal()) {
				if	(globalsWithSpecialIdx != null && 
						globalsWithSpecialIdx.contains(var)) {
					cIndex = getIndexedConstant(var, globSpecialIdx);
				}
				else {
					cIndex = getIndexedConstant(var, globDefaultIdx);
				}
			} else {
				// var is local and not contained in specialIdx
				cIndex = getIndexedConstant(var, defaultIdx);
			}
			TermVariable c = var.getTermVariable();
			substitution.put(c, cIndex);
		}

		TermVariable[] vars = new TermVariable[substitution.size()];
		Term[] values = new Term[substitution.size()];
		int i = 0;
		for (TermVariable var : substitution.keySet()) {
			vars[i] = var;
			values[i] = substitution.get(var);
			i++;
		}
		Term result = m_Script.let(vars, values, psTerm);
		return result;
	}
	
	
	/**
	 * Return formula of a transition where all variables are renamed 
	 * (substituted by a constant that has the new name) according to the
	 * following scheme:
	 * <ul>
	 * <li> Each inVar v is renamed to v_idxInVar.
	 * <li> Each outVar v that does not occur as an inVar 
	 * (no update/assignment) is renamed to v_idxOutVar.
	 * <li> Each variable v that occurs neither as inVar nor outVar is renamed
	 * to v_23.
	 * <li> Each oldVar v is renamed to v_OLD.
	 * </ul> 

	 */
	private Term formulaWithIndexedVars(TransFormula tf,
			int idxInVar, int idxOutVar, Set<BoogieVar> assignedVars) {
		assert (assignedVars != null && assignedVars.isEmpty());
		Set<TermVariable> notYetSubst = new HashSet<TermVariable>();
		notYetSubst.addAll(Arrays.asList(tf.getFormula().getFreeVars()));
		Term fTrans = tf.getFormula();
		String t = fTrans.toString();
		for (BoogieVar inVar : tf.getInVars().keySet()) {
			TermVariable tv = tf.getInVars().get(inVar);
			Term cIndex;
			if (inVar.isOldvar()) {
				cIndex = getConstant(inVar);
			}
			else {
				cIndex = getIndexedConstant(inVar, idxInVar);
			}
			TermVariable[] vars = { tv }; 
			Term[] values = { cIndex };
			Term undamagedFTrans = fTrans;
			fTrans = m_Script.let(vars, values, fTrans);
			t = fTrans.toString();
			notYetSubst.remove(tv);
		}
		for (BoogieVar outVar : tf.getOutVars().keySet()) {
			TermVariable tv = tf.getOutVars().get(outVar);
			if (tf.getInVars().get(outVar) != tv) {
				assignedVars.add(outVar);
				Term cIndex;
				if (outVar.isOldvar()) {
					cIndex = getConstant(outVar);
				}
				else {
					cIndex = getIndexedConstant(outVar, idxOutVar);
				}
				TermVariable[] vars = { tv }; 
				Term[] values = { cIndex };
				fTrans = m_Script.let(vars, values, fTrans);
				t = fTrans.toString();
				notYetSubst.remove(tv);
			}
		}
		for (TermVariable tv : notYetSubst) {
			Term cIndex = getFreshConstant(tv);
			TermVariable[] vars = { tv }; 
			Term[] values = { cIndex };
			fTrans = m_Script.let(vars, values, fTrans);
			t = fTrans.toString();
		}
		return fTrans;		
	}
			
			
	


//	static Term getConstant(Script theory, String name, Sort sort) {
//		Term result = null;
//		Sort[] emptySorts = {};
//		theory.declareFun(name, emptySorts, sort);
//		Term[] emptyTerms = {};
//		result = theory.term(name, emptyTerms);
//		return result;
//	}
	
	
	
	
	
	
	public Term substituteRepresentants(Set<BoogieVar> boogieVars, Map<BoogieVar,TermVariable> substitution, Term term) {
		ArrayList<TermVariable> replacees = new ArrayList<TermVariable>();
		ArrayList<Term> replacers = new ArrayList<Term>();
		
		for (BoogieVar var : boogieVars) {
			TermVariable representant = var.getTermVariable();
			assert representant != null;
			Term substitute = substitution.get(var);
			assert substitute != null;
			replacees.add(representant);
			replacers.add(substitute);
		}
		TermVariable[] vars = replacees.toArray(new TermVariable[replacees.size()]);
		Term[] values = replacers.toArray(new Term[replacers.size()]);
		Term result = m_Script.let( vars , values, term);
		result = (new FormulaUnLet()).unlet(result);
		return result;
	}
	
	public Term substituteToRepresentants(Set<BoogieVar> boogieVars, Map<BoogieVar,TermVariable> boogieVar2TermVar, Term term) {
		ArrayList<TermVariable> replacees = new ArrayList<TermVariable>();
		ArrayList<Term> replacers = new ArrayList<Term>();
		
		for (BoogieVar var : boogieVars) {
			TermVariable representant = boogieVar2TermVar.get(var);
			assert representant != null;
			Term substitute = var.getTermVariable();
			assert substitute != null;
			replacees.add(representant);
			replacers.add(substitute);
		}
		TermVariable[] vars = replacees.toArray(new TermVariable[replacees.size()]);
		Term[] values = replacers.toArray(new Term[replacers.size()]);
		Term result = m_Script.let( vars , values, term);
		result = (new FormulaUnLet()).unlet(result);
		return result;
	}
	
	
	public Term substituteTermVariablesByTerms(Map<TermVariable, Term> substitution, Term term) {
		ArrayList<TermVariable> replacees = new ArrayList<TermVariable>();
		ArrayList<Term> replacers = new ArrayList<Term>();
		
		for (TermVariable tv : substitution.keySet()) {
			Term replacer = substitution.get(tv);
			assert replacer != null;
			replacees.add(tv);
			replacers.add(replacer);
		}
		TermVariable[] vars = replacees.toArray(new TermVariable[replacees.size()]);
		Term[] values = replacers.toArray(new Term[replacers.size()]);
		Term result = m_Script.let( vars , values, term);
		result = (new FormulaUnLet()).unlet(result);
		return result;
	}

	
	

	public Term getConstant(BoogieVar var) {
		String procString = var.getProcedure() == null ? "" : var.getProcedure();
		String varString;
		if (var.isOldvar()) {
			varString = "old("+var.getIdentifier()+")";
		} else {
			varString = var.getIdentifier();
		}
		String name = procString+ "_" + varString;
		Term constant = m_IndexedConstants.get(name);
		if (constant == null) {
			Sort resultSort = m_Smt2Boogie.getSort(var.getIType(), null);
			Sort[] emptySorts = {};
			m_Script.declareFun(name, emptySorts, resultSort);
			Term[] emptyTerms = {};
			constant = m_Script.term(name, emptyTerms);
			m_IndexedConstants.put(name, constant);
		}
		return constant;
	}


	public Term getIndexedConstant(BoogieVar var, int index) {
		String procString = var.getProcedure() == null ? "" : var.getProcedure();
		String varString;
		if (var.isOldvar()) {
			varString = "old(" + var.getIdentifier() + ")";
		} else {
			varString = var.getIdentifier();
		}
//		String indexString = quoteMinusOne(index);
		String indexString = String.valueOf(index);
		String name = procString+ "_" + varString + "_" + indexString;
		Term constant = m_IndexedConstants.get(name);
		if (constant == null) {
			Sort resultSort = m_Smt2Boogie.getSort(var.getIType(), null);
			Sort[] emptySorts = {};
			m_Script.declareFun(name, emptySorts, resultSort);
			Term[] emptyTerms = {};
			constant = m_Script.term(name, emptyTerms);
			m_IndexedConstants.put(name, constant);
		}
		return constant;
	}
	
	public Term getFreshConstant(TermVariable tv) {
		String name = "fresh_" + tv.getName() + m_FreshVariableCouter++;
		Sort resultSort = tv.getSort();
		Sort[] emptySorts = {};
		m_Script.declareFun(name, emptySorts, resultSort);
		Term[] emptyTerms = {};
		return m_Script.term(name, emptyTerms); 
	}
	
	/**
	 * @param int >=-1
	 * @return String representation of number, where -1 is represented as 
	 * <i>init</i> 
	 */
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

	
//	@Deprecated
//	private Term getIndexedConstant(String varName, int index, Sort sort) {
//		String name = "c_"+varName+"_"+index;
//		Term result = m_IndexedConstants.get(name);
//		if (result == null) {
//			Sort[] emptySorts = {};
//			m_Script.declareFun(name, emptySorts, sort);
//			Term[] emptyTerms = {};
//			result = m_Script.term(name, emptyTerms);
//			m_IndexedConstants.put(name, result);
//		}
//		return result; 
//	}
	
//	@Deprecated
//	private Term getOldVarConstant(String varName, Sort sort) {
//		String name = "c_"+varName+"_OLD";
//		Term result = m_IndexedConstants.get(name);
//		if (result == null) {		
//			Sort[] emptySorts = {};
//			m_Script.declareFun(name, emptySorts, sort);
//			Term[] emptyTerms = {};
//			result = m_Script.term(name, emptyTerms);
//			m_IndexedConstants.put(name, result);
//		}
//		return result;
//	}

	
	/**
	 * Check if each edge of automaton is inductive (resp. if inductivity can be
	 * refuted if <i>antiInductivity</i> is set).
	 * @param antiInductivity if false, we check if each edge is inductive, if
	 * true we check if inductivity of each edge can be refuted.
	 * @param assertInductivity if true, assert statements require inductivity
	 * (resp. anti-inductivity)
	 */
	public boolean checkInductivity(IAutomaton<CodeBlock, IPredicate> automaton, 
							boolean antiInductivity, boolean assertInductivity) {
		if (!(automaton instanceof INestedWordAutomatonOldApi)) {
			s_Logger.warn("unable to verify inductivity for this kind of automaton");
			return true;
		}
		INestedWordAutomatonOldApi<CodeBlock, IPredicate> nwa = (INestedWordAutomatonOldApi<CodeBlock, IPredicate>) automaton;
		if (antiInductivity) {
			s_Logger.debug("Start checking anti-inductivity of automaton");
		} else {
			s_Logger.debug("Start checking inductivity of automaton");
		}
		
		boolean result = true;
		// yield[0] is the number of edges whose inductiveness could be
		// proven
		// yield[1] is the number of edges whose inductiveness could be
		// refuted
		// yield[2] is the number of edges whose inductiveness could be
		// neither proven nor refuted because theorem prover too weak
		// yield[3] is the number of edges whose inductiveness could be
		// neither proven nor refuted because there were no interpolants
		
		int[] yield = new int[4]; 
		for(IPredicate state : nwa.getStates()) {
//			assert (state.getContent().getStateFormulas().size()==1);
			IPredicate sf1 = state;
			for (CodeBlock transAnnot : nwa.lettersInternal(state)) {
				for (IPredicate succState : nwa.succInternal(state, transAnnot)) {
//					assert (succState.getContent().getStateFormulas().size()==1);
					IPredicate sf2 = succState;

					if (sf1 == null || sf2 == null) {
						yield[3]++;
					}
					else {
						LBool inductivity = null;
						inductivity = isInductive(sf1, transAnnot, sf2);
						switch (inductivity) {
						case UNSAT: {
							yield[0]++;
							if (antiInductivity) {
								result = false;
								assert !assertInductivity || result : "anti inductivity failed";
							}
							break;
						}
						case SAT: {
							yield[1]++;
							if (!antiInductivity) {
								s_Logger.warn("Transition "+ transAnnot + " from " +
										sf1 + " to " + sf2 + " not inductive");
								result = false;
								assert !assertInductivity || result : "anti inductivity failed";
							}
							break;
						}
						case UNKNOWN: {
							yield[2]++;
							break;
						}
						default:
							throw new IllegalArgumentException();
						}
					}
				}
			}
			
			for (CodeBlock transAnnot : nwa.lettersCall(state)) {
				
				for (IPredicate succState : nwa.succCall(state, transAnnot)) {
//					assert (succState.getContent().getStateFormulas().size()==1);
					IPredicate sf2 = succState;

					if (sf1 == null || sf2 == null) {
						yield[3]++;
					}
					else {
						LBool inductivity = null;
						inductivity = isInductiveCall(sf1, (Call) transAnnot, sf2);
						switch (inductivity) {
						case UNSAT: {
							yield[0]++;
							if (antiInductivity) {
								result = false;
								assert !assertInductivity || result : "anti inductivity failed";
							}
							break;
						}
						case SAT: {
							yield[1]++;
							if (!antiInductivity) {
								s_Logger.warn("Transition "+ transAnnot + " from " +
										sf1 + " to " + sf2 + " not inductive");
								result = false;
								assert !assertInductivity || result : "anti inductivity failed";
							}
							break;
						}
						case UNKNOWN: {
							yield[2]++;
							break;
						}
						default:
							throw new IllegalArgumentException();
						}
					}
				}
				
				
			}
			
			for (CodeBlock transAnnot : nwa.lettersReturn(state)) {
				for (IPredicate hier : nwa.hierPred(state, transAnnot)) {

					for (IPredicate succState : nwa.succReturn(state, hier, transAnnot)) {
						//					assert (succState.getContent().getStateFormulas().size()==1);
						IPredicate sf2 = succState;
						IPredicate sfk = hier;

						if (sf1 == null || sf2 == null || sfk == null) {
							yield[3]++;
						}
						else {
							LBool inductivity = null;
							inductivity = isInductiveReturn(sf1, sfk, (Return) transAnnot, sf2);
							switch (inductivity) {
							case UNSAT: {
								yield[0]++;
								if (antiInductivity) {
									result = false;
									assert !assertInductivity || result : "anti inductivity failed";
								}
								break;
							}
							case SAT: {
								yield[1]++;
								if (!antiInductivity) {
									s_Logger.warn("Transition "+ transAnnot + " from " +
											sf1 + " to " + sf2 + " not inductive");
									result = false;
									assert !assertInductivity || result : "anti inductivity failed";
								}
								break;
							}
							case UNKNOWN: {
								yield[2]++;
								break;
							}
							default:
								throw new IllegalArgumentException();
							}
						}
					}
				}
				
				
			}
			
			
		}
		s_Logger.info("Interpolant automaton has " + (yield[0]+yield[1]+yield[2]+yield[3]) + 
				" edges. " + yield[0] + " inductive. " + yield[1] +
				" not inductive. " +	yield[2]+ " times theorem prover too" +
				" weak to decide inductivity. " + yield[3]+ " times interpolants"
				+ " missing.");
		return result;
	}
	
	
	
	

	
	
	
	
	
	
	
	
	
	
	public boolean cfgInductive(RootNode rootNode) {
		boolean result = true;
		// yield[0] is the number of edges whose inductiveness could be
		// proven
		// yield[1] is the number of edges whose inductiveness could be
		// refuted
		// yield[2] is the number of edges whose inductiveness could be
		// neither proven nor refuted because theorem prover too weak
		// yield[3] is the number of edges whose inductiveness could be
		// neither proven nor refuted because there were no interpolants
		int[] yield = new int[4]; 
		
		List<RCFGNode> initialNodes = rootNode.getOutgoingNodes();
		Set<ProgramPoint> visited = new HashSet<ProgramPoint>();
		List<ProgramPoint> worklist = new LinkedList<ProgramPoint>();
		
		if (initialNodes != null) {
			for (RCFGNode initINode : initialNodes) {
				ProgramPoint initNode = (ProgramPoint) initINode;
				visited.add(initNode);
				worklist.add(initNode);
			}
		} else {
			s_Logger.warn("There was no procedure with an implementation");
		}
		while (!worklist.isEmpty()) {
			ProgramPoint locNode = worklist.remove(0);
			for (RCFGEdge iEdge : locNode.getOutgoingEdges()) {
				
				RCFGNode iSuccLoc = iEdge.getTarget();
				ProgramPoint succLoc = (ProgramPoint) iSuccLoc;
				if (!visited.contains(succLoc)) {
					visited.add(succLoc);
					worklist.add(succLoc);
				}
				
				IPredicate sf1 = getHoareAnnotation(locNode);
				if (sf1 == null) {
					s_Logger.warn(locNode + " has no Hoare annotation");
					continue;
				}

				IPredicate sf2 = getHoareAnnotation(succLoc);
				if (sf2 == null) {
					s_Logger.warn(succLoc + " has no Hoare annotation");
					continue;
				}


				LBool inductivity;
				CodeBlock transAnnot;

				if (iEdge instanceof Call) {
					transAnnot= ((Call) iEdge);
					inductivity = isInductiveCall(sf1, (Call) transAnnot, sf2);
				}
				else if (iEdge instanceof Return) {
					ProgramPoint callerNode = ((Return) iEdge).getCallerProgramPoint();
					IPredicate sfk = getHoareAnnotation(callerNode);
					if (sfk == null) {
						s_Logger.warn(callerNode + " has no Hoare annotation");
						continue;
					}
					transAnnot= ((Return) iEdge);
					inductivity = isInductiveReturn(sf1, sfk, (Return) transAnnot, sf2, true);
				}
				else if (iEdge instanceof Summary) {
					transAnnot= ((Summary) iEdge);
					if (((Summary) transAnnot).calledProcedureHasImplementation()) {
						continue;
					}
					else {
						inductivity = isInductive(sf1, transAnnot, sf2, true);
					}
				}
				else if (iEdge instanceof CodeBlock) {
					transAnnot= ((CodeBlock) iEdge);
					inductivity = isInductive(sf1, transAnnot, sf2, true);
				}
				else {
					continue;
				}

				switch (inductivity) {
				case UNSAT: {
					yield[0]++;
					break;
				}
				case SAT: {
					yield[1]++;
					s_Logger.warn("Transition   "+ transAnnot + "   from   "+ sf1 + "   to   " + sf2 + "   not inductive");
					result = false;
					break;
				}
				case UNKNOWN: {
					yield[2]++;
					//						s_Logger.warn("Theorem prover too weak to decide inductiveness");
					break;
				}
				default:
					throw new IllegalArgumentException();
				}
			}
		}
		s_Logger.info("CFG has " + (yield[0]+yield[1]+yield[2]+yield[3]) + 
				" edges. " + yield[0] + " inductive. " + yield[1] +
				" not inductive. " +	yield[2]+ " times theorem prover too" +
				" weak to decide inductivity. " + yield[3]+ " times interpolants"
				+ " missing.");
		return result;
	}
	
	
	
	/**
	 * Construct Predicate which represents the same Predicate as ps, but
	 * where all globalVars are renamed to oldGlobalVars.
	 */
	public ISLPredicate renameGlobalsToOldGlobals(ISLPredicate ps) {
		if (isDontCare(ps)){
			return this.newDontCarePredicate(ps.getProgramPoint());
		}
		
		Set<BoogieVar> allVars = ps.getVars();
		Set<BoogieVar> varsOfRenamed = new HashSet<BoogieVar>();
		varsOfRenamed.addAll(allVars);
		Set<BoogieVar> globalVars = new HashSet<BoogieVar>();
		for (BoogieVar var : allVars) {
			if (var.isGlobal()) {
				globalVars.add(var);
				varsOfRenamed.remove(var);
			}
		}
		List<TermVariable> vars = new ArrayList<TermVariable>();
		List<Term> values = new ArrayList<Term>();
		for (BoogieVar globalBoogieVar : globalVars) {
			if (!globalBoogieVar.isOldvar()) {
				vars.add(globalBoogieVar.getTermVariable());
				BoogieVar oldBoogieVar = this.getOldVar(globalBoogieVar);
				varsOfRenamed.add(oldBoogieVar);
				values.add(oldBoogieVar.getTermVariable());
			}
		}
		ps.getFormula().getFreeVars();
		Term renamedFormula = m_Script.let(vars.toArray(new TermVariable[0]), 
								values.toArray(new Term[0]), ps.getFormula());
		SmtManager.TermVarsProc tvp = this.computeTermVarsProc(renamedFormula);
		SPredicate result = this.newSPredicate(ps.getProgramPoint(), 
				renamedFormula, tvp.getProcedures(),
				tvp.getVars(), tvp.getClosedFormula());
		return result;
	}
	
	
	
	/**
	 * Computes the strongest postcondition of the given predicate p and
	 * the CodeBlock cb.
	 * @param p
	 * @param cb
	 * @return
	 */
	public IPredicate strongestPostcondition(IPredicate p, CodeBlock cb) {
		if (cb instanceof Call) {
			throw new UnsupportedOperationException("This method is not responsible for Call-Statemtens.");
		} else if (cb instanceof Return) {
			throw new UnsupportedOperationException("This method is not responsible for Return-Statements.");
		} else if (cb instanceof InterproceduralSequentialComposition) {
			throw new UnsupportedOperationException();
		}
		// Check if p is false
		if (p.getFormula() == False()) {
			return p;
		}
		TransFormula tf = cb.getTransitionFormula();	
		Term tf_term = tf.getFormula();		
		ArrayList<TermVariable> replacees = new ArrayList<TermVariable>();
		ArrayList<Term> replacers = new ArrayList<Term>();
		// 1 Rename the invars of the TransFormula of the given CodeBlock cb into TermVariables
		for (BoogieVar bv : tf.getInVars().keySet()) {
			// TODO: Check if bv is a free var
			// if not, then continue, there is nothing to do
			TermVariable bv_term = tf.getInVars().get(bv);
			// Case: var in InVars and var not in OutVars
			if (!tf.getOutVars().keySet().contains(bv)) {
				throw new UnsupportedOperationException("This case is still undefined!");
			} 
			// Case: var in InVars and var in OutVars and Invars(var) == OutVars(var)
			else if (bv_term == tf.getOutVars().get(bv)) {
				replacees.add(bv_term);
				replacers.add(bv.getTermVariable());
			}
			// Case: var in InVars and var in OutVars and Invars(var) != OutVars(var)
			else {
				if (!tf.getAssignedVars().contains(bv)) {
					replacees.add(bv_term);
					replacers.add(bv.getTermVariable());
				}
			}
		}
		

		Term tf_term_invars_renamed = substituteVars(tf_term, replacees, replacers);
		
		// 2 Rename the outvars of the TransFormula of the given CodeBlock cb into TermVariables
		replacees.clear();
		replacers.clear();
		for (BoogieVar bv : tf.getOutVars().keySet()) {
			// TODO: Check if bv is a free var
			// if not, then continue, there is nothing to do
			TermVariable bv_term = tf.getOutVars().get(bv);
			// Case: var not in InVars and var in OutVars
			if (!tf.getInVars().keySet().contains(bv)) {
				replacees.add(bv_term);
				replacers.add(bv.getTermVariable());
			} 
			// Case: var in InVars and var in OutVars and Invars(var) == OutVars(var)
			else if (bv_term == tf.getInVars().get(bv)) {
				continue;
			}
			// Case: var in InVars and var in OutVars and Invars(var) != OutVars(var)
			else if (bv_term != tf.getInVars().get(bv)) {
				replacees.add(bv_term);
				replacers.add(bv.getTermVariable());
			}
		}

		Term tf_term_outvars_renamed = substituteVars(tf_term_invars_renamed, replacees, replacers);

				
		
		// 3. Connect the renamed predicate and the renamed TransFormula by an logical and.
		Term predicate_AND_tf_term = Util.and(m_Script, p.getFormula(), tf_term_outvars_renamed);
		// Select from the invars the freevars, and existentially quantify over them. Quantification is done
		// in step 4 below.
		TermVariable[] invarsOccuringInFreeVarsOrAssignedVars_TermVariables = new TermVariable[tf.getInVars().keySet().size()];
		Map<BoogieVar, TermVariable> invarsOccuringInFreeVarsOrAssignedVars = new HashMap<BoogieVar, TermVariable>();
		{
			ArrayList<TermVariable> freeVars = new ArrayList<TermVariable>();
			for (int j = 0; j < predicate_AND_tf_term.getFreeVars().length; j++) {
				freeVars.add(predicate_AND_tf_term.getFreeVars()[j]);
			}
			int i = 0;
			for (BoogieVar bv : tf.getInVars().keySet()) {
				if (freeVars.contains(tf.getInVars().get(bv))) {
					invarsOccuringInFreeVarsOrAssignedVars.put(bv, tf.getInVars().get(bv));
				}
			}
			for (BoogieVar bv : tf.getAssignedVars()) {
				if (p.getVars().contains(bv)) {
					if (!invarsOccuringInFreeVarsOrAssignedVars.keySet().contains(bv)) {
						invarsOccuringInFreeVarsOrAssignedVars.put(bv, tf.getOutVars().get(bv));
					}
				}
			}
			invarsOccuringInFreeVarsOrAssignedVars_TermVariables = new TermVariable[invarsOccuringInFreeVarsOrAssignedVars.values().size()];
			for (TermVariable tv : invarsOccuringInFreeVarsOrAssignedVars.values()) {
				invarsOccuringInFreeVarsOrAssignedVars_TermVariables[i] = tv;
				i++;
			}
		}
		// 4. Existentially quantify the invars in TransFormula of the given CodeBlock cb, but only if the set of invars
		// is not empty.
		Term result = null;
		if (invarsOccuringInFreeVarsOrAssignedVars_TermVariables.length > 0) {
			replacees.clear(); replacers.clear();
			for (BoogieVar bv : invarsOccuringInFreeVarsOrAssignedVars.keySet()) {
				replacees.add(bv.getTermVariable());
				replacers.add(invarsOccuringInFreeVarsOrAssignedVars.get(bv));
			}
			Term predicate_renamed = substituteVars(p.getFormula(), replacees, replacers);
			predicate_AND_tf_term = Util.and(m_Script, predicate_renamed, tf_term_outvars_renamed);
			
			result = DestructiveEqualityResolution.quantifier(m_Script, Script.EXISTS,
					invarsOccuringInFreeVarsOrAssignedVars_TermVariables, predicate_AND_tf_term, (Term[][]) null);
		} else {
			result = predicate_AND_tf_term;
		}
		// Compute the set of BoogieVars, the procedures and the term
		TermVarsProc tvp = computeTermVarsProc(result);
		// Compute a closed formula version of result, it is needed for newPredicate.
		Term result_as_closed_formula = SmtManager.computeClosedFormula(result, tvp.getVars(), m_Script);
		return newPredicate(result, tvp.getProcedures(), tvp.getVars(), result_as_closed_formula);
	}
	
	/**
	 * Substitutes the replacees through replacers in the given formula.
	 * @return formula, where replacees are substituted by replacers.
	 */
	private Term substituteVars(Term formula, List<TermVariable> replacees, List<Term> replacers) {
		
		assert(replacees.size() == replacers.size());
		TermVariable[] vars = replacees.toArray(new TermVariable[replacees
		                                                         .size()]);
		Term[] values = replacers.toArray(new Term[replacers.size()]);
		Term predicate_renamed = m_Script.let(vars, values, formula);
		predicate_renamed = (new FormulaUnLet()).unlet(predicate_renamed);
		return predicate_renamed;
	}
	
	
	/**
	 * Compute the strongest postcondition for a predicate and a call statement.
	 * Call statements must be treated in a special way.
	 */
	public IPredicate strongestPostcondition(IPredicate p, Call call) {

		// 1. Compute those global variable assignments, i.e. x_global = old(x_global) if x_global is
		// a global variable.
		TransFormula globalVarsAssignment = m_ModifiableGlobals.getGlobalVarsAssignment(call.getCallStatement().getMethodName());
		// 1.1 Rename the invars in global variable assignments.
		List<TermVariable> replacees = new ArrayList<TermVariable>();
		List<Term> replacers = new ArrayList<Term>();
		for (BoogieVar bv : globalVarsAssignment.getInVars().keySet()) {
			replacees.add(globalVarsAssignment.getInVars().get(bv));
			replacers.add(bv.getTermVariable());
		}
		Term globalVars_Invars_Renamed = substituteVars(globalVarsAssignment.getFormula(), replacees, replacers);
		// 1.2 Rename the outvars in global variable assignments.
		replacees.clear();
		replacers.clear();
		for (BoogieVar bv : globalVarsAssignment.getOutVars().keySet()) {
			replacees.add(globalVarsAssignment.getOutVars().get(bv));
			replacers.add(bv.getTermVariable());
		}
		
		Term globalVars_InVarsRenamed_OutVarsRenamed = substituteVars(globalVars_Invars_Renamed, replacees, replacers);
		replacees.clear();
		replacers.clear();
		
		// Collect the local variables
		Set<TermVariable> localVars = new HashSet<TermVariable>();
		for (BoogieVar bv : p.getVars()) {
			if (!m_GlobalVars.containsKey(bv.getIdentifier())) {
				localVars.add(bv.getTermVariable());
			}
		}
		TransFormula call_TF = call.getTransitionFormula();
		// 2.1 Rename the invars of the term of the Call-Statement.
		for (BoogieVar bv : call_TF.getInVars().keySet()) {
			replacees.add(call_TF.getInVars().get(bv));
			replacers.add(bv.getTermVariable());
			// Add this invar to localVars, if it is not contained in outVars, such
			// that it is later quantified.
			if (!call_TF.getOutVars().keySet().contains(bv)) {
				localVars.add(bv.getTermVariable());
			}
		}
		Term call_Term_InVarsRenamed = substituteVars(call_TF.getFormula(), replacees, replacers);
		replacees.clear();
		replacers.clear();
		// 2.2 Rename the outvars of the term of the Call-Statement.
		for (BoogieVar bv : call_TF.getOutVars().keySet()) {
			replacees.add(call_TF.getOutVars().get(bv));
			replacers.add(bv.getTermVariable());
		}
		
		
		Term call_Term_InVarsRenamed_OutVarsRenamed = substituteVars(call_Term_InVarsRenamed, replacees, replacers);
		Term callTerm_AND_predicate = Util.and(m_Script, call_Term_InVarsRenamed_OutVarsRenamed, p.getFormula());
		Term callTerm_AND_predicate_quantified = callTerm_AND_predicate;
		if (localVars.size() > 0) {
			callTerm_AND_predicate_quantified = DestructiveEqualityResolution.quantifier(m_Script, Script.EXISTS,
					localVars.toArray(new TermVariable[localVars.size()]),
					callTerm_AND_predicate, (Term[][])null);
		}
		
		Term result = Util.and(m_Script, callTerm_AND_predicate_quantified, globalVars_InVarsRenamed_OutVarsRenamed);
		
		TermVarsProc tvp = computeTermVarsProc(result);
		Term result_as_closed_formula = SmtManager.computeClosedFormula(result, tvp.getVars(), m_Script);
		return newPredicate(result, tvp.getProcedures(), tvp.getVars(), result_as_closed_formula);
	}
	
	
	/**
	 * Compute strongest postcondition for a return statement, where calleePred
	 * is the predicate that holds in the called procedure before the return 
	 * statement and callerPred is the predicate that held in the calling 
	 * procedure before the corresponding call. 
	 */
	public IPredicate strongestPostcondition(IPredicate calleePred, 
											IPredicate callerPred, Return ret) {
		// 1. Rename invars in Term of Return statement
		List<TermVariable> replacees = new ArrayList<TermVariable>();
		List<Term> replacers = new ArrayList<Term>();
		TransFormula ret_TF = ret.getTransitionFormula();
		for (BoogieVar bv : ret_TF.getInVars().keySet()) {
			replacees.add(ret_TF.getInVars().get(bv));
			replacers.add(bv.getTermVariable());
		}
		Term ret_Term_InVarsRenamed = substituteVars(ret_TF.getFormula(), replacees, replacers);
		replacees.clear();
		replacers.clear();
		//2. Rename outvars in Term of Return statement
		for (BoogieVar bv : ret_TF.getOutVars().keySet()) {
			replacees.add(ret_TF.getOutVars().get(bv));
			replacers.add(bv.getTermVariable());
		}
		Term ret_Term_InVarsRenamed_OutVarsRenamed = substituteVars(ret_Term_InVarsRenamed, replacees, replacers);
		// 3. Compute the local variables of the called procedure.
		Set<TermVariable> localVarsOfCalledProc = new HashSet<TermVariable>();
		for (BoogieVar bv : calleePred.getVars()) {
			if (!callerPred.getVars().contains(bv)) {
				if (!m_GlobalVars.containsKey(bv.getIdentifier())) {
					localVarsOfCalledProc.add(bv.getTermVariable());
				}
			}
		}
		
		Term ret_Term_AND_calleePred = Util.and(m_Script, ret_Term_InVarsRenamed_OutVarsRenamed, calleePred.getFormula());
		Term ret_Term_AND_calleePred_quantified = ret_Term_AND_calleePred;
		if (localVarsOfCalledProc.size() > 0) {
			ret_Term_AND_calleePred_quantified = DestructiveEqualityResolution.quantifier(m_Script, Script.EXISTS,
					localVarsOfCalledProc.toArray(new TermVariable[localVarsOfCalledProc.size()]),
					ret_Term_AND_calleePred, (Term[][])null);
		}
				
		TermVarsProc tvp = computeTermVarsProc(ret_Term_AND_calleePred_quantified);
		Term ret_Term_AND_calleePred_as_closed_formula = SmtManager.computeClosedFormula(ret_Term_AND_calleePred_quantified, tvp.getVars(), m_Script);
		return newPredicate(ret_Term_AND_calleePred_quantified, tvp.getProcedures(), tvp.getVars(), ret_Term_AND_calleePred_as_closed_formula);
	}

	
	// TODO: Do we need also a special SP for call and return?
	public IPredicate strongestPostconditionSpecial(IPredicate p, CodeBlock cb) {

		Set<TermVariable> assignedVars = new HashSet<TermVariable>();
		for (BoogieVar bv : cb.getTransitionFormula().getAssignedVars()) {
			assignedVars.add(bv.getTermVariable());
		}
		
		Term formulaAssignedVarsQuantified = p.getFormula();
		if (assignedVars.size() > 0) {
			formulaAssignedVarsQuantified = m_Script.quantifier(Script.EXISTS,
					assignedVars.toArray(new TermVariable[assignedVars.size()]),
					p.getFormula(), (Term[][]) null);
		} 
		Term result = formulaAssignedVarsQuantified;
		TermVarsProc tvp = computeTermVarsProc(result);
		Term result_as_closed_formula = SmtManager.computeClosedFormula(result, tvp.getVars(), m_Script);
		return newPredicate(result, tvp.getProcedures(), tvp.getVars(), result_as_closed_formula);
		
	}

	
	/**
	 * Computes the weakest precondition of the given predicate p and the
	 * CodeBlock cb. 
	 */
	public IPredicate weakestPrecondition(IPredicate p, CodeBlock cb) {
		if (cb instanceof Call) {
			throw new UnsupportedOperationException();
		} else if (cb instanceof Return) {
			throw new UnsupportedOperationException();
		} else if (cb instanceof InterproceduralSequentialComposition) {
			throw new UnsupportedOperationException();
		}
		// If the given predicate p is true, then return true, since wp(true, st) = true for every statement st.
		if (p.getFormula() == True()) {
			return p;
		}
		TransFormula tf = cb.getTransitionFormula();	
		Term tf_term = tf.getFormula();		
		ArrayList<TermVariable> replacees = new ArrayList<TermVariable>();
		ArrayList<Term> replacers = new ArrayList<Term>();
		// 1 Rename the invars of the TransFormula of the given CodeBlock cb into TermVariables
		for (BoogieVar bv : tf.getInVars().keySet()) {
			TermVariable bv_term = tf.getInVars().get(bv);
			// Case: var in InVars and var not in OutVars
			if (!tf.getOutVars().keySet().contains(bv)) {
				throw new UnsupportedOperationException("This case is still undefined!");
			}
			
			// Case: var in InVars and var in OutVars and Invars(var) == OutVars(var)
			else if (bv_term == tf.getOutVars().get(bv)) {
				replacees.add(bv_term);
				replacers.add(bv.getTermVariable());
			}
			// Case: var in InVars and var in OutVars and Invars(var) != OutVars(var)
			else {
				replacees.add(bv_term);
				replacers.add(bv.getTermVariable());
			}
		}
		

		Term tf_term_invars_renamed = substituteVars(tf_term, replacees, replacers);
		
		// 2 Rename the outvars of the TransFormula of the given CodeBlock cb into TermVariables
		replacees.clear();
		replacers.clear();
		for (BoogieVar bv : tf.getOutVars().keySet()) {
			TermVariable bv_term = tf.getOutVars().get(bv);
			// Case: var not in InVars and var in OutVars
			if (!tf.getInVars().keySet().contains(bv)) {
				continue;
			}  
			// Case: var in InVars and var in OutVars and Invars(var) == OutVars(var)
			else if (bv_term == tf.getInVars().get(bv)) {
				continue;
			}
			// Case: var in InVars and var in OutVars and Invars(var) != OutVars(var)
			else {
				if (!tf.getAssignedVars().contains(bv)) {
					replacees.add(bv_term);
					replacers.add(bv.getTermVariable());
				}
			}
		}

		Term tf_term_outvars_renamed = substituteVars(tf_term_invars_renamed, replacees, replacers);

				
		
		// 3. Connect the renamed TransFormula and the renamed predicate by a logical implication.
		//    (TransFormula) --> Predicate
		Term NOT_tfterm_OR_predicate = Util.or(m_Script, Util.not(m_Script, tf_term_outvars_renamed), p.getFormula());
		// Since WP is computed backwards, now you select from the outvars the freevars, and universally quantify over them.
		// Quantification is done in step 4 below.
		TermVariable[] outvarsOccuringInFreeVars_TermVariables = new TermVariable[tf.getOutVars().keySet().size()];
		Map<BoogieVar, TermVariable> outvarsOccuringInFreeVars = new HashMap<BoogieVar, TermVariable>();
		{
			ArrayList<TermVariable> freeVars = new ArrayList<TermVariable>();
			for (int j = 0; j < NOT_tfterm_OR_predicate.getFreeVars().length; j++) {
				freeVars.add(NOT_tfterm_OR_predicate.getFreeVars()[j]);
			}
			int i = 0;
			for (BoogieVar bv : tf.getOutVars().keySet()) {
				if (freeVars.contains(tf.getOutVars().get(bv))) {
					outvarsOccuringInFreeVars.put(bv, tf.getOutVars().get(bv));
				}
			}
			outvarsOccuringInFreeVars_TermVariables = new TermVariable[outvarsOccuringInFreeVars.values().size()];
			for (TermVariable tv : outvarsOccuringInFreeVars.values()) {
				outvarsOccuringInFreeVars_TermVariables[i] = tv;
				i++;
			}
		}
		// 4. Universally quantify the invars in TransFormula of the given CodeBlock cb, but only if the set of invars
		// is not empty.
		Term result = null;
		if (outvarsOccuringInFreeVars_TermVariables.length > 0) {
			replacees.clear(); replacers.clear();
			for (BoogieVar bv : outvarsOccuringInFreeVars.keySet()) {
				replacees.add(bv.getTermVariable());
				replacers.add(outvarsOccuringInFreeVars.get(bv));
			}
			Term predicate_renamed = substituteVars(p.getFormula(), replacees, replacers);
			NOT_tfterm_OR_predicate = Util.or(m_Script, Util.not(m_Script, tf_term_outvars_renamed), predicate_renamed);
			
			result = DestructiveEqualityResolution.quantifier(m_Script, Script.FORALL,
					outvarsOccuringInFreeVars_TermVariables,
					NOT_tfterm_OR_predicate, (Term[][]) null);
		} else {
			result = NOT_tfterm_OR_predicate;
		}
		// Compute the set of BoogieVars, the procedures and the term
		TermVarsProc tvp = computeTermVarsProc(result);
		// Compute a closed formula version of result, it is needed for newPredicate.
		Term result_as_closed_formula = SmtManager.computeClosedFormula(result, tvp.getVars(), m_Script);
		return newPredicate(result, tvp.getProcedures(), tvp.getVars(), result_as_closed_formula);
	}
	
	
	/**
	 * Compute the weakest precondition for a call statement, where the returneePred
	 * is the predicate that holds in the returned procedure before the call statement
	 * and returnerPred is the predicate that held in the returning procedure before the
	 * corresponding  return.
	 */
	public IPredicate weakestPrecondition(IPredicate returneePred, 
						IPredicate returnerPred, Call call) {
		
		// 1. Rename invars in Term of Call statement
		List<TermVariable> replacees = new ArrayList<TermVariable>();
		List<Term> replacers = new ArrayList<Term>();
		TransFormula call_TF = call.getTransitionFormula();
		for (BoogieVar bv : call_TF.getInVars().keySet()) {
			replacees.add(call_TF.getInVars().get(bv));
			replacers.add(bv.getTermVariable());
		}
		Term call_Term_InVarsRenamed = substituteVars(call_TF.getFormula(), replacees, replacers);
		replacees.clear();
		replacers.clear();
		//2. Rename outvars in Term of Call statement
		for (BoogieVar bv : call_TF.getOutVars().keySet()) {
			replacees.add(call_TF.getOutVars().get(bv));
			replacers.add(bv.getTermVariable());
		}
		Term call_Term_InVarsRenamed_OutVarsRenamed = substituteVars(call_Term_InVarsRenamed, replacees, replacers);
		// 3. Compute the local variables of the called procedure.
		Set<TermVariable> localVarsOfCalledProc = new HashSet<TermVariable>();
		for (BoogieVar bv : returneePred.getVars()) {
			if (!returnerPred.getVars().contains(bv)) {
				if (!m_GlobalVars.containsKey(bv.getIdentifier())) {
					localVarsOfCalledProc.add(bv.getTermVariable());
				}
			}
		}

		Term call_Term_IMPLIES_returneePred = Util.or(m_Script, 
				Util.not(m_Script, call_Term_InVarsRenamed_OutVarsRenamed),
				returneePred.getFormula());
		Term call_Term_AND_returneePred_quantified = call_Term_IMPLIES_returneePred;
		if (localVarsOfCalledProc.size() > 0) {
			call_Term_AND_returneePred_quantified = DestructiveEqualityResolution.quantifier(m_Script, Script.FORALL,
					localVarsOfCalledProc.toArray(new TermVariable[localVarsOfCalledProc.size()]),
					call_Term_IMPLIES_returneePred, (Term[][])null);
		}

		TermVarsProc tvp = computeTermVarsProc(call_Term_AND_returneePred_quantified);
		Term call_Term_AND_returneePred_as_closed_formula = SmtManager.computeClosedFormula(call_Term_AND_returneePred_quantified, tvp.getVars(), m_Script);
		return newPredicate(call_Term_AND_returneePred_quantified, tvp.getProcedures(), tvp.getVars(), call_Term_AND_returneePred_as_closed_formula);
	}
	
	public IPredicate weakestPrecondition(IPredicate p, Return ret) {
		// 1. Compute those global variable assignments, i.e. x_global = old(x_global) if x_global is
		// a global variable.
		TransFormula globalVarsAssignment = m_ModifiableGlobals.getGlobalVarsAssignment(
				ret.getCorrespondingCall().getCallStatement().getMethodName());
		// 1.1 Rename the invars in global variable assignments.
		List<TermVariable> replacees = new ArrayList<TermVariable>();
		List<Term> replacers = new ArrayList<Term>();
		for (BoogieVar bv : globalVarsAssignment.getInVars().keySet()) {
			replacees.add(globalVarsAssignment.getInVars().get(bv));
			replacers.add(bv.getTermVariable());
		}
		Term globalVars_Invars_Renamed = substituteVars(globalVarsAssignment.getFormula(), replacees, replacers);
		// 1.2 Rename the outvars in global variable assignments.
		replacees.clear();
		replacers.clear();
		for (BoogieVar bv : globalVarsAssignment.getOutVars().keySet()) {
			replacees.add(globalVarsAssignment.getOutVars().get(bv));
			replacers.add(bv.getTermVariable());
		}
		
		Term globalVars_InVarsRenamed_OutVarsRenamed = substituteVars(globalVars_Invars_Renamed, replacees, replacers);
		replacees.clear();
		replacers.clear();
		
		// Collect the local variables
		Set<TermVariable> localVars = new HashSet<TermVariable>();
		for (BoogieVar bv : p.getVars()) {
			if (!m_GlobalVars.containsKey(bv.getIdentifier())) {
				localVars.add(bv.getTermVariable());
			}
		}
		TransFormula ret_TF = ret.getTransitionFormula();
		// 2.1 Rename the invars of the term of the Return-Statement.
		for (BoogieVar bv : ret_TF.getInVars().keySet()) {
			replacees.add(ret_TF.getInVars().get(bv));
			replacers.add(bv.getTermVariable());
		}
		Term ret_Term_InVarsRenamed = substituteVars(ret_TF.getFormula(), replacees, replacers);
		replacees.clear();
		replacers.clear();
		// 2.2 Rename the outvars of the term of the Return-Statement.
		for (BoogieVar bv : ret_TF.getOutVars().keySet()) {
			replacees.add(ret_TF.getOutVars().get(bv));
			replacers.add(bv.getTermVariable());
			// Add this invar to localVars, if it is not contained in outVars, such
			// that it is later quantified.
			if (!ret_TF.getOutVars().keySet().contains(bv)) {
				localVars.add(bv.getTermVariable());
			}

		}
		


		Term ret_Term_InVarsRenamed_OutVarsRenamed = substituteVars(ret_Term_InVarsRenamed, replacees, replacers);
		
		Term ret_Term_AND_globalVarsAssignment = Util.and(m_Script, 
				ret_Term_InVarsRenamed_OutVarsRenamed, 
				globalVars_InVarsRenamed_OutVarsRenamed);
		
		Term retTermANDglobalVarsAssignment_IMPLIES_predicate = Util.or(m_Script, 
				Util.not(m_Script, ret_Term_AND_globalVarsAssignment), p.getFormula());
		
		Term retTermANDglobalVarsAssignment_IMPLIES_predicate_quantified = retTermANDglobalVarsAssignment_IMPLIES_predicate;
		if (localVars.size() > 0) {
			retTermANDglobalVarsAssignment_IMPLIES_predicate_quantified = DestructiveEqualityResolution.quantifier(m_Script, Script.FORALL,
					localVars.toArray(new TermVariable[localVars.size()]),
					retTermANDglobalVarsAssignment_IMPLIES_predicate, (Term[][])null);
		}

		Term result = Util.and(m_Script, retTermANDglobalVarsAssignment_IMPLIES_predicate_quantified, globalVars_InVarsRenamed_OutVarsRenamed);

		TermVarsProc tvp = computeTermVarsProc(result);
		Term result_as_closed_formula = SmtManager.computeClosedFormula(result, tvp.getVars(), m_Script);
		return newPredicate(result, tvp.getProcedures(), tvp.getVars(), result_as_closed_formula);
	}
	
	
	//FIXME: does not work im SmtInterpol2
	public static void dumpInterpolProblem(Term[] formulas,
			int iterationNumber, int interpolProblem,
			String dumpPath, Script theory) {
//		String filename = "Iteration" + iterationNumber + "_InterpolProblem" 
//				+ interpolProblem + ".smt";
//		File file = new File(dumpPath + "/" +filename);
//		FileWriter fileWriter;
//		try {
//			fileWriter = new FileWriter(file);
//			PrintWriter printWriter = new PrintWriter(fileWriter);
//			fileWriter.close();
//		} catch (IOException e) {
//			e.printStackTrace();
//		}
	}
	
	//FIXME: does not work im SmtInterpol2
	static protected void dumpSatProblem(Term formula,
			int iterationNumber, int satProbNumber,
			String dumpPath, Script theory) {
//		String filename = "Iteration" + iterationNumber + "_SatProblem" 
//			+ satProbNumber + ".smt";
//		File file = new File(dumpPath + "/" +filename);
//		FileWriter fileWriter;
//		try {
//			fileWriter = new FileWriter(file);
//			PrintWriter printWriter = new PrintWriter(fileWriter);
//			fileWriter.close();
//		} catch (IOException e) {
//			e.printStackTrace();
//		}
	}





	public static HoareAnnotation getHoareAnnotation(ProgramPoint programPoint) {
		return ((HoareAnnotation) programPoint.getPayload().
								   getAnnotations().get(Activator.s_PLUGIN_ID));
	}


	public LBool checkSatWithFreeVars(Term negation) {
		LBool result = Util.checkSat(m_Script, negation);
//		if (result == LBool.UNKNOWN) {
//			Object[] reason = m_Script.getInfo(":reason-unknown");
//		}
//		de.uni_freiburg.informatik.ultimate.smtinterpol.util.ReasonUnknown reasonUnknown = reason[0];
		return result;
	}
	
	
	public IPredicate[] computeInterpolants(IPredicate precondition, 
										   IPredicate postcondition, 
										   IRun<CodeBlock,IPredicate> run) {
		return null;
	}
	

	

	
	
//	public class TermVarsProcs {
//		private final Term mTerm;
//		private final Set<BoogieVar> mVars;
//		private final Set<String> mProcs;
//		
//		
//		
//	}
	

			
			
	


		

	
	
	
	//FIXME: remove once enough tested
	private void testMyReturnDataflowCheck(IPredicate ps1, IPredicate psk,
			Return ta, IPredicate ps2, LBool result) {
		if (ps2.getFormula() == m_Script.term("false")) {
			return;
		}
		EdgeChecker edgeChecker = new EdgeChecker(this, m_ModifiableGlobals);
		LBool testRes = edgeChecker.sdecReturn(ps1, psk, ta, ps2);
		if (testRes != null) {
//			assert testRes == result : "my return dataflow check failed";
			if (testRes != result) {
				edgeChecker.sdecReturn(ps1, psk, ta, ps2);
			}
		}
	}
	
	
	//FIXME: remove once enough tested
	private void testMyCallDataflowCheck(IPredicate ps1,
			Call ta, IPredicate ps2, LBool result) {
		if (ps2.getFormula() == m_Script.term("false")) {
			return;
		}
		EdgeChecker edgeChecker = new EdgeChecker(this, m_ModifiableGlobals);
		LBool testRes = edgeChecker.sdecCall(ps1, ta, ps2);
		if (testRes != null) {
			assert testRes == result : "my call dataflow check failed";
//			if (testRes != result) {
//				edgeChecker.sdecReturn(ps1, psk, ta, ps2);
//			}
		}
	}
	
	
	//FIXME: remove once enough tested
	private void testMyInternalDataflowCheck(IPredicate ps1,
			CodeBlock ta, IPredicate ps2, LBool result) {
		if (ps2.getFormula() == m_Script.term("false")) {
			EdgeChecker edgeChecker = new EdgeChecker(this, m_ModifiableGlobals);
			LBool testRes = edgeChecker.sdecInternalToFalse(ps1, ta);
			if (testRes != null) {
				assert testRes == result || 
						testRes == LBool.UNKNOWN && result == LBool.SAT : 
							"my internal dataflow check failed";
//				if (testRes != result) {
//					edgeChecker.sdecInternalToFalse(ps1, ta);
//				}
			}
			return;
		}
		if (ps1 == ps2) {
			EdgeChecker edgeChecker = new EdgeChecker(this, m_ModifiableGlobals);
			LBool testRes = edgeChecker.sdecInternalSelfloop(ps1, ta);
			if (testRes != null) {
				assert testRes == result : "my internal dataflow check failed";
//				if (testRes != result) {
//					edgeChecker.sdecReturn(ps1, psk, ta, ps2);
//				}
			}
		}
		if (ta.getTransitionFormula().isInfeasible() == Infeasibility.INFEASIBLE) {
			return;
		}
		EdgeChecker edgeChecker = new EdgeChecker(this, m_ModifiableGlobals);
		LBool testRes = edgeChecker.sdecInteral(ps1, ta, ps2);
		if (testRes != null) {
			assert testRes == result : "my internal dataflow check failed";
//			if (testRes != result) {
//				edgeChecker.sdecReturn(ps1, psk, ta, ps2);
//			}
		}
		if (testRes == null && result == LBool.SAT){
			boolean a = 1 == 1;
			boolean stop = true;
		}
	}

	public TermVarsProc computeTermVarsProc(Term term) {
		HashSet<BoogieVar> vars = new HashSet<BoogieVar>();
		Set<String> procs = new HashSet<String>();
		for (TermVariable tv : term.getFreeVars()) {
			BoogieVar bv = m_Smt2Boogie.getBoogieVar(tv);
			vars.add(bv);
			if (bv.getProcedure() != null) {
				procs.add(bv.getProcedure());
			}
		}
		Term closedTerm = computeClosedFormula(term, vars, getScript());
		return new TermVarsProc(term, vars, procs.toArray(new String[0]), closedTerm);
	}
	
//	public static Set<String> computeProcedures(Set<BoogieVar> vars) {
//		Set<String> result = new HashSet<String>();
//		for (BoogieVar bv : vars) {
//			if (bv.getProcedure() != null) {
//				result.add(bv.getProcedure());
//			}
//		}
//		return result;
//	}

	public static Term computeClosedFormula(Term formula,
			Set<BoogieVar> boogieVars, Script script) {
		ArrayList<TermVariable> replacees = new ArrayList<TermVariable>();
		ArrayList<Term> replacers = new ArrayList<Term>();
		for (BoogieVar bv : boogieVars) {
			replacees.add(bv.getTermVariable());
			replacers.add(bv.getDefaultConstant());
		}
		TermVariable[] vars = replacees.toArray(new TermVariable[replacees
				.size()]);
		Term[] values = replacers.toArray(new Term[replacers.size()]);
		Term closedTerm = script.let(vars, values, formula);
		closedTerm = (new FormulaUnLet()).unlet(closedTerm);
		assert closedTerm.getFreeVars().length == 0;
		return closedTerm;
	}

//	public Predicate newPredicate(ProgramPoint pp, Term term,
//			Set<BoogieVar> vars) {
//		Term closedFormula = computeClosedFormula(term, vars, m_Script);
//		// if (varSetMinimalAssured && !varSetIsMinimal(vars, term,
//		// closedFormula)) {
//		// throw new AssertionError("VarSet not minimal");
//		// }
//		Predicate predicate = new Predicate(pp, term, vars, closedFormula);
//		return predicate;
//	}

//	@Deprecated
//	public Predicate newPredicate(ProgramPoint pp, Term term) {
//		Set<BoogieVar> vars = computeVars(term);
//		Predicate predicate = new Predicate(pp, term, vars, null);
//		return predicate;
//	}

	public PredicateWithHistory newPredicateWithHistory(ProgramPoint pp, 
			Term term, String[] procedures, Set<BoogieVar> vars, 
			Term closedFormula,
			Map<Integer, Term> history) {
		PredicateWithHistory pred = new PredicateWithHistory(pp,
				m_SerialNumber++, procedures, term, vars, closedFormula,
				history);
		return pred;
	}
	
	public static boolean isDontCare(IPredicate pred) {
		return pred.getFormula() == SmtManager.m_DontCareTerm;
	}
	
//	public SPredicate newTrueSPredicateWithHistory(ProgramPoint pp) {
//		SPredicate predicate = new PredicateWithHistory(pp, m_SerialNumber++, m_NoProcedure, m_Script.term("true"),
//				new HashSet<BoogieVar>(0), m_Script.term("true"), new HashMap<Integer,Term>());
//		return predicate;
//	}
	
	public DetermninisticNwaPredicate newDetermninisticNwaPredicate(Script script, Term term, String[] procedures, Set<BoogieVar> vars) {
		DetermninisticNwaPredicate dnp = new DetermninisticNwaPredicate(script, m_SerialNumber++, term, procedures, vars);
		return dnp;
	}
	
	
	public SPredicate newSPredicate(ProgramPoint pp, Term term,
			String[] procedures, Set<BoogieVar> vars, Term closedFormula) {
		SPredicate pred = new SPredicate(pp, m_SerialNumber++, procedures,
				term, vars, closedFormula);
		return pred;
	}
	
//	public SPredicate newSPredicate(ProgramPoint pp, String[] procedures, Term term,
//			Set<BoogieVar> vars) {
//		Term closedFormula = computeClosedFormula(term, vars, m_Script);
//		SPredicate predicate = new SPredicate(pp, m_SerialNumber++, procedures, term, vars, closedFormula);
//		return predicate;
//	}
	
	public BasicPredicate newPredicate(Term term, String[] procedures,
			Set<BoogieVar> vars, Term closedTerm) {
		BasicPredicate predicate = new BasicPredicate(m_SerialNumber++,
				procedures, term, vars, closedTerm);
		return predicate;
	}

	public IPredicate newTruePredicate() {
		IPredicate pred = new BasicPredicate(m_SerialNumber++, m_NoProcedure,
				m_Script.term("true"), m_EmptyVars, m_Script.term("true"));
		return pred;
	}
	
	public IPredicate newFalsePredicate() {
		IPredicate pred = new BasicPredicate(m_SerialNumber++, m_NoProcedure,
				m_Script.term("false"), m_EmptyVars, m_Script.term("false"));
		return pred;
	}

	public UnknownState newDontCarePredicate(ProgramPoint pp) {
		UnknownState pred = new UnknownState(pp, m_SerialNumber++);
		return pred;
	}
	
	public DebugPredicate newDebugPredicate(String debugMessage) {
		DebugPredicate pred = new DebugPredicate(debugMessage, m_SerialNumber++);
		return pred;
	}
	
	public ISLPredicate newEmptyStackPredicate() {
		ProgramPoint pp = new ProgramPoint("noCaller", "noCaller", false, 
				null, null, getScript());
//		m_SmtManager.getScript().variable(
//	"emptyStack", m_SmtManager.getScript().sort("Bool"));
		return newSPredicate(pp, m_EmptyStackTerm, m_NoProcedure, m_EmptyVars, m_EmptyStackTerm);
		
	}
	
	public SPredicate newTrueSLPredicate(ProgramPoint pp) {
		SPredicate pred = new SPredicate(pp, m_SerialNumber++, m_NoProcedure, 
				m_Script.term("true"), m_EmptyVars, m_Script.term("true"));
		return pred;
	}
	
	public SPredicate newTrueSLPredicateWithHistory(ProgramPoint pp) {
		SPredicate pred = new PredicateWithHistory(pp, m_SerialNumber++,
				m_NoProcedure, m_Script.term("true"), m_EmptyVars,
				m_Script.term("true"), new HashMap<Integer, Term>());
		return pred;
	}
	
	public HoareAnnotation getNewHoareAnnotation(ProgramPoint pp) {
		return new HoareAnnotation(pp, m_SerialNumber++, this);
	}
	
	public IPredicate newBuchiPredicate(Set<IPredicate> inputPreds) {
		TermVarsProc tvp = and(inputPreds.toArray(new IPredicate[0]));
		BuchiPredicate buchi = new BuchiPredicate(m_SerialNumber++,	tvp.getProcedures(), 
				tvp.getFormula(), tvp.getVars(), tvp.getClosedFormula(), inputPreds);
		return buchi;
	}
	
	public class TermVarsProc {
		private final Term m_Term;
		private final Set<BoogieVar> m_Vars;
		private final String[] m_Procedures;
		private final Term m_ClosedTerm;
		
		public TermVarsProc(Term term, Set<BoogieVar> vars,
				String[] procedures, Term closedTerm) {
			m_Term = term;
			m_Vars = vars;
			m_Procedures = procedures;
			m_ClosedTerm = closedTerm;
		}

		public String[] getProcedures() {
			return m_Procedures;
		}

		public Term getFormula() {
			return m_Term;
		}

		public Term getClosedFormula() {
			return m_ClosedTerm;
		}

		public Set<BoogieVar> getVars() {
			return m_Vars;
		}

	}
	
	
	
	private class AuxilliaryTerm extends Term {
		
		String m_Name;

		private AuxilliaryTerm(String name) {
			super(0);
			m_Name = name;
		}
		
		@Override
		public Sort getSort() {
			throw new UnsupportedOperationException(
					"Auxilliary term has no sort");
		}

		@Override
		public void toStringHelper(ArrayDeque<Object> m_Todo) {
			throw new UnsupportedOperationException(
					"Auxilliary term must not be subterm of other terms");
		}

		@Override
		public TermVariable[] getFreeVars() {
			throw new UnsupportedOperationException(
					"Auxilliary term has no vars");
		}

		@Override
		public Theory getTheory() {
			throw new UnsupportedOperationException(
					"Auxilliary term has no theory");
		}

		@Override
		public String toString() {
			return m_Name;
		}

		@Override
		public String toStringDirect() {
			throw new UnsupportedOperationException(
					"Auxilliary term must not be subterm of other terms");
		}

		@Override
		public int hashCode() {
			throw new UnsupportedOperationException(
					"Auxilliary term must not be contained in any collection");
		}
	}








}
