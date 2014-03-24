package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
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
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.ReasonUnknown;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.logic.simplification.SimplifyDDA;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Term2Expression;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.InterproceduralSequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.HoareAnnotation;
import de.uni_freiburg.informatik.ultimate.util.ScopedHashMap;

public class SmtManager {
	
	private static Logger s_Logger = 
		UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	
	enum Status { IDLE, TRACECHECK, CODEBLOCKCHECK1, 
		CODEBLOCKCHECK2, EDGECHECK };
	
	private Status m_Status = Status.IDLE; 
	
	private final Boogie2SMT m_Boogie2Smt;
	private final Script m_Script;
//	private final Map<String,ASTType> m_GlobalVars;
	private final ModifiableGlobalVariableManager m_ModifiableGlobals;
	private int m_Iteration;
	private int m_satProbNumber;
	
	private ScopedHashMap<String, Term> m_IndexedConstants;
	Set<BoogieVar> m_AssignedVars;

	private int m_TrivialSatQueries = 0;
	private int m_NontrivialSatQueries = 0;

	private int m_TrivialCoverQueries = 0;
	private int m_NontrivialCoverQueries = 0;
	
//	int m_LazyEdgeCheckQueries = 0;
//	int m_TrivialEdgeCheckQueries = 0;
//	int m_NontrivialEdgeCheckQueries = 0;
	
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

	private Set<BoogieVar> m_EmptyVars = Collections.emptySet();
	
	/**
	 * Whenever you do an edge check with the old method (not edge checker),
	 * test if the dataflow checks deliver a compatible result.
	 * Set this only to true if you can guarantee that only an IPredicate whose
	 * formula is true is equivalent to true.
	 */
	private final static boolean m_TestDataflow = false;



	
	
	protected static Term m_DontCareTerm;
	protected static Term m_EmptyStackTerm;
	protected static String[] m_NoProcedure = new String[0];
	
	public SmtManager(Boogie2SMT boogie2smt,
					ModifiableGlobalVariableManager modifiableGlobals) {
		m_DontCareTerm = new AuxilliaryTerm("don't care");
		m_EmptyStackTerm = new AuxilliaryTerm("emptyStack");
		m_Boogie2Smt = boogie2smt;
		m_Script = boogie2smt.getScript();
		m_ModifiableGlobals =  modifiableGlobals;
	}
	
	public boolean isIdle() {
		return getStatus() == Status.IDLE;
	}
	
	
//	public Smt2Boogie getSmt2Boogie() {
//		return m_Smt2Boogie;
//	}
	
	public Boogie2SMT getBoogie2Smt() {
		return m_Boogie2Smt;
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
	
//	public int getTrivialEdgeCheckQueries() {
//		return m_TrivialEdgeCheckQueries;
//	}
//	
//	public int getLazyEdgeCheckQueries() {
//		return m_LazyEdgeCheckQueries;
//	}
//
//	public int getNontrivialEdgeCheckQueries() {
//		return m_NontrivialEdgeCheckQueries;
//	}
	
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
		BoogieVar result = m_Boogie2Smt.getBoogie2SmtSymbolTable().getGlobals().get(bv.getIdentifier());
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
		BoogieVar result = m_Boogie2Smt.getBoogie2SmtSymbolTable().getOldGlobals().get(bv.getIdentifier());
		assert result != null;
		return result;
	}
	
	/**
	 * Returns a predicate which states that old(g)=g for all global variables
	 * g that are modifiable by procedure proc according to 
	 * ModifiableGlobalVariableManager modGlobVarManager.
	 */
	public IPredicate getOldVarsEquality(String proc, 
			ModifiableGlobalVariableManager modGlobVarManager) {
		Set<BoogieVar> vars = new HashSet<BoogieVar>();
		Term term = getScript().term("true");
		for (BoogieVar bv : modGlobVarManager.getGlobalVarsAssignment(proc).getAssignedVars()) {
			vars.add(bv);
			BoogieVar bvOld = getOldVar(bv);
			vars.add(bvOld);
			TermVariable tv = bv.getTermVariable();
			TermVariable tvOld = bvOld.getTermVariable();
			Term equality = getScript().term("=", tv, tvOld);
			term = Util.and(getScript(), term, equality);
		}
		String[] procs = new String[0];
		IPredicate result = newPredicate(term, procs, vars, 
				computeClosedFormula(term, vars, getScript())); 
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
		if (getStatus() != Status.IDLE) {
			throw new AssertionError("SmtManager is busy");
		} else {
			assert m_TraceCheckStartTime == Long.MIN_VALUE;
			m_TraceCheckStartTime = System.nanoTime();
			setStatus(Status.TRACECHECK);
			m_Script.echo(new QuotedObject("starting trace check"));
			m_IndexedConstants = new ScopedHashMap<String, Term>();
			m_Script.push(1);
		}
	}
	
	public void endTraceCheck() {
		if (getStatus() != Status.TRACECHECK) {
			throw new AssertionError("SmtManager is not performing a traceCheck");
		} else {
			m_TraceCheckTime += (System.nanoTime() - m_TraceCheckStartTime);
			m_TraceCheckStartTime = Long.MIN_VALUE;
			m_Script.echo(new QuotedObject("finished trace check"));
			setStatus(Status.IDLE);
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
		return new SimplifyDDA(m_Script).getSimplifiedTerm(term);
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
		assert (getStatus() == Status.IDLE) : "SmtManager is busy";
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
		assert (getStatus() == Status.IDLE) : "SmtManager is busy";
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
		if (m_TestDataflow) {
			testMyInternalDataflowCheck(ps1, ta, ps2, result);
		}
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
		assert (getStatus() == Status.IDLE) : "SmtManager is busy";
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
		
		LBool result = this.checkSatisfiable(f);
		m_IndexedConstants = null;
		m_Script.pop(1);
		if (expectUnsat) {
			assert (result == Script.LBool.UNSAT || result == Script.LBool.UNKNOWN) 
				: "call statement not inductive";
		}
		m_SatCheckTime += (System.nanoTime() - startTime);
		if (m_TestDataflow) {
			testMyCallDataflowCheck(ps1, ta, ps2, result);
		}
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
		assert (getStatus() == Status.IDLE) : "SmtManager is busy";
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
		if (m_TestDataflow) {
			testMyReturnDataflowCheck(ps1,psk,ta,ps2,result);
		}
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
			Sort resultSort = m_Boogie2Smt.getTypeSortTranslator().getSort(var.getIType(), null);
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
			Sort resultSort = m_Boogie2Smt.getTypeSortTranslator().getSort(var.getIType(), null);
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
	
	public TermVariable getFreshTermVariable(String identifier, Sort sort) {
		String name = "fresh_" + identifier + m_FreshVariableCouter++;
		TermVariable result = m_Script.variable(name, sort);
		return result;
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
								assert !assertInductivity || result : "inductivity failed";
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
								assert !assertInductivity || result : "inductivity failed";
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
									assert !assertInductivity || result : "inductivity failed";
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
	
	
	
	private Integer quantifiersContainedInFormula(Term formula, Set<TermVariable> quantifiedVariables) {
		Integer quantifier = null;
		if (formula instanceof ApplicationTerm) {
			Term[] parameters = ((ApplicationTerm) formula).getParameters();
			for (int i = 0; i < parameters.length; i++) {
				quantifier = quantifiersContainedInFormula(parameters[i], quantifiedVariables);
			}
		} else if (formula instanceof QuantifiedFormula) {
			quantifier = ((QuantifiedFormula) formula).getQuantifier();
			Collections.addAll(quantifiedVariables, ((QuantifiedFormula) formula).getVariables());
		}
		return quantifier;
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
	public IPredicate renameGlobalsToOldGlobals(IPredicate ps) {
		if (isDontCare(ps)){
			throw new UnsupportedOperationException("don't cat not expected");
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
		Map<TermVariable, Term> substitutionMapping = new HashMap<TermVariable, Term>();
		for (BoogieVar globalBoogieVar : globalVars) {
			if (!globalBoogieVar.isOldvar()) {
				BoogieVar oldBoogieVar = this.getOldVar(globalBoogieVar);
				varsOfRenamed.add(oldBoogieVar);
				substitutionMapping.put(globalBoogieVar.getTermVariable(), oldBoogieVar.getTermVariable());
			}
		}
		Term renamedFormula = (new Substitution(substitutionMapping, m_Script)).transform(ps.getFormula());
		renamedFormula = simplify(renamedFormula);
		SmtManager.TermVarsProc tvp = this.computeTermVarsProc(renamedFormula);
		IPredicate result = this.newPredicate( renamedFormula,
				tvp.getProcedures(), 
				tvp.getVars(), tvp.getClosedFormula());
		return result;
	}
	
	/**
	 * Compute the irrelevant variables of the given predicate p. 
	 * A variable is irrelevant, if it isn't contained in the given set of relevantVars.
	 */
	private Set<TermVariable> computeIrrelevantVariables(Set<BoogieVar> relevantVars, IPredicate p) {
		Set<TermVariable> result = new HashSet<TermVariable>();
		for (BoogieVar bv : p.getVars()) {
			if (!relevantVars.contains(bv)) {
				result.add(bv.getTermVariable());
			}
		}
		return result;
	}
	
	public IPredicate computeForwardRelevantPredicate(IPredicate sp, Set<BoogieVar> relevantVars) {
		return computeRelevantPredicateHelper(sp, relevantVars,
				Script.EXISTS);
	}
	
	/**
	 * Computes a predicate from the given predicate p, such that all irrelevant variables are quantified.
	 */
	private IPredicate computeRelevantPredicateHelper(IPredicate p,
			Set<BoogieVar> relevantVars,
			int quantifier) {
		Set<TermVariable> irrelevantVars = computeIrrelevantVariables(relevantVars, p);
//		if (irrelevantVars.size() > 0) {
//			Term formula = PartialQuantifierElimination.quantifier(m_Script, quantifier,
//					irrelevantVars.toArray(new TermVariable[0]), p.getFormula(), (Term[][]) null);
//			
//		} else {
//			return p;
//		}
		return constructPredicate(p.getFormula(), quantifier, irrelevantVars);
	}
	
	
	public IPredicate computeBackwardRelevantPredicate(IPredicate wp, Set<BoogieVar> relevantVars) {
		return computeRelevantPredicateHelper(wp, relevantVars, Script.FORALL);
	}
	
	/**
	 * Computes the strongest postcondition of the given predicate p and
	 * the CodeBlock cb.
	 * @param p
	 * @param cb
	 * @return
	 */
	@Deprecated
	public IPredicate strongestPostcondition(IPredicate p, CodeBlock cb) {
		if (cb instanceof Call) {
			throw new UnsupportedOperationException("This method is not responsible for Call-Statemtens.");
		} else if (cb instanceof Return) {
			throw new UnsupportedOperationException("This method is not responsible for Return-Statements.");
		} else if (cb instanceof InterproceduralSequentialComposition) {
			throw new UnsupportedOperationException();
		}
		return strongestPostcondition(p, cb.getTransitionFormula());
	}
	
	/**
	 * Computes the strongest postcondition of the given predicate p and
	 * the TransFormula tf.
	 * TODO: How is the SP computed?
	 */
	public IPredicate strongestPostcondition(IPredicate p, TransFormula tf) {
		// Check if p is false
		if (p.getFormula() == False()) {
			return p;
		}
		
		Set<TermVariable> varsToQuantify = new HashSet<TermVariable>();
		Map<TermVariable, Term> varsToRenameInPred = new HashMap<TermVariable, Term>();
		Map<TermVariable, Term> substitution = new HashMap<TermVariable, Term>();
		Term tf_term = tf.getFormula();		
		
		for (BoogieVar bv : tf.getInVars().keySet()) {
			if (!tf.getOutVars().containsKey(bv) || 
					tf.getOutVars().get(bv) != tf.getInVars().get(bv)) {
				TermVariable freshVar = getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
				varsToRenameInPred.put(bv.getTermVariable(), freshVar);
				substitution.put(tf.getInVars().get(bv), freshVar);
				varsToQuantify.add(freshVar);
			}
		}
		
		Term TFInvarsRenamed = new Substitution(substitution, m_Script).transform(tf_term);
		
		substitution.clear();
		for (BoogieVar bv : tf.getOutVars().keySet()) {
			substitution.put(tf.getOutVars().get(bv), bv.getTermVariable());
			if (tf.getInVars().isEmpty() && tf.getFormula() == True()) {
				varsToQuantify.add(bv.getTermVariable());
			} else if (!tf.getInVars().containsKey(bv)) {
				TermVariable freshVar = getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
				varsToRenameInPred.put(bv.getTermVariable(), freshVar);
				varsToQuantify.add(freshVar);
			}
		}
		
		Term TFInVarsOutVarsRenamed = new Substitution(substitution, m_Script).transform(TFInvarsRenamed);
		
		Term predicateRenamed = new Substitution(varsToRenameInPred, m_Script).transform(p.getFormula());
		
		// Remove the superflous quantified variables. These are variables, which don't occur neither in
		// the predicate nor in the Transformula
		Set<TermVariable> freeVarsOfPredicate = new HashSet<TermVariable>();
		Set<TermVariable> freeVarsOfTF = new HashSet<TermVariable>();
		Collections.addAll(freeVarsOfPredicate, predicateRenamed.getFreeVars());
		Collections.addAll(freeVarsOfTF, TFInVarsOutVarsRenamed.getFreeVars());
		Set<TermVariable> superflousQuantifiedVars = new HashSet<TermVariable>();
		for (TermVariable tv : varsToQuantify) {
			if (!freeVarsOfPredicate.contains(tv) && !freeVarsOfTF.contains(tv)) {
				superflousQuantifiedVars.add(tv);
			}
		}
		varsToQuantify.removeAll(superflousQuantifiedVars);
		
		Term result = Util.and(m_Script, TFInVarsOutVarsRenamed, predicateRenamed);
		
		// Add aux vars to varsToQuantify
		varsToQuantify.addAll(tf.getAuxVars());
		
//		if (varsToQuantify.size() > 0) {
//			result = PartialQuantifierElimination.quantifier(m_Script, Script.EXISTS,
//					varsToQuantify.toArray(new TermVariable[varsToQuantify.size()]), result, (Term[][]) null);
//		}
		return constructPredicate(result, Script.EXISTS, varsToQuantify);
	}
	
	/**
	 * Compute the strongest postcondition for a predicate and a call statement.
	 * Call statements must be treated in a special way.
	 */
	@Deprecated
	public IPredicate strongestPostcondition(IPredicate p, Call call, boolean isPendingCall) {
		
		return strongestPostcondition(p, call.getTransitionFormula(),
				m_ModifiableGlobals.getGlobalVarsAssignment(call.getCallStatement().getMethodName()), 
				m_ModifiableGlobals.getOldVarsAssignment(call.getCallStatement().getMethodName()),
				isPendingCall);
	}

	/**
	 * Compute the strongest postcondition for a predicate and a call statement.
	 * Call statements must be treated in a special way.
	 * TODO: How do we compute the SP of a Call Statement?
	 */
	public IPredicate strongestPostcondition(IPredicate p, TransFormula localVarAssignments, 
			TransFormula globalVarAssignments,
			TransFormula oldVarAssignments,
			boolean isPendingCall) {

		// VarsToQuantify contains the local Vars and  the global vars of the calling proc, for a non-pending call.
		Set<TermVariable> varsToQuantifyNonPendingCall = new HashSet<TermVariable>();
		// Variables, which should be quantified if we have a pending call.
		Set<TermVariable> varsToQuantifyPendingCall = new HashSet<TermVariable>();
		// We rename oldvars of non-modifiable global variables to freshvars and quantify them.
		Set<TermVariable> varsToQuantifyNonModOldVars = new HashSet<TermVariable>();
		// In Pred we rename oldvars of non-modifiable global variables to freshvars.
		Map<TermVariable, Term> varsToRenameInPredInBoth = new HashMap<TermVariable, Term>();
		// Union Set of auxvars occurring in each transformula
		Set<TermVariable> allAuxVars = new HashSet<TermVariable>();
		allAuxVars.addAll(localVarAssignments.getAuxVars());
		allAuxVars.addAll(globalVarAssignments.getAuxVars());
		allAuxVars.addAll(oldVarAssignments.getAuxVars());
		
		Map<TermVariable, Term> varsToRenameInPredPendingCall = new HashMap<TermVariable, Term>();
		Map<TermVariable, Term> varsToRenameInPredNonPendingCall = new HashMap<TermVariable, Term>();
		// 1.1 Rename the invars in global variable assignments.Invars are {old(g) --> old(g)_23}
		Map<TermVariable, Term> substitution = new HashMap<TermVariable, Term>();
//		for (BoogieVar bv : globalVarAssignments.getInVars().keySet()) {
//			TermVariable freshVar = getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
//			substitution.put(globalVarAssignments.getInVars().get(bv), bv.getTermVariable());
//			varsToRenameInPredPendingCall.put(bv.getTermVariable(), freshVar);
//			varsToRenameInPredNonPendingCall.put(bv.getTermVariable(), freshVar);
//			varsToQuantifyNonPendingCall.add(freshVar);
//			varsToQuantifyPendingCall.add(freshVar);
//		}
//		Term globalVarsInvarsRenamed = new Substitution(substitution, m_Script).transform(globalVarAssignments.getFormula());
		Term globalVarsInvarsRenamed = substituteToRepresantantsAndAddToQuantify(globalVarAssignments.getInVars(),
				globalVarAssignments.getFormula(), varsToRenameInPredNonPendingCall, varsToQuantifyNonPendingCall);
		varsToQuantifyPendingCall.addAll(varsToQuantifyNonPendingCall);
		varsToRenameInPredPendingCall.putAll(varsToRenameInPredNonPendingCall);
		
		// 1.2 Rename the outvars in global variable assignments.
//		substitution.clear();
//		for (BoogieVar bv : globalVarAssignments.getOutVars().keySet()) {
//			substitution.put(globalVarAssignments.getOutVars().get(bv), bv.getTermVariable());
//			TermVariable freshVar = getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
//			varsToQuantifyNonPendingCall.add(freshVar);
//			varsToRenameInPredNonPendingCall.put(bv.getTermVariable(), freshVar);
//		}
//		
//		Term globalVarsInVarsRenamedOutVarsRenamed = new Substitution(substitution, m_Script).transform(globalVarsInvarsRenamed);
		Term globalVarsInVarsRenamedOutVarsRenamed = substituteToRepresantantsAndAddToQuantify(globalVarAssignments.getOutVars(),
				globalVarsInvarsRenamed, varsToRenameInPredNonPendingCall, varsToQuantifyNonPendingCall);
		substitution.clear();
		if (globalVarAssignments.getFormula() == newTruePredicate().getFormula()) {
			for (BoogieVar bv : oldVarAssignments.getInVars().keySet()) {
				substitution.put(oldVarAssignments.getInVars().get(bv), bv.getTermVariable());
				TermVariable freshVar = getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
				varsToQuantifyNonPendingCall.add(freshVar);
				varsToRenameInPredNonPendingCall.put(bv.getTermVariable(), freshVar);
			}
			globalVarsInvarsRenamed = new Substitution(substitution, m_Script).transform(oldVarAssignments.getFormula());
			substitution.clear();
			
			for (BoogieVar bv : oldVarAssignments.getOutVars().keySet()) {
				TermVariable freshVar = getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
				substitution.put(oldVarAssignments.getOutVars().get(bv), bv.getTermVariable());
				varsToQuantifyPendingCall.add(freshVar);
				varsToRenameInPredPendingCall.put(bv.getTermVariable(), freshVar);
				varsToRenameInPredNonPendingCall.put(bv.getTermVariable(), freshVar);
				varsToQuantifyNonPendingCall.add(freshVar);
			}
			globalVarsInVarsRenamedOutVarsRenamed = new Substitution(substitution, m_Script).transform(globalVarsInvarsRenamed);
		}
		// Collect the local and the non-modifiable global variables of the calling proc.
		for (BoogieVar bv : p.getVars()) {
			// Procedure is null, if it is a global variable
			if (bv.getProcedure() != null) {
				varsToQuantifyNonPendingCall.add(bv.getTermVariable());
				// Ensure that variable doesn't occur in call
				if (!localVarAssignments.getInVars().containsKey(bv)
						&& !localVarAssignments.getOutVars().containsKey(bv)) {
					TermVariable freshVar = getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
					varsToRenameInPredPendingCall.put(bv.getTermVariable(), freshVar);
					varsToQuantifyPendingCall.add(freshVar);
					varsToQuantifyNonPendingCall.add(bv.getTermVariable());
				}
			}
			
			if (bv.isGlobal() &&
					!globalVarAssignments.getInVars().containsKey(bv) && 
					!globalVarAssignments.getOutVars().containsKey(bv)) {
				if (bv.isOldvar()) {
					TermVariable freshVar = getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
					varsToRenameInPredInBoth.put(bv.getTermVariable(), freshVar);
					varsToQuantifyNonModOldVars.add(freshVar);
				}
			}
		}
		substitution.clear();
		
//		 2.1 Rename the invars of the term of Call-Statement.
		for (BoogieVar bv : localVarAssignments.getInVars().keySet()) {
			
			if (globalVarAssignments.getOutVars().containsKey(bv)) {
				// If it is a global var, then we substitute it through its oldvar
				substitution.put(localVarAssignments.getInVars().get(bv), getOldVar(bv).getTermVariable());
			} else {
				TermVariable freshVar = getFreshTermVariable(bv.getIdentifier(),
						bv.getTermVariable().getSort());
				substitution.put(localVarAssignments.getInVars().get(bv), freshVar);
				varsToRenameInPredPendingCall.put(bv.getTermVariable(), freshVar);
				varsToQuantifyPendingCall.add(freshVar);
				varsToQuantifyNonPendingCall.add(bv.getTermVariable());
			}
		}
		Term call_Term_InVarsRenamed = new Substitution(substitution, m_Script).transform(localVarAssignments.getFormula());
		substitution.clear();
		
		Term predNonModOldVarsRenamed = new Substitution(varsToRenameInPredInBoth, m_Script).transform(p.getFormula());


		if (isPendingCall) {
			// 2.2 Rename the outvars of the term of the Call-Statement.
			for (BoogieVar bv : localVarAssignments.getOutVars().keySet()) {
				substitution.put(localVarAssignments.getOutVars().get(bv), bv.getTermVariable());
			}
			Term callTermInvarsRenamedOutVarsRenamed = new Substitution(substitution, m_Script).transform(call_Term_InVarsRenamed);
			// Rename the invars of CAll, local Vars and old version of global variables.
			Term predRenamed = new Substitution(varsToRenameInPredPendingCall, m_Script).transform(predNonModOldVarsRenamed);
			Term predANDCallANDGlobalVars = Util.and(m_Script, predRenamed, callTermInvarsRenamedOutVarsRenamed,
					globalVarsInVarsRenamedOutVarsRenamed);
			varsToQuantifyPendingCall.addAll(varsToQuantifyNonModOldVars);
			varsToQuantifyPendingCall.addAll(allAuxVars);
//			Term result = PartialQuantifierElimination.quantifier(m_Script,
//					Script.EXISTS,
//					varsToQuantifyPendingCall.toArray(new TermVariable[varsToQuantifyPendingCall.size()]),
//					predANDCallANDGlobalVars, (Term[][])null);
			
			return constructPredicate(predANDCallANDGlobalVars, Script.EXISTS, varsToQuantifyPendingCall);
		} else {
			Term predRenamed = new Substitution(varsToRenameInPredNonPendingCall, m_Script).transform(predNonModOldVarsRenamed);
			varsToQuantifyNonPendingCall.addAll(varsToQuantifyNonModOldVars);
			varsToQuantifyNonPendingCall.addAll(allAuxVars);
//			Term result = PartialQuantifierElimination.quantifier(m_Script, 
//					Script.EXISTS,
//					varsToQuantifyNonPendingCall.toArray(new TermVariable[varsToQuantifyNonPendingCall.size()]),
//					Util.and(m_Script, predRenamed, globalVarsInVarsRenamedOutVarsRenamed),
//					(Term[][])null);
			return constructPredicate(Util.and(m_Script, predRenamed, globalVarsInVarsRenamedOutVarsRenamed), Script.EXISTS, varsToQuantifyNonPendingCall);
		}
	}
	
	
	
	/**
	 * Compute strongest postcondition for a return statement, where calleePred
	 * is the predicate that holds in the called procedure before the return 
	 * statement and callerPred is the predicate that held in the calling 
	 * procedure before the corresponding call. 
	 */
	@Deprecated
	public IPredicate strongestPostcondition(IPredicate calleePred, 
											IPredicate callerPred, Return ret) {

		return strongestPostcondition(calleePred, callerPred, ret.getTransitionFormula(),
				ret.getCorrespondingCall().getTransitionFormula(),
				m_ModifiableGlobals.getGlobalVarsAssignment(
						ret.getCorrespondingCall().getCallStatement().getMethodName()));
	}


	/**
	 * Compute strongest postcondition for a return statement, where calleePred
	 * is the predicate that holds in the called procedure before the return 
	 * statement and callerPred is the predicate that held in the calling 
	 * procedure before the corresponding call.
	 * TODO: How is it computed? 
	 */
	public IPredicate strongestPostcondition(IPredicate calleePred, 
			IPredicate callerPred, TransFormula ret_TF, TransFormula callTF,
			TransFormula globalVarsAssignment) {
		// VarsToQuantify contains local vars of called procedure, and it may contain
		// some invars, if it was a recursive call, i.e. callingProc = calledProc.
		Set<TermVariable> varsToQuantifyOverAll = new HashSet<TermVariable>();
		Set<TermVariable> varsToQuantifyInCalleePred = new HashSet<TermVariable>();
		Set<TermVariable> varsToQuantifyInCallerPredAndCallTF = new HashSet<TermVariable>();
		Map<TermVariable, Term> varsToRenameInCalleePred = new HashMap<TermVariable, Term>();
		Map<TermVariable, Term> varsToRenameInCallerPred = new HashMap<TermVariable, Term>();
		Map<TermVariable, Term> outVarsToRenameInCallTF = new HashMap<TermVariable, Term>();
		Map<TermVariable, Term> inVarsToRenameInReturnTF = new HashMap<TermVariable, Term>();
		Set<TermVariable> allAuxVars = new HashSet<TermVariable>();
		allAuxVars.addAll(ret_TF.getAuxVars());
		allAuxVars.addAll(callTF.getAuxVars());
		allAuxVars.addAll(globalVarsAssignment.getAuxVars());
		
		
		// Substitute oldvars of modifiable global vars by fresh vars in calleePred
		// and substitue their non-oldvar by the same fresh var in callerPred.
		for (BoogieVar bv : globalVarsAssignment.getInVars().keySet()) {
			TermVariable freshVar = getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
			varsToRenameInCalleePred.put(bv.getTermVariable(), freshVar);
			varsToRenameInCallerPred.put(getNonOldVar(bv).getTermVariable(), freshVar);
			varsToQuantifyOverAll.add(freshVar);
		}
		// Note: We have to take also the outvars into account, because sometimes it may be the case,
		// that a invar does not occur in the outvars.
		for (BoogieVar bv : globalVarsAssignment.getOutVars().keySet()) {
			// We have only to check the vars, that are not contained in the map varsToRenameInCallerPred,
			// because otherwise it is already treated in the case above.
			if (!varsToRenameInCallerPred.containsKey(bv.getTermVariable())) {
				TermVariable freshVar = getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
				varsToRenameInCallerPred.put(bv.getTermVariable(), freshVar);
				varsToQuantifyOverAll.add(freshVar);
			}
			
		}
		
		
		// Collect the local variables of called proc
		for (BoogieVar bv : calleePred.getVars()) {
			if (bv.isGlobal() || bv.isOldvar()) {
				continue;
			}
			if (ret_TF.getOutVars().containsKey(bv)) {
				TermVariable freshVar = getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
				varsToRenameInCalleePred.put(bv.getTermVariable(), freshVar);
				varsToQuantifyOverAll.add(freshVar);
				if (ret_TF.getInVars().containsKey(bv)) {
					inVarsToRenameInReturnTF.put(ret_TF.getInVars().get(bv), freshVar);
				}
				if (callTF.getOutVars().containsKey(bv)) {
					outVarsToRenameInCallTF.put(callTF.getOutVars().get(bv), freshVar);
				}
			} else if (callTF.getInVars().containsKey(bv)) {
				TermVariable freshVar = getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
				varsToRenameInCalleePred.put(bv.getTermVariable(), freshVar);
				varsToQuantifyOverAll.add(freshVar);
				if (ret_TF.getInVars().containsKey(bv)) {
					inVarsToRenameInReturnTF.put(ret_TF.getInVars().get(bv), freshVar);
				}
				if (callTF.getOutVars().containsKey(bv)) {
					outVarsToRenameInCallTF.put(callTF.getOutVars().get(bv), freshVar);
				}
			} else if (callerPred.getVars().contains(bv)) {
				TermVariable freshVar = getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
				varsToRenameInCalleePred.put(bv.getTermVariable(), freshVar);
				varsToQuantifyOverAll.add(freshVar);
				if (ret_TF.getInVars().containsKey(bv)) {
					inVarsToRenameInReturnTF.put(ret_TF.getInVars().get(bv), freshVar);
				}
				if (callTF.getOutVars().containsKey(bv)) {
					outVarsToRenameInCallTF.put(callTF.getOutVars().get(bv), freshVar);
				}
			} else if (!ret_TF.getInVars().containsKey(bv) && 
					!callTF.getOutVars().containsKey(bv)) {
				if (!m_ModifiableGlobals.getGlobals().containsKey(bv.getIdentifier())) {
					varsToQuantifyInCalleePred.add(bv.getTermVariable());
				}
			}
			
		}
		
		
		// 1.1 We doesn't rename the invars of the TransFormula Return,
		// because we quantify them out.
		Map<TermVariable, Term> substitution = new HashMap<TermVariable, Term>();
		for (BoogieVar bv : ret_TF.getInVars().keySet()) {
			if (!inVarsToRenameInReturnTF.containsKey(ret_TF.getInVars().get(bv))) {
				TermVariable substitutor = ret_TF.getInVars().get(bv);
				varsToRenameInCalleePred.put(bv.getTermVariable(), substitutor);
				varsToQuantifyOverAll.add(substitutor);
			}
		}
		//1.2 Rename outvars of Return statement
		for (BoogieVar bv : ret_TF.getOutVars().keySet()) {
			if (calleePred.getVars().contains(bv)) {
				if (!varsToRenameInCalleePred.containsKey(bv.getTermVariable())) {
					TermVariable freshVar = getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
					varsToRenameInCalleePred.put(bv.getTermVariable(), freshVar);
					varsToQuantifyOverAll.add(freshVar);
				} 
			}
			substitution.put(ret_TF.getOutVars().get(bv), bv.getTermVariable());
			varsToQuantifyInCallerPredAndCallTF.add(bv.getTermVariable());
		}
		Term retTermRenamed = new Substitution(inVarsToRenameInReturnTF, m_Script).transform(ret_TF.getFormula());
		retTermRenamed = new Substitution(substitution, m_Script).transform(retTermRenamed);
		// 2.1 Rename invars of TransFormula of corresponding Call statement
		substitution.clear();
		for (BoogieVar bv : callTF.getInVars().keySet()) {
			if (ret_TF.getOutVars().containsKey(bv)) {
				TermVariable freshVar = getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
				substitution.put(callTF.getInVars().get(bv), freshVar);
				varsToRenameInCallerPred.put(bv.getTermVariable(), freshVar);
				varsToQuantifyInCallerPredAndCallTF.add(freshVar);
			} else if (globalVarsAssignment.getOutVars().containsKey(bv)) {
				Term freshVar = varsToRenameInCallerPred.get(bv.getTermVariable());
				assert freshVar != null : "added null to substitution mapping";
				substitution.put(callTF.getInVars().get(bv), freshVar);
			} else {
				substitution.put(callTF.getInVars().get(bv), bv.getTermVariable());
			}
		}
		Term callTermRenamed = new Substitution(outVarsToRenameInCallTF, m_Script).transform(callTF.getFormula());
		callTermRenamed = new Substitution(substitution, m_Script).transform(callTermRenamed);
		// 2.2 We doesn't rename the outvars, because the outvars are the localvars
		// of the called procedure, therefore we want to quantify them out.
		for (BoogieVar bv : callTF.getOutVars().keySet()) {
			if (!outVarsToRenameInCallTF.containsKey(callTF.getOutVars().get(bv))) {
				TermVariable substitutor = callTF.getOutVars().get(bv);
				varsToRenameInCalleePred.put(bv.getTermVariable(), substitutor);
				varsToQuantifyOverAll.add(substitutor);
			}
		}

		
		// 3. Rename the vars in calleePred, which occur as an outvar in the TransFormula of Return Statement, or
		// which occur as an invar in the TransFormula of the corresponding Call statement.
		// This substitution is only necessary, if we have a recursive call.
		Term calleePredVarsRenamed = new Substitution(varsToRenameInCalleePred, m_Script).transform(calleePred.getFormula());


		
		// 5. Substitute oldvars through fresh variables in calleePredicate.
		Term calleePredVarsRenamedOldVarsToFreshVars = new Substitution(varsToRenameInCalleePred, m_Script).transform(calleePredVarsRenamed);
		

		// 6. Substitute the global variables in callerPred through the fresh Vars computed in (4).
		Term callerPredVarsRenamedToFreshVars = new Substitution(varsToRenameInCallerPred, m_Script).transform(callerPred.getFormula());
		
		// 1. CalleePredRenamed and loc vars quantified
		Term calleePredRenamedQuantified = PartialQuantifierElimination.quantifier(m_Script,
				Script.EXISTS,
				varsToQuantifyInCalleePred.toArray(new TermVariable[varsToQuantifyInCalleePred.size()]),
				calleePredVarsRenamedOldVarsToFreshVars,(Term[][])null);
		// 2. CallTF and callerPred
		Term calleRPredANDCallTFRenamedQuantified = PartialQuantifierElimination.quantifier(m_Script,
				Script.EXISTS,
				varsToQuantifyInCallerPredAndCallTF.toArray(new TermVariable[varsToQuantifyInCallerPredAndCallTF.size()]),
				Util.and(m_Script, callerPredVarsRenamedToFreshVars, callTermRenamed),(Term[][])null);
		// 3. Result
		varsToQuantifyOverAll.addAll(allAuxVars);
//		Term result = PartialQuantifierElimination.quantifier(m_Script,
//				Script.EXISTS,
//				varsToQuantifyOverAll.toArray(new TermVariable[varsToQuantifyOverAll.size()]),
//				Util.and(m_Script, calleePredRenamedQuantified, retTermRenamed,
//						calleRPredANDCallTFRenamedQuantified),
//				(Term[][])null);
		
		return constructPredicate(Util.and(m_Script, calleePredRenamedQuantified, retTermRenamed,
				calleRPredANDCallTFRenamedQuantified), Script.EXISTS, varsToQuantifyOverAll);
	}

	/**
	 * Constructs a predicate from the given term. If the given term is quantifier-free, a BasicPredicate will be constructed, otherwise
	 * it constructs a BasicPredicateExplicitQuantifier.
	 * @param quantifier TODO
	 */
	private IPredicate constructPredicate(Term term, int quantifier, Set<TermVariable> quantifiedVariables) {
		if (quantifiedVariables == null || quantifiedVariables.isEmpty()) {
			// Compute the set of BoogieVars, the procedures and the term
			TermVarsProc tvp = computeTermVarsProc(term);
			// Compute a closed formula version of term.
			Term closed_formula = SmtManager.computeClosedFormula(term, tvp.getVars(), m_Script);
			return newPredicate(term, tvp.getProcedures(), tvp.getVars(), closed_formula);
		} else {
			Term result = PartialQuantifierElimination.quantifier(m_Script, quantifier,
					quantifiedVariables.toArray(new TermVariable[quantifiedVariables.size()]),
					term, (Term[][]) null);
			// Compute the set of BoogieVars, the procedures and the term
			TermVarsProc tvp = computeTermVarsProc(result);
			// Compute a closed formula version of term.
			Term closed_formula = SmtManager.computeClosedFormula(result, tvp.getVars(), m_Script);
			return new BasicPredicateExplicitQuantifier(m_SerialNumber++, tvp.getProcedures(), 
					result, tvp.getVars(), closed_formula, quantifier, quantifiedVariables);
		}
	}

	/**
	 * Computes the weakest precondition of the given predicate p and the
	 * CodeBlock cb. 
	 */
	@Deprecated
	public IPredicate weakestPrecondition(IPredicate p, CodeBlock cb) {
		if (cb instanceof Call) {
			throw new UnsupportedOperationException("This method is not responsible for Call.");
		} else if (cb instanceof Return) {
			throw new UnsupportedOperationException("This method is not responsible for Return.");
		} else if (cb instanceof InterproceduralSequentialComposition) {
			throw new UnsupportedOperationException("This method is not responsible for InterproceduralSequentialComposition.");
		}
		return weakestPrecondition(p, cb.getTransitionFormula());
	}
	
	public IPredicate weakestPrecondition(IPredicate p, TransFormula tf) {
		// If the given predicate p is true, then return true, since wp(true, st) = true for every statement st.
		if (p.getFormula() == True()) {
			return p;
		}
		Set<TermVariable> varsToQuantify = new HashSet<TermVariable>();
		Map<TermVariable, Term> varsToRenameInPred = new HashMap<TermVariable, Term>();
		Term tf_term = tf.getFormula();
		Map<TermVariable, Term> substitution = new HashMap<TermVariable, Term>();
		// 1 Rename the invars of the TransFormula of the given CodeBlock cb into TermVariables
//		for (BoogieVar bv : tf.getInVars().keySet()) {
//			substitution.put(tf.getInVars().get(bv), bv.getTermVariable());
//		}
//		Term TFInVarsRenamed = new Substitution(substitution, m_Script).transform(tf_term);
		
		Term TFInVarsRenamed = substituteToRepresantantsAndAddToQuantify(tf.getInVars(), tf_term, null, null);
		
		substitution.clear();
		// 2 Rename the outvars of the TransFormula of the given CodeBlock cb into TermVariables
		for (BoogieVar bv : tf.getOutVars().keySet()) {
			if (tf.getAssignedVars().contains(bv)) {
				TermVariable freshVar = getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
				varsToRenameInPred.put(bv.getTermVariable(), freshVar);
				substitution.put(tf.getOutVars().get(bv), freshVar);
				varsToQuantify.add(freshVar);
			}
		}
		Term TFInVarsOutVarsRenamed = new Substitution(substitution, m_Script).transform(TFInVarsRenamed);
		
		// 3. Rename the necessary vars in the given predicate
		Term predicateRenamed = new Substitution(varsToRenameInPred, m_Script).transform(p.getFormula());
		
		// Remove the superflous quantified variables. These are variables, which don't occur neither in
		// the predicate nor in the transformula
		Set<TermVariable> freeVarsOfPredicate = new HashSet<TermVariable>();
		Set<TermVariable> freeVarsOfTF = new HashSet<TermVariable>();
		Collections.addAll(freeVarsOfPredicate, predicateRenamed.getFreeVars());
		Collections.addAll(freeVarsOfTF, TFInVarsOutVarsRenamed.getFreeVars());
		Set<TermVariable> superflousQuantifiedVars = new HashSet<TermVariable>();
		for (TermVariable tv : varsToQuantify) {
			if (!freeVarsOfPredicate.contains(tv) && !freeVarsOfTF.contains(tv)) {
				superflousQuantifiedVars.add(tv);
			}
		}
		varsToQuantify.removeAll(superflousQuantifiedVars);
		
		Term result = Util.or(m_Script, Util.not(m_Script, TFInVarsOutVarsRenamed), predicateRenamed);
		// Add aux-vars to quantified vars
		varsToQuantify.addAll(tf.getAuxVars());
//		if (varsToQuantify.size() > 0) {
//			result = PartialQuantifierElimination.quantifier(m_Script, Script.FORALL,
//					varsToQuantify.toArray(new TermVariable[varsToQuantify.size()]),
//					result, (Term[][]) null);
//		} 
		return constructPredicate(result, Script.FORALL, varsToQuantify);
	}
	
	/**
	 * Compute the weakest precondition for a call statement, where the returneePred
	 * is the predicate that holds in the returned procedure before the call statement
	 * and returnerPred is the predicate that held in the returning procedure before the
	 * corresponding  return.
	 */
	@Deprecated
	public IPredicate weakestPrecondition(IPredicate calleePred, 
						IPredicate returnerPred, Call call, Return ret,
						TransFormula globalVarsAssignments,
						TransFormula oldVarsAssignments,
						boolean isPendingCall) {
		return weakestPrecondition(calleePred, call.getTransitionFormula(), globalVarsAssignments, oldVarsAssignments,
				isPendingCall);
	}
	
	/**
	 * Responsible for computing WP of a Call statement.
	 * 
	 */
	public IPredicate weakestPrecondition(IPredicate calleePred, 
			TransFormula call_TF, 
			TransFormula globalVarsAssignments,
			TransFormula oldVarsAssignments,
			boolean isPendingCall) {
		
		if (isPendingCall) {
			Map<TermVariable, Term> varsToRenameInCalleePred = new HashMap<TermVariable, Term>();
			Set<TermVariable> varsToQuantify = new HashSet<TermVariable>();
			Map<TermVariable, Term> substitution = new HashMap<TermVariable, Term>();
			
			// 1. Rename oldvars of global vars to fresh vars
			for (BoogieVar bv : globalVarsAssignments.getInVars().keySet()) {
				TermVariable freshVar = getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
				substitution.put(globalVarsAssignments.getInVars().get(bv), freshVar);
				varsToRenameInCalleePred.put(bv.getTermVariable(), freshVar);
				varsToQuantify.add(freshVar);
			}
			Term globalVarsInVarsRenamed = new Substitution(substitution, m_Script).transform(globalVarsAssignments.getFormula());
			
			substitution.clear();
			// 2. Rename global vars to fresh vars
			for (BoogieVar bv : globalVarsAssignments.getOutVars().keySet()) {
//				TermVariable freshVar = getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
				substitution.put(globalVarsAssignments.getOutVars().get(bv), bv.getTermVariable());
//				varsToRenameInCalleePred.put(bv.getTermVariable(), freshVar);
//				varsToQuantify.add(freshVar);
			}
			Term globalVarsInVarsOutVarsRenamed  = new Substitution(substitution, m_Script).transform(globalVarsInVarsRenamed);
			substitution.clear();
			if (globalVarsAssignments.getFormula() == newTruePredicate().getFormula()) {
				for (BoogieVar bv : oldVarsAssignments.getInVars().keySet()) {
//					TermVariable freshVar = getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
					substitution.put(oldVarsAssignments.getInVars().get(bv), bv.getTermVariable());
//					varsToRenameInCalleePred.put(bv.getTermVariable(), freshVar);
//					varsToQuantify.add(freshVar);
				}
				globalVarsInVarsRenamed = new Substitution(substitution, m_Script).transform(oldVarsAssignments.getFormula());
				substitution.clear();
				for (BoogieVar bv : oldVarsAssignments.getOutVars().keySet()) {
					TermVariable freshVar = getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
					substitution.put(oldVarsAssignments.getOutVars().get(bv), freshVar);
					varsToRenameInCalleePred.put(bv.getTermVariable(), freshVar);
					varsToQuantify.add(freshVar);
				}
				globalVarsInVarsOutVarsRenamed  = new Substitution(substitution, m_Script).transform(globalVarsInVarsRenamed);
			}
			
			substitution.clear();
			// 3. Rename invars of Call to its correspondent termvariables
			for (BoogieVar bv : call_TF.getInVars().keySet()) {
				substitution.put(call_TF.getInVars().get(bv), bv.getTermVariable());
			}
			Term callTFInVarsRenamed = new Substitution(substitution, m_Script).transform(call_TF.getFormula());
			// 4. Rename outvars of Call to fresh vars
			substitution.clear();
			for (BoogieVar bv : call_TF.getOutVars().keySet()) {
				TermVariable freshVar = getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
				substitution.put(call_TF.getOutVars().get(bv), freshVar);
				varsToRenameInCalleePred.put(bv.getTermVariable(), freshVar);
				varsToQuantify.add(freshVar);
			}
			Term callTFInVarsOutVarsRenamed = new Substitution(substitution, m_Script).transform(callTFInVarsRenamed);
			
			Term calleePredRenamed = new Substitution(varsToRenameInCalleePred, m_Script).transform(calleePred.getFormula());

			Term result = Util.or(m_Script, 
					Util.not(m_Script, 
							Util.and(m_Script, callTFInVarsOutVarsRenamed,
							globalVarsInVarsOutVarsRenamed)),
					calleePredRenamed);
			varsToQuantify.addAll(call_TF.getAuxVars());
//			if (varsToQuantify.size() > 0) {
//				result = PartialQuantifierElimination.quantifier(m_Script, Script.FORALL,
//						varsToQuantify.toArray(new TermVariable[varsToQuantify.size()]),
//						result, (Term[][])null);
//			}
			return constructPredicate(result, Script.FORALL, varsToQuantify);
		} else {
			throw new UnsupportedOperationException("WP for non-pending Call is not implemented yet!");
		}
	}
	
	@Deprecated
	public IPredicate weakestPrecondition(IPredicate returnerPred, IPredicate callerPred, Return ret) {
		return weakestPrecondition(returnerPred, callerPred, ret.getTransitionFormula(), ret.getCorrespondingCall().getTransitionFormula(),
				m_ModifiableGlobals.getGlobalVarsAssignment(ret.getCorrespondingCall().getCallStatement().getMethodName()),
				m_ModifiableGlobals.getModifiedBoogieVars(ret.getCorrespondingCall().getCallStatement().getMethodName()));
		
	}
	
	
	
	/**
	 * Computes weakest precondition of a Return statement.
	 * TODO: Document how the WP of a Return statement is computed!
	 * 
	 */
	public IPredicate weakestPrecondition(IPredicate returnerPred, IPredicate callerPred, 
			TransFormula returnTF,
			TransFormula callTF,
			TransFormula globalVarsAssignments,
			Set<BoogieVar> modifiableGlobals) {
		
		Map<TermVariable, Term> varsToRenameInCallerAndReturnPred = new HashMap<TermVariable, Term>();
		Map<TermVariable, Term> varsToRenameInReturnPred = new HashMap<TermVariable, Term>();
		Map<TermVariable, Term> varsToRenameInCallerPred = new HashMap<TermVariable, Term>();
		Set<TermVariable> varsToQuantify = new HashSet<TermVariable>();
		// Appropriately rename global var assignments
		// 1.1 Rename the invars in global variable assignments (old_vars).
		Term globalVarsRenamed = substituteToRepresantantsAndAddToQuantify(
				globalVarsAssignments.getInVars(),globalVarsAssignments.getFormula(), varsToRenameInCallerAndReturnPred,
				varsToQuantify);
		// 1.2 Rename the outvars in global variable assignments.
		globalVarsRenamed = substituteToFreshVarsAndAddToQuantify(globalVarsAssignments.getOutVars(),
				globalVarsRenamed,
				varsToRenameInCallerPred, varsToQuantify);
		// 2.1 Rename the invars of Return-Statement.
		Map<TermVariable, Term> substitution = new HashMap<TermVariable, Term>();
		for (BoogieVar bv : returnTF.getInVars().keySet()) {
			TermVariable freshVar = getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
			// TODO: Document this step
			if (returnTF.getOutVars().containsKey(bv)) {
				varsToRenameInCallerPred.put(bv.getTermVariable(), freshVar);
			} else {
				varsToRenameInCallerAndReturnPred.put(bv.getTermVariable(), freshVar);
			}
			varsToQuantify.add(freshVar);
			substitution.put(returnTF.getInVars().get(bv), bv.getTermVariable());
		}
		Term returnTermRenamed = new Substitution(substitution, m_Script).transform(returnTF.getFormula());
		substitution.clear();
		// 2.2 We rename the outvars to freshvars and quantify them
//		for (BoogieVar bv : returnTF.getOutVars().keySet()) {
//			TermVariable freshVar = getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
//			varsToRenameInReturnPred.put(bv.getTermVariable(), freshVar);
//			substitution.put(returnTF.getOutVars().get(bv), freshVar);
//			varsToQuantify.add(freshVar);
//		}
//		returnTermRenamed = new Substitution(substitution, m_Script).transform(returnTermRenamed);
		returnTermRenamed = substituteToFreshVarsAndAddToQuantify(returnTF.getOutVars(), returnTermRenamed, varsToRenameInReturnPred, varsToQuantify);
		// Rename the invars of the Call and quantify them
		substitution.clear();
		for (BoogieVar bv : callTF.getInVars().keySet()) {
			if (varsToRenameInCallerAndReturnPred.containsKey(bv.getTermVariable())) {
				substitution.put(callTF.getInVars().get(bv), varsToRenameInCallerAndReturnPred.get(bv.getTermVariable()));
			} else {
				TermVariable freshVar = null; 
				if (varsToRenameInCallerPred.containsKey(bv.getTermVariable())) {
					freshVar = (TermVariable) varsToRenameInCallerPred.get(bv.getTermVariable());
				} else {
					freshVar = getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
					varsToRenameInCallerPred.put(bv.getTermVariable(), freshVar);
				}
				substitution.put(callTF.getInVars().get(bv), freshVar);
				// If the variable is a modifiable global variable, we don't rename it in the returnerPred.
				if (!bv.isGlobal() && !globalVarsAssignments.getOutVars().containsKey(bv) &&
						!returnTF.getAssignedVars().contains(bv)) {
						varsToRenameInCallerAndReturnPred.put(bv.getTermVariable(), freshVar);
						varsToRenameInCallerPred.remove(bv.getTermVariable());
				}
				varsToQuantify.add(freshVar);
			}
		}
		Term callTermRenamed = new Substitution(substitution, m_Script).transform(callTF.getFormula());
		substitution.clear();
		for (BoogieVar bv : callTF.getOutVars().keySet()) {
			TermVariable freshVar = getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
			if (!varsToRenameInCallerAndReturnPred.containsKey(bv.getTermVariable())) {
				if (!varsToRenameInCallerPred.containsKey(bv.getTermVariable())) {
					varsToRenameInCallerAndReturnPred.put(bv.getTermVariable(), freshVar);
				} else {
					varsToRenameInReturnPred.put(bv.getTermVariable(), freshVar);
				}
			}
			substitution.put(callTF.getOutVars().get(bv), bv.getTermVariable());
			varsToQuantify.add(freshVar);
		}
		callTermRenamed = new Substitution(substitution, m_Script).transform(callTermRenamed);
		
		// Appropriately rename and quantify local vars in the returner predicate (i.e. the variables that do not occur in the called procedure)
		for (BoogieVar bv : returnerPred.getVars()) {
			// TODO: Check whether these 2 case are really necessary?
			if (bv.isOldvar()) {
				if (!varsToRenameInCallerAndReturnPred.containsKey(bv.getTermVariable()) &&
						!varsToRenameInReturnPred.containsKey(bv.getTermVariable())) {
					TermVariable freshVar = getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
					varsToRenameInReturnPred.put(bv.getTermVariable(), freshVar);
					varsToQuantify.add(freshVar);
				}
			} else if (!bv.isGlobal()){
				if (!varsToRenameInCallerAndReturnPred.containsKey(bv.getTermVariable())		
						&& !varsToRenameInReturnPred.containsKey(bv.getTermVariable())) {
					TermVariable freshVar = getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
					varsToRenameInCallerAndReturnPred.put(bv.getTermVariable(), freshVar);
					varsToQuantify.add(freshVar);
				}
				
			}
		}
		// Appropriately rename and quantify local vars in the caller predicate (i.e. the variables that do not occur in the called procedure)
		for (BoogieVar bv : callerPred.getVars()) {
			if (!bv.isGlobal()) {
				// 1.case: bv is a local var
				if (!varsToRenameInCallerAndReturnPred.containsKey(bv.getTermVariable())&&
						!varsToRenameInCallerPred.containsKey(bv.getTermVariable())) {
					TermVariable freshVar = getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
					varsToRenameInCallerAndReturnPred.put(bv.getTermVariable(), freshVar);
					varsToQuantify.add(freshVar);
				}
			} else if (bv.isOldvar()) {
				// 2.case: bv is an oldvar
				if (!varsToRenameInReturnPred.containsKey(bv.getTermVariable()) || 
						!varsToRenameInCallerAndReturnPred.containsKey(bv.getTermVariable())) {
					TermVariable freshVar = getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
					varsToRenameInCallerPred.put(bv.getTermVariable(), freshVar);
					varsToQuantify.add(freshVar);
				}
			} else {
				// 3.case: bv is a global var
				// If a global variable isn't modifiable by the returned proc. and it doesn't occur on the left-hand side
				// of the Return transformula (is not assigned), then do not quantify it.
				if (!modifiableGlobals.contains(bv)) {
					// TODO:
					if (returnerPred.getVars().contains(bv)) {
						continue;	
					}
				}
				// TODO: Is the occurrence of the global variable in the return Predicate just a special case, or
				// is the way  described above generally possible
				if (!varsToRenameInCallerPred.containsKey(bv.getTermVariable())) {
					TermVariable freshVar = getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
					varsToRenameInCallerPred.put(bv.getTermVariable(), freshVar);
					varsToQuantify.add(freshVar);
					// TODO: document this additional step
					if (returnerPred.getVars().contains(bv) && 
							!globalVarsAssignments.getOutVars().containsKey(bv)) {
						if (!varsToRenameInReturnPred.containsKey(bv.getTermVariable())) {
							varsToRenameInReturnPred.put(bv.getTermVariable(), freshVar);
						}
					}
				}
			}
		}
		
		Term returnPredRenamed = new Substitution(varsToRenameInCallerAndReturnPred, m_Script).transform(returnerPred.getFormula());
		returnPredRenamed = new Substitution(varsToRenameInReturnPred, m_Script).transform(returnPredRenamed);
		Term callerPredRenamed = new Substitution(varsToRenameInCallerAndReturnPred, m_Script).transform(callerPred.getFormula());
		callerPredRenamed = new Substitution(varsToRenameInCallerPred, m_Script).transform(callerPredRenamed);
		
		// Add aux vars to quantify them
		varsToQuantify.addAll(callTF.getAuxVars());
		varsToQuantify.addAll(returnTF.getAuxVars());
		varsToQuantify.addAll(globalVarsAssignments.getAuxVars());
		
		Term callerPredANDCallANDReturnAndGlobalVars = Util.and(m_Script, callerPredRenamed,
				returnTermRenamed, callTermRenamed,
				globalVarsRenamed);
		
		Term result = Util.or(m_Script, Util.not(m_Script, callerPredANDCallANDReturnAndGlobalVars), returnPredRenamed);
		
//		if (varsToQuantify.size() > 0) {
//			result = PartialQuantifierElimination.quantifier(m_Script, Script.FORALL,
//					varsToQuantify.toArray(new TermVariable[varsToQuantify.size()]),
//					result, (Term[][])null);
//		}
		return constructPredicate(result, Script.FORALL, varsToQuantify);
	}

	/**
	 * TODO: Documentation!
	 * @param varsToBeSubstituted
	 * @param varsToBeSubstitutedByFreshVars
	 * @param varsToQuantify
	 * @return 
	 */
	private Term substituteToFreshVarsAndAddToQuantify(
			Map<BoogieVar, TermVariable> varsToBeSubstituted,
			Term formulaToBeSubstituted,
			Map<TermVariable, Term> varsToBeSubstitutedByFreshVars,
			Set<TermVariable> varsToQuantify) {
		Map<TermVariable, Term> substitution = new HashMap<TermVariable, Term>();
		for (BoogieVar bv : varsToBeSubstituted.keySet()) {
			TermVariable freshVar = getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
			substitution.put(varsToBeSubstituted.get(bv), freshVar);
			if (varsToBeSubstitutedByFreshVars != null) {
				varsToBeSubstitutedByFreshVars.put(bv.getTermVariable(), freshVar);
			}
			if (varsToQuantify != null) {
				varsToQuantify.add(freshVar);
			}
		}
		return new Substitution(substitution, m_Script).transform(formulaToBeSubstituted);
	}

	/**
	 * TODO: Documentation!
	 * @param varsToBeSubstituted
	 * @param varsToBeSubstitutedByFreshVars
	 * @param varsToQuantify
	 * @return
	 */
	private Term substituteToRepresantantsAndAddToQuantify(
			Map<BoogieVar, TermVariable> varsToBeSubstituted,
			Term formulaToBeSubstituted,
			Map<TermVariable, Term> varsToBeSubstitutedByFreshVars,
			Set<TermVariable> varsToQuantify) {
		Map<TermVariable, Term> substitution = new HashMap<TermVariable, Term>();
		for (BoogieVar bv : varsToBeSubstituted.keySet()) {
			TermVariable freshVar = getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
			substitution.put(varsToBeSubstituted.get(bv), bv.getTermVariable());
			if (varsToBeSubstitutedByFreshVars != null) {
				varsToBeSubstitutedByFreshVars.put(bv.getTermVariable(), freshVar);
			}
			if (varsToQuantify != null) {
				varsToQuantify.add(freshVar);
			}
		}
		return new Substitution(substitution, m_Script).transform(formulaToBeSubstituted);
	}
	
	/**
	 * Substitutes each variable that doesn't occur in the given procedure by a fresh variable.
	 * @param tf
	 * @param thisProc
	 * @return
	 */
	public IPredicate renameVarsOfOtherProcsToFreshVars(IPredicate p, String thisProc) {
		Map<TermVariable, Term> substitution = new HashMap<TermVariable, Term>();
		Set<TermVariable> varsToQuantify = new HashSet<TermVariable>();
		// Substitute the vars if necessary
		for (BoogieVar bv : p.getVars()) {
			// if the current var bv is not a global and if it does belong to another
			// procedure, than replace it by a a fresh var
			if (bv.getProcedure() != null && !bv.getProcedure().equals(thisProc)) {
				TermVariable freshVar = getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
				substitution.put(bv.getTermVariable(), freshVar);
				varsToQuantify.add(freshVar);
			}
		}
		Term predicateRenamed = new Substitution(substitution, m_Script).transform(p.getFormula());
//		Term predicateRenamedQuantified = PartialQuantifierElimination.quantifier(m_Script, Script.EXISTS,
//				varsToQuantify.toArray(new TermVariable[varsToQuantify.size()]),
//				predicateRenamed, (Term[][])null);
		return constructPredicate(predicateRenamed, Script.EXISTS, varsToQuantify);
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

	
	/**
	 * Given a term in which every free variable is the TermVariable of a 
	 * BoogieVar. Compute the BoogieVars of the free variables and the 
	 * procedures of these BoogieVariables.
	 */
	public TermVarsProc computeTermVarsProc(Term term) {
		HashSet<BoogieVar> vars = new HashSet<BoogieVar>();
		Set<String> procs = new HashSet<String>();
		for (TermVariable tv : term.getFreeVars()) {
			BoogieVar bv = m_Boogie2Smt.getBoogie2SmtSymbolTable().getBoogieVar(tv);
			if (bv == null) {
				throw new AssertionError("No corresponding BoogieVar for " + tv);
			}
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
		Map<TermVariable,Term> substitutionMapping = new HashMap<TermVariable, Term>();
		for (BoogieVar bv : boogieVars) {
			substitutionMapping.put(bv.getTermVariable(), bv.getDefaultConstant());
		}
		Term closedTerm = (new Substitution(substitutionMapping, script)).transform(formula);
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
	
	
	public SPredicate newSPredicate(ProgramPoint pp, TermVarsProc termVarsProc) {
		SPredicate pred = new SPredicate(pp, m_SerialNumber++, 
				termVarsProc.getProcedures(), termVarsProc.getFormula(), 
				termVarsProc.getVars(), termVarsProc.getClosedFormula());
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
	
	public BasicPredicate newPredicate(TermVarsProc termVarsProc) {
		BasicPredicate predicate = new BasicPredicate(m_SerialNumber++,
				termVarsProc.getProcedures(), termVarsProc.getFormula(), 
				termVarsProc.getVars(), termVarsProc.getClosedFormula());
		return predicate;
	}
	
	public MLPredicate newMLPredicate(ProgramPoint[] programPoints, 
											TermVarsProc termVarsProc) {
		MLPredicate predicate = new MLPredicate(programPoints, 
				m_SerialNumber++,
				termVarsProc.getProcedures(), termVarsProc.getFormula(), 
				termVarsProc.getVars(), termVarsProc.getClosedFormula());
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
	
	public MLPredicate newMLDontCarePredicate(ProgramPoint[] pps) {
		Set<BoogieVar> empty = Collections.emptySet();
		MLPredicate pred = new MLPredicate(pps, m_SerialNumber++, new String[0],
				getDontCareTerm(), empty, getDontCareTerm());
		return pred;
	}
	
	public DebugPredicate newDebugPredicate(String debugMessage) {
		DebugPredicate pred = new DebugPredicate(debugMessage, m_SerialNumber++);
		return pred;
	}
	
	public ISLPredicate newEmptyStackPredicate() {
		ProgramPoint pp = new ProgramPoint("noCaller", "noCaller", false, 
				null);
		return newSPredicate(pp, new TermVarsProc(m_EmptyStackTerm, 
				m_EmptyVars, m_NoProcedure, m_EmptyStackTerm));
		
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
	
	Status getStatus() {
		return m_Status;
	}

	void setStatus(Status status) {
		m_Status = status;
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
