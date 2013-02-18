package local.stalin.plugins.generator.traceabstraction;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import local.stalin.SMTInterface.SMTInterface;
import local.stalin.automata.nwalibrary.INestedWordAutomaton;
import local.stalin.automata.nwalibrary.IState;
import local.stalin.core.api.StalinServices;
import local.stalin.logic.ApplicationTerm;
import local.stalin.logic.Atom;
import local.stalin.logic.Formula;
import local.stalin.logic.FormulaUnFleterer;
import local.stalin.logic.FormulaWalker;
import local.stalin.logic.FunctionSymbol;
import local.stalin.logic.SMTLibBase;
import local.stalin.logic.Sort;
import local.stalin.logic.Term;
import local.stalin.logic.TermVariable;
import local.stalin.logic.Theory;
import local.stalin.model.IEdge;
import local.stalin.model.INode;
import local.stalin.model.boogie.ast.ASTType;
import local.stalin.plugins.generator.rcfgbuilder.CallAnnot;
import local.stalin.plugins.generator.rcfgbuilder.IProgramState;
import local.stalin.plugins.generator.rcfgbuilder.InternalEdge;
import local.stalin.plugins.generator.rcfgbuilder.LocNode;
import local.stalin.plugins.generator.rcfgbuilder.ReturnAnnot;
import local.stalin.plugins.generator.rcfgbuilder.RootNode;
import local.stalin.plugins.generator.rcfgbuilder.StateFormula;
import local.stalin.plugins.generator.rcfgbuilder.SummaryEdge;
import local.stalin.plugins.generator.rcfgbuilder.TransAnnot;
import local.stalin.plugins.generator.rcfgbuilder.TransFormula;
import local.stalin.plugins.generator.rcfgbuilder.smt.BoogieVar2SmtVar;

public class SmtManager {
	
	private static Logger s_Logger = 
		StalinServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	
	private final BoogieVar2SmtVar m_BoogieVar2SmtVar;
	private final Theory m_Theory;
	private final SMTInterface m_SmtInterface;
	private final Map<String,ASTType> m_GlobalVars;
	private final boolean m_DumpFormulaToFile;
	private final String m_DumpPath;
	private int m_Iteration;
	private int m_satProbNumber;

	private int m_TrivialSatQueries = 0;
	private int m_NontrivialSatQueries = 0;
	
	public SmtManager(BoogieVar2SmtVar boogieVar2SmtVar,
					int solver, 
					Map<String,ASTType> globalVars,
					boolean dumpFormulaToFile,
					String dumpPath) {
		m_BoogieVar2SmtVar = boogieVar2SmtVar;
		m_Theory = boogieVar2SmtVar.getTheory();
		m_SmtInterface = new SMTInterface(m_Theory, solver);
		m_GlobalVars = globalVars;
		m_DumpFormulaToFile = dumpFormulaToFile;
		m_DumpPath = dumpPath;
	}
	
	
	public BoogieVar2SmtVar getBoogieVar2SmtVar() {
		return m_BoogieVar2SmtVar;
	}


	public Theory getTheory() {
		return m_Theory;
	}


	public SMTInterface getSmtInterface() {
		return m_SmtInterface;
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
	

	public void setIteration(int iteration) {
		m_Iteration = iteration;
		m_satProbNumber = 0;
	}



	/**
	 * Check if ps1 is a subset of ps2.
	 * @param ps1 set of states represented as IProgramState
	 * @param ps2 set of states resresented as IProgramState
	 * @return SMT_UNSAT if the inclusion holds, 1729 if the inclusion trivially
	 * holds, SMT_SAT if the inclusion does not hold and SMT_UNKNOWN if the
     * theorem prover was not able to give an answer.
	 */
	public int isCovered(IProgramState ps1, IProgramState ps2) {
		Formula formula1 = ps1.getFormula();
		Formula formula2 = ps2.getFormula();
		int result;
		// tivial case
		if (formula1 == Atom.FALSE || formula2 == Atom.TRUE) {
			m_TrivialSatQueries++;
			result = 1729;
		}
		else {
			m_NontrivialSatQueries++;
			Formula negImpl = m_Theory.and(formula1, m_Theory.not(formula2));
			if (m_DumpFormulaToFile) {
				dumpSatProblem(negImpl, m_Iteration, m_satProbNumber, m_DumpPath, m_Theory);
				m_satProbNumber++;
			}
			result = m_SmtInterface.checkSatisfiable(negImpl);
		}
		return result;
	}
	
	//TODO less renaming possible e.g. keep var names in ps1
	/**
	 * Check if post(sf1,tf) is a subset of sf2.
	 * @param ps1 a set of states represented by a StateFormula
	 * @param tf a transition relation represented by a TransFormula
	 * @param ps2 a set of states represented by a StateFormula
	 * @return The result of a theorem prover query, where SMT_UNSAT means yes
	 * to our question, SMT_SAT means no to our question and SMT_UNKNOWN means
	 * that the theorem prover was not able give an answer to our question. 
	 */
	public int checkInductivity(IProgramState ps1, TransAnnot ta, IProgramState ps2) {

		if (ps1.isUnknown() || ps2.isUnknown()) {
			m_TrivialSatQueries++;
			return SMTInterface.SMT_UNKNOWN;
		}
		
		if (ps1.getFormula() == Atom.FALSE || ps2.getFormula() == Atom.TRUE) {
			m_TrivialSatQueries++;
			return SMTInterface.SMT_UNSAT;
		}
		
		m_NontrivialSatQueries++;
		
		Formula ps1renamed = formulaWithIndexedVars(ps1,new HashSet<String>(0),
				4, 0, Integer.MIN_VALUE,null,-5);
		
		TransFormula tf = ta.getTransitionFormula();
		Set<String> assignedVars = new HashSet<String>();
		Formula fTrans = formulaWithIndexedVars(tf, 0, 1, assignedVars);

		
		Formula ps2renamed = formulaWithIndexedVars(ps2, assignedVars,
				1, 0, Integer.MIN_VALUE,null,-5);
		
		
		//We want to return true if (fState1 && fTrans)-> fState2 is valid
		//This is the case if (fState1 && fTrans && !fState2) is unsatisfiable
		Formula f = m_Theory.not(ps2renamed);
		f = m_Theory.and(fTrans,f);
		f = m_Theory.and(ps1renamed, f);
		
		if (m_DumpFormulaToFile) {
			dumpSatProblem(f,m_Iteration,m_satProbNumber,m_DumpPath,m_Theory);
			m_satProbNumber++;
		}
		return m_SmtInterface.checkSatisfiable(f);
	}
	
	
	
	/**
	 * 
	 * @param ps1
	 * @param ta
	 * @param ps2
	 * @return
	 */
	public int isInductiveCall(IProgramState ps1, CallAnnot ta, IProgramState ps2) {
		if (ps1.isUnknown() || ps2.isUnknown()) {
			m_TrivialSatQueries++;
			return SMTInterface.SMT_UNKNOWN;
		}
		
		if (ps1.getFormula() == Atom.FALSE || ps2.getFormula() == Atom.TRUE) {
			m_TrivialSatQueries++;
			return SMTInterface.SMT_UNSAT;
		}
		
		m_NontrivialSatQueries++;
		
		Formula ps1renamed = formulaWithIndexedVars(ps1,new HashSet<String>(0),
				4, 0, Integer.MIN_VALUE,null,-5);
		
		TransFormula tf = ta.getTransitionFormula();
		Set<String> assignedVars = new HashSet<String>();
		Formula fTrans = formulaWithIndexedVars(tf, 0, 1, assignedVars);

		
		Formula ps2renamed = formulaWithIndexedVars(ps2, new HashSet<String>(0),
				4, 1, 0,ta.getOldVarsEquality().getOutVars().keySet(),0);
		
		
		//We want to return true if (fState1 && fTrans)-> fState2 is valid
		//This is the case if (fState1 && fTrans && !fState2) is unsatisfiable
		Formula f = m_Theory.not(ps2renamed);
		f = m_Theory.and(fTrans,f);
		f = m_Theory.and(ps1renamed, f);
		
		if (m_DumpFormulaToFile) {
			dumpSatProblem(f,m_Iteration,m_satProbNumber,m_DumpPath,m_Theory);
			m_satProbNumber++;
		}
		return m_SmtInterface.checkSatisfiable(f);		
	}
	
	public int isInductiveReturn(IProgramState ps1, 
			IProgramState psk, 
			ReturnAnnot ta, 
			IProgramState ps2) {
		if (ps1.isUnknown() || ps2.isUnknown() || psk.isUnknown()) {
			m_TrivialSatQueries++;
			return SMTInterface.SMT_UNKNOWN;
		}
		
		if (ps1.getFormula() == Atom.FALSE ||
				psk.getFormula() == Atom.FALSE ||
				ps2.getFormula() == Atom.TRUE) {
			m_TrivialSatQueries++;
			return SMTInterface.SMT_UNSAT;
		}
		
		m_NontrivialSatQueries++;
		
		CallAnnot ca = ta.getCorrespondingCallAnnot();
		Set<String> modifiableGlobals = 
			 					ca.getOldVarsEquality().getOutVars().keySet();
		
		
		TransFormula tfReturn = ta.getTransitionFormula();
		Set<String> assignedVarsOnReturn = new HashSet<String>();
		Formula fReturn = formulaWithIndexedVars(tfReturn, 1, 2, assignedVarsOnReturn);
		fReturn = (new FormulaUnFleterer(m_Theory)).unflet(fReturn);
		
		TransFormula tfCall = ca.getTransitionFormula();
		Set<String> assignedVarsOnCall = new HashSet<String>();
		Formula fCall = formulaWithIndexedVars(tfCall, 0, 1, assignedVarsOnCall);
		fCall = (new FormulaUnFleterer(m_Theory)).unflet(fCall);

		// oldVars not renamed
		// other variables get index 0
		Formula pskrenamed = formulaWithIndexedVars(psk, new HashSet<String>(0),
				23, 0, Integer.MIN_VALUE, null, 23);

		
		// oldVars get index 0
		// modifiable globals get index 2
		// other variables get index 1
		Formula ps1renamed = formulaWithIndexedVars(ps1, new HashSet<String>(0),
				23, 1, 0, modifiableGlobals, 2);
		
		// oldVars not renamed
		// modifiable globals get index 2
		// variables assigned on return get index 2
		// other variables get index 0
		Formula ps2renamed = formulaWithIndexedVars(ps2, assignedVarsOnReturn,
				2, 0, Integer.MIN_VALUE, modifiableGlobals, 2);
		
		
		//We want to return true if (fState1 && fTrans)-> fState2 is valid
		//This is the case if (fState1 && fTrans && !fState2) is unsatisfiable
		Formula f = m_Theory.not(ps2renamed);
		f = m_Theory.and(fReturn,f);
		f = m_Theory.and(ps1renamed, f);
		f = m_Theory.and(fCall, f);
		f = m_Theory.and(pskrenamed, f);
		
		if (m_DumpFormulaToFile) {
			dumpSatProblem(f,m_Iteration,m_satProbNumber,m_DumpPath,m_Theory);
			m_satProbNumber++;
		}
		return m_SmtInterface.checkSatisfiable(f);	
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
	private Formula formulaWithIndexedVars(IProgramState ps, 
						Set<String> varsWithSpecialIdx, int specialIdx,
						int defaultIdx,
						int oldVarIdx,
						Set<String> globalsWithSpecialIdx, int globSpecialIdx) {
		Formula result;
		Map<ApplicationTerm, ApplicationTerm> substitution;
		ConstantSubstitutionVisitor csv;
		FormulaWalker walker;

		Formula psFormula = ps.getFormula();
		
		substitution = new HashMap<ApplicationTerm, ApplicationTerm>();
		if (ps.getOldVars() != null)
			for (String oldVar : ps.getOldVars()) {
				ApplicationTerm c = m_BoogieVar2SmtVar.getOldVariable(oldVar);
				ApplicationTerm cIndex;
				if (oldVarIdx == Integer.MIN_VALUE) {
					cIndex = getOldVarConstant(oldVar, c.getSort());
				}
				else {
					cIndex = getIndexedConstant(oldVar, oldVarIdx, c.getSort());
				}
				substitution.put(c, cIndex);
			}

		if (ps.getVars() != null)
			for (String var : ps.getVars()) {
				int index;
				if (varsWithSpecialIdx.contains(var)) {
					index = specialIdx;
				}
				else if	(globalsWithSpecialIdx != null && 
						globalsWithSpecialIdx.contains(var)) {
					index = globSpecialIdx;
				}
				else {
					index = defaultIdx;
				}
				ApplicationTerm c = m_BoogieVar2SmtVar.getVariable(var);
				ApplicationTerm cIndex = 
						getIndexedConstant(var, index, c.getSort());
				substitution.put(c, cIndex);
			}
		csv = new ConstantSubstitutionVisitor(m_Theory, substitution);
		walker = new FormulaWalker(csv, m_Theory);
		result = walker.process(psFormula);
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
	private Formula formulaWithIndexedVars(TransFormula tf,
			int idxInVar, int idxOutVar, Set<String> assignedVars) {
		assert (assignedVars != null && assignedVars.isEmpty());
		int idxFreshVar = 23;
		Set<TermVariable> notYetSubst = new HashSet<TermVariable>();
		notYetSubst.addAll(tf.getVars());
		Formula fTrans = tf.getFormula();
		for (String oldVar : tf.getOldVars().keySet()) {
			TermVariable tv = tf.getOldVars().get(oldVar);
			ApplicationTerm cIndex = 
						getOldVarConstant(oldVar, tv.getSort());
			fTrans = m_Theory.let(tv, cIndex, fTrans);
			notYetSubst.remove(tv);
		}
		for (String inVar : tf.getInVars().keySet()) {
			TermVariable tv = tf.getInVars().get(inVar);
			ApplicationTerm cIndex = 
						getIndexedConstant(inVar, idxInVar, tv.getSort());
			fTrans = m_Theory.let(tv, cIndex, fTrans);
			notYetSubst.remove(tv);
		}
		for (String outVar : tf.getOutVars().keySet()) {
			TermVariable tv = tf.getOutVars().get(outVar);
			if (tf.getInVars().get(outVar) != tv) {
				assignedVars.add(outVar);
				ApplicationTerm cIndex = 
						getIndexedConstant(outVar, idxOutVar, tv.getSort());
				fTrans = m_Theory.let(tv, cIndex, fTrans);
				notYetSubst.remove(tv);
			}
		}
		for (TermVariable tv : notYetSubst) {
			ApplicationTerm cIndex = 
					getIndexedConstant(tv.getName(), idxFreshVar, tv.getSort());
			fTrans = m_Theory.let(tv, cIndex, fTrans);
		}
		
		return fTrans;		
	}
			
			
	



	static ApplicationTerm getConstant(Theory theory, String name, Sort sort) {
		Sort[] emptySorts = {};
		FunctionSymbol func = theory.getFunction(name, emptySorts); 
		if (func == null) {
			func = theory.createFunction(name, emptySorts, sort);
		}
		Term[] emptyTerms = {};
		return theory.term(func, emptyTerms);
	}
	
	private ApplicationTerm getIndexedConstant(String varName, int index, Sort sort) {
		String name = SMTLibBase.quoteId("v_"+varName+"_"+index);
		Sort[] emptySorts = {};
		FunctionSymbol func = m_Theory.getFunction(name, emptySorts); 
		if (func == null) {
			func = m_Theory.createFunction(name, emptySorts, sort);
		}
		Term[] emptyTerms = {};
		return m_Theory.term(func, emptyTerms);
	}
	
	private ApplicationTerm getOldVarConstant(String varName, Sort sort) {
		String name = SMTLibBase.quoteId("v_"+varName+"_OLD");
		Sort[] emptySorts = {};
		FunctionSymbol func = m_Theory.getFunction(name, emptySorts); 
		if (func == null) {
			func = m_Theory.createFunction(name, emptySorts, sort);
		}
		Term[] emptyTerms = {};
		return m_Theory.term(func, emptyTerms);
	}

	
	
	public boolean checkInductivity(INestedWordAutomaton<TransAnnot, IProgramState> nwa) {
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
		for(IState<TransAnnot, IProgramState> state : nwa.getAllStates()) {
//			assert (state.getContent().getStateFormulas().size()==1);
			IProgramState sf1 = state.getContent();
			for (TransAnnot transAnnot : state.getSymbolsInternal()) {
				for (IState<TransAnnot, IProgramState> succState : state.getInternalSucc(transAnnot)) {
//					assert (succState.getContent().getStateFormulas().size()==1);
					IProgramState sf2 = succState.getContent();

					if (sf1 == null || sf2 == null) {
						yield[3]++;
					}
					else {
						int inductivity = checkInductivity(sf1, transAnnot, sf2);
						switch (inductivity) {
						case SMTInterface.SMT_UNSAT: {
							yield[0]++;
							break;
						}
						case SMTInterface.SMT_SAT: {
							yield[1]++;
							assert (false);
							//						s_Logger.warn("Transition   "+ tf + "   from   "+ sf1 + "   to   " + sf2 + "   not inductive");
							result = false;
							break;
						}
						case SMTInterface.SMT_UNKNOWN: {
							yield[2]++;
							//						s_Logger.warn("Theorem prover too weak to decide inductiveness");
							break;
						}
						default:
							throw new IllegalArgumentException();
						}
					}
				}
			}
			
			for (TransAnnot transAnnot : state.getSymbolsCall()) {
				
				for (IState<TransAnnot, IProgramState> succState : state.getCallSucc(transAnnot)) {
//					assert (succState.getContent().getStateFormulas().size()==1);
					IProgramState sf2 = succState.getContent();

					if (sf1 == null || sf2 == null) {
						yield[3]++;
					}
					else {
						int inductivity = isInductiveCall(sf1, (CallAnnot) transAnnot, sf2);
						switch (inductivity) {
						case SMTInterface.SMT_UNSAT: {
							yield[0]++;
							break;
						}
						case SMTInterface.SMT_SAT: {
							yield[1]++;
							assert (false);
							//						s_Logger.warn("Transition   "+ tf + "   from   "+ sf1 + "   to   " + sf2 + "   not inductive");
							result = false;
							break;
						}
						case SMTInterface.SMT_UNKNOWN: {
							yield[2]++;
							//						s_Logger.warn("Theorem prover too weak to decide inductiveness");
							break;
						}
						default:
							throw new IllegalArgumentException();
						}
					}
				}
				
				
			}
			
			for (TransAnnot transAnnot : state.getSymbolsReturn()) {
				for (IState<TransAnnot, IProgramState> linPred : state.getReturnLinearPred(transAnnot)) {

					for (IState<TransAnnot, IProgramState> succState : state.getReturnSucc(linPred,transAnnot)) {
						//					assert (succState.getContent().getStateFormulas().size()==1);
						IProgramState sf2 = succState.getContent();
						IProgramState sfk = linPred.getContent();

						if (sf1 == null || sf2 == null || sfk == null) {
							yield[3]++;
						}
						else {
							int inductivity = isInductiveReturn(sf1, sfk, (ReturnAnnot) transAnnot, sf2);
							switch (inductivity) {
							case SMTInterface.SMT_UNSAT: {
								yield[0]++;
								break;
							}
							case SMTInterface.SMT_SAT: {
								yield[1]++;
								assert (false);
								//						s_Logger.warn("Transition   "+ tf + "   from   "+ sf1 + "   to   " + sf2 + "   not inductive");
								result = false;
								break;
							}
							case SMTInterface.SMT_UNKNOWN: {
								yield[2]++;
								//						s_Logger.warn("Theorem prover too weak to decide inductiveness");
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
		
		List<INode> initialNodes = rootNode.getOutgoingNodes();
		Set<LocNode> visited = new HashSet<LocNode>();
		List<LocNode> worklist = new LinkedList<LocNode>();
		
		for (INode initINode : initialNodes) {
			LocNode initNode = (LocNode) initINode;
			visited.add(initNode);
			worklist.add(initNode);
		}
		while (!worklist.isEmpty()) {
			LocNode locNode = worklist.remove(0);
			for (IEdge iEdge : locNode.getOutgoingEdges()) {
				TransAnnot transAnnot;
				if (iEdge instanceof InternalEdge) {
					transAnnot= ((InternalEdge) iEdge).getInternalAnnotations();	
				}
				else if (iEdge instanceof SummaryEdge) {
					transAnnot= ((SummaryEdge) iEdge).getInternalAnnotations();
				}
				else {
					continue;
				}
				INode iSuccLoc = iEdge.getTarget();
				LocNode succLoc = (LocNode) iSuccLoc;
				if (!visited.contains(succLoc)) {
					visited.add(succLoc);
					worklist.add(succLoc);
				}
				
				IProgramState sf1 = locNode.getStateAnnot();
				IProgramState sf2 = succLoc.getStateAnnot();
				
				int inductivity = checkInductivity(sf1, transAnnot, sf2);
				switch (inductivity) {
				case SMTInterface.SMT_UNSAT: {
					yield[0]++;
					break;
				}
				case SMTInterface.SMT_SAT: {
					yield[1]++;
					//						s_Logger.warn("Transition   "+ tf + "   from   "+ sf1 + "   to   " + sf2 + "   not inductive");
					result = false;
					break;
				}
				case SMTInterface.SMT_UNKNOWN: {
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
	
	
	
	
	
	
	
	
	
	
	
	static protected void dumpInterpolProblem(Formula[] formulas,
			int iterationNumber, int interpolProblem,
			String dumpPath, Theory theory) {
		String filename = "Iteration" + iterationNumber + "_InterpolProblem" 
				+ interpolProblem + ".smt";
		File file = new File(dumpPath + "/" +filename);
		FileWriter fileWriter;
		try {
			fileWriter = new FileWriter(file);
			PrintWriter printWriter = new PrintWriter(fileWriter);
			theory.dumpInterpolationBenchmark(printWriter, formulas);
			fileWriter.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
//		s_Logger.debug("Dumped interpolation problem in file" + m_DumpPath + "/" +filename + "!");
	}
	
	static protected void dumpSatProblem(Formula formula,
			int iterationNumber, int satProbNumber,
			String dumpPath, Theory theory) {
		String filename = "Iteration" + iterationNumber + "_SatProblem" 
			+ satProbNumber + ".smt";
		File file = new File(dumpPath + "/" +filename);
		FileWriter fileWriter;
		try {
			fileWriter = new FileWriter(file);
			PrintWriter printWriter = new PrintWriter(fileWriter);
			theory.dumpBenchmark(printWriter, formula);
			fileWriter.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
//		s_Logger.debug("Dumped satisfiability problem in file" + dumpPath + "/" +satCheckFilename);
	}






	
}
