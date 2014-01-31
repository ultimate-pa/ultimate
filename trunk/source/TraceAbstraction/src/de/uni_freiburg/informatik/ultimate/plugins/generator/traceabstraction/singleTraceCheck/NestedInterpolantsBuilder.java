package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.FormulaWalker;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.BasicCegarLoop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.util.DebugMessage;

public class NestedInterpolantsBuilder {
	
	private static Logger s_Logger = 
		UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	
	final Script m_Script;
	final SmtManager m_SmtManager;
	final PredicateConstructionVisitor m_sfmv;

	Term[] m_CraigInterpolants;
	final PrintWriter m_IterationPW = null;
//	final int m_Iteration =-1;
//	int m_InterpolationProblem = 0;
	
	private IPredicate[] m_Interpolants;

//	private TAPreferences m_Pref = null;
	
	private NestedFormulas<Term, Term> m_AnnotSSA;
	
	private final PredicateUnifier m_PredicateBuilder;

	private Set<Integer> m_InterpolatedPositions;

	private ArrayList<Term> interpolInput;

	private ArrayList<Integer> treeStructure;

	private ArrayList<Integer> craigInt2interpolantIndex;

	private int startOfCurrentSubtree;

	private final NestedWord<CodeBlock> m_Trace;

	private int m_stackHeightAtLastInterpolatedPosition;

	private Stack<Integer> m_startOfSubtreeStack;
	
	private final boolean m_TreeInterpolation;

	public NestedInterpolantsBuilder(SmtManager smtManager,
									NestedFormulas<Term, Term> annotatdSsa,
								 	Map<Term,BoogieVar> m_constants2BoogieVar,
								 	PredicateUnifier predicateBuilder,
								 	Set<Integer> interpolatedPositions,
								 	boolean treeInterpolation) {
		m_TreeInterpolation = treeInterpolation;
		m_Script = smtManager.getScript();
		m_SmtManager = smtManager;
		m_PredicateBuilder = predicateBuilder;
		m_AnnotSSA = annotatdSsa;
		m_CraigInterpolants = new Term[m_AnnotSSA.getTrace().length()-1];
		m_sfmv = new PredicateConstructionVisitor(m_constants2BoogieVar);
		m_InterpolatedPositions = interpolatedPositions;
		m_Trace = annotatdSsa.getTrace();

		
		computeCraigInterpolants();
		m_SmtManager.endTraceCheck();
			for (int i=0; i<m_CraigInterpolants.length; i++) {
				s_Logger.debug(new DebugMessage("NestedInterpolant {0}: {1}", i, m_CraigInterpolants[i]));
			}
		m_Interpolants = computePredicates();
		assert m_Interpolants != null;
//			if (m_Pref.dumpFormulas()) {
//				dumpNestedStateFormulas(m_Interpolants, m_Trace, m_IterationPW);
		} 
	
	
	

	
	
	
	public void computeCraigInterpolants() {
		interpolInput = new ArrayList<Term>();
		treeStructure= new ArrayList<Integer>();
		craigInt2interpolantIndex = new ArrayList<Integer>();
		startOfCurrentSubtree = 0;
		m_startOfSubtreeStack = new Stack<Integer>();
		m_stackHeightAtLastInterpolatedPosition = 0;
		boolean startNewFormula = true;
		
		for (int i=0; i<m_AnnotSSA.getTrace().length(); i++) {
			//if last position was interpolated position we add new formula to interpol input
			if (startNewFormula) {
				if (m_Trace.isInternalPosition(i)) {
					newInterpolInputFormula(i);		
				} else if (m_Trace.isCallPosition(i)) {
					if (!m_Trace.isPendingCall(i)) {
						int nextPosition = interpolInput.size();
						m_startOfSubtreeStack.push(startOfCurrentSubtree);
						startOfCurrentSubtree = nextPosition;
					}
					newInterpolInputFormula(i);
					if (m_Trace.isPendingCall(i)) {
						addToLastInterpolInputFormula(m_AnnotSSA.getLocalVarAssignment(i));
						addToLastInterpolInputFormula(m_AnnotSSA.getOldVarAssignment(i));
					}
				} else if (m_Trace.isReturnPosition(i)) {
					if (m_Trace.isPendingReturn(i)) {
						newInterpolInputFormula(i);
						addToLastInterpolInputFormula(m_AnnotSSA.getLocalVarAssignment(i));
						addToLastInterpolInputFormula(m_AnnotSSA.getOldVarAssignment(i));
						addToLastInterpolInputFormula(m_AnnotSSA.getPendingContext(i));
					} else {
						startOfCurrentSubtree = m_startOfSubtreeStack.pop();
						newInterpolInputFormula(i);
						int correspondingCallPosition = m_Trace.getCallPosition(i);
						addToLastInterpolInputFormula(m_AnnotSSA.getLocalVarAssignment(correspondingCallPosition));
						addToLastInterpolInputFormula(m_AnnotSSA.getOldVarAssignment(correspondingCallPosition));
					}
						
				} else {
					throw new AssertionError();
				}
						
			} else {
				if (m_Trace.isInternalPosition(i)) {
					addToLastInterpolInputFormula(m_AnnotSSA.getFormulaFromNonCallPos(i));
				} else if (m_Trace.isCallPosition(i)) {
					if (!m_Trace.isPendingCall(i)) {
						m_startOfSubtreeStack.push(startOfCurrentSubtree);
						startOfCurrentSubtree = -23;
					}
					addToLastInterpolInputFormula(m_AnnotSSA.getGlobalVarAssignment(i));
					if (m_Trace.isPendingCall(i)) {
						addToLastInterpolInputFormula(m_AnnotSSA.getLocalVarAssignment(i));
						addToLastInterpolInputFormula(m_AnnotSSA.getOldVarAssignment(i));
					} 
				} else if (m_Trace.isReturnPosition(i)) {
					if (m_Trace.isPendingReturn(i)) {
						addToLastInterpolInputFormula(m_AnnotSSA.getFormulaFromNonCallPos(i));
						addToLastInterpolInputFormula(m_AnnotSSA.getLocalVarAssignment(i));
						addToLastInterpolInputFormula(m_AnnotSSA.getOldVarAssignment(i));
						addToLastInterpolInputFormula(m_AnnotSSA.getPendingContext(i));
					} else {
						startOfCurrentSubtree = m_startOfSubtreeStack.pop();
						addToLastInterpolInputFormula(m_AnnotSSA.getFormulaFromNonCallPos(i));
						int correspondingCallPosition = m_Trace.getCallPosition(i);
						addToLastInterpolInputFormula(m_AnnotSSA.getLocalVarAssignment(correspondingCallPosition));
						addToLastInterpolInputFormula(m_AnnotSSA.getOldVarAssignment(correspondingCallPosition));
					}					
				} else {
					throw new AssertionError();
				}
			}
			startNewFormula = isInterpolatedPositio(i);
			if (isInterpolatedPositio(i)) {
				m_stackHeightAtLastInterpolatedPosition = m_startOfSubtreeStack.size();
				craigInt2interpolantIndex.add(i);
			}

		}
		Term[] interpolInput = this.interpolInput.toArray(new Term[0]);
		//add precondition to first term
		// special case: if first position is non pending call, then we add the
		// precondition to the corresponding return. 
		if (m_Trace.isCallPosition(0) && !m_Trace.isPendingCall(0)) {
			final int correspondingReturn = m_Trace.getReturnPosition(0);
			// if we do not interpolate at each position
			// interpolInput[correspondingReturn] might be the wrong position
			int interpolInputPositionOfReturn = 0;
			for (int i=0; i<correspondingReturn; i++) {
				if (m_InterpolatedPositions.contains(i)) {
					interpolInputPositionOfReturn++;
				}
			}
			interpolInput[interpolInputPositionOfReturn] = Util.and(m_Script, interpolInput[interpolInputPositionOfReturn], m_AnnotSSA.getPrecondition());
		} else {
			interpolInput[0] = Util.and(m_Script, interpolInput[0], m_AnnotSSA.getPrecondition());
		}
		//add negated postcondition to last term
		interpolInput[interpolInput.length-1] = Util.and(m_Script, interpolInput[interpolInput.length-1], m_AnnotSSA.getPostcondition());
		
		int[] startOfSubtree = integerListToIntArray(this.treeStructure);
		if (m_TreeInterpolation) {
			m_CraigInterpolants = m_SmtManager.computeInterpolants(interpolInput, startOfSubtree);
		} else {
			m_CraigInterpolants = m_SmtManager.computeInterpolants(interpolInput);
		}
		
	}
	
	
	public static int[] integerListToIntArray(List<Integer> integerList) {
		int[] result = new int[integerList.size()];
		for (int i=0; i<integerList.size();i++) {
			result[i] = integerList.get(i);
		}
		return result;
	}
	
	
	private void newInterpolInputFormula(int i) {
		if (m_stackHeightAtLastInterpolatedPosition == m_startOfSubtreeStack.size()) {
			//everything ok
		} else {
			if (m_stackHeightAtLastInterpolatedPosition+1 == m_startOfSubtreeStack.size() && m_Trace.isCallPosition(i) && (i==0 || isInterpolatedPositio(i-1))) {
				//everything ok
			} else {
				if (m_stackHeightAtLastInterpolatedPosition-1 == m_startOfSubtreeStack.size() && m_Trace.isReturnPosition(i) && isInterpolatedPositio(i-1)) {
					//everything ok
				} else {
					throw new IllegalArgumentException("if you want to interpolate between call and return you have to interpolate after call and after return.");
				}
			}
		}
		Term term;
		if (m_Trace.isCallPosition(i)) {
			term = m_AnnotSSA.getGlobalVarAssignment(i);
		} else {
			term = m_AnnotSSA.getFormulaFromNonCallPos(i);
		}
		interpolInput.add(term);
		//the interpolant between last formula and this new formula can be found
		//at position i-1
		
		treeStructure.add(startOfCurrentSubtree);
	}
	
	private void addToLastInterpolInputFormula(Term term) {
		int lastPosition = interpolInput.size() - 1;
		Term newFormula = Util.and(m_Script, interpolInput.get(lastPosition), term);
		interpolInput.set(lastPosition, newFormula);
	}
	

	public boolean isInterpolatedPositio(int i) {
		assert i>=0;
		assert i<m_Trace.length();
		if (i==m_Trace.length()-1) {
			return false;
		}
		if (m_InterpolatedPositions == null) {
			return true;
		} else {
			return m_InterpolatedPositions.contains(i);
		}
	}

	
	

	
	public IPredicate[] getNestedInterpolants() {
		for (int j=0; j<m_Interpolants.length; j++) {
			s_Logger.debug(new DebugMessage("Interpolant {0}: {1}", j, m_Interpolants[j]));
		}
		return m_Interpolants;
	}
	


	
//	/**
//	 * Compute nested interpolants for given SSA. The result are the Craig
//	 * interpolants for the SSA given as formula, the interpolants contain the
//	 * variables with indices as they occur in the SSA. The result is written
//	 * to m_CraigInterpolants.
//	 */
//	private void computeCraigInterpolants() {
////		m_CraigInterpolants[0] = m_SmtManager.getScript().term("true");
////		m_CraigInterpolants[m_CraigInterpolants.length-1] =  m_SmtManager.getScript().term("false");
//		List<Integer> interpolProbStartPositions = getInterpolProbStartPositions();
//		for (Integer k: interpolProbStartPositions) {
//			computeInterpolantSubsequence(k);
//		}
//	}
//	
//	
//	
//	/**
//	 * Given a run, return all positions from where we have to start an 
//	 * interpolation problem. These positions are:
//	 * <ul>
//	 * <li> Position 0
//	 * <li> Each call position where the call is not a pending call.
//	 * </ul> 
//	 */
//	private List<Integer> getInterpolProbStartPositions() {
//		List<Integer> interpolProbStartPos = new LinkedList<Integer>();
////		if (m_Pref.interprocedural()) {
//			for (int i=0; i<m_Trace.length(); i++) {
//				if (m_Trace.isCallPosition(i) && !m_Trace.isPendingCall(i)) {
//					interpolProbStartPos.add(i);
//				}
//			}
//			if (interpolProbStartPos.isEmpty() || 
//					interpolProbStartPos.get(0) !=0 ) {
//				interpolProbStartPos.add(0, 0);
//			}
////		}
////		else {
////			interpolProbStartPos.add(0);
////		}
//		return interpolProbStartPos;
//	}
	
	
//	/**
//	 * Given the SSA compute interpolants for a subsequence starting from
//	 * position k and write the result to m_CraigInterpolants.
//	 * If k is a non-pending call position the end of the sequence is the 
//	 * corresponding return position. Otherwise k = 0 and the end position is 
//	 * the last position of the SSA.
//	 * The interpolation subsequence consists of the corresponding SSA 
//	 * subsequence. If k!=0, we add two additional conjuncts. First the 
//	 * k-th interpolant (which has been computed yet). Second, the negation of
//	 * the 'sequence end position'-th interpolant.
//	 * @param k a non-pending call position of the m_run or 0
//	 * @return true iff the interpolation subsequence is satisfiable
//	 * @throws ölö 
//	 */
//	private boolean computeInterpolantSubsequence(int k) {
//		int endPos;
//		if (k==0) {
//			endPos = m_AnnotSSA.getTerms().length-1;
//		}
//		else {
//			assert (m_Trace.isCallPosition(k) && 
//					!m_Trace.isPendingCall(k));
//			endPos = m_Trace.getReturnPosition(k);
//		}
//		ArrayList<Term> interpolProb = new ArrayList<Term>();
//		ArrayList<Integer> indexTranslation = new ArrayList<Integer>();
//		Term interproceduralLinkPendingCalls = m_SmtManager.getScript().term("true");
//		int j=0;
//		interpolProb.add(j, getFormulaforPos(k));
//		for (int i=k+1; i<= endPos; i++) {
//			Term iFormu = getFormulaforPos(i);
//			if (m_Trace.isPendingCall(i)) {
//				interproceduralLinkPendingCalls = Util.and(m_Script,
//									interproceduralLinkPendingCalls, 
//									m_AnnotSSA.getTerms()[i]);
//			}
//			if (isInterpolatedPosition(i)) {
//				j++;
//				indexTranslation.add(i);
//				interpolProb.add(j,iFormu);
//			}
//			else {
//				Term jFormu = interpolProb.get(j);
//				interpolProb.set(j,Util.and(m_Script,jFormu,iFormu));
//			}
//		}
//		Term lastTerm = interpolProb.get(j);
//		
//		if (k !=0 ) {
//			for (int i = 0; i<k; i++) {
//				if (m_Trace.isPendingCall(i)) {
//					interproceduralLinkPendingCalls = Util.and(m_Script,
//										interproceduralLinkPendingCalls, 
//										m_AnnotSSA.getTerms()[i]);
//				}
//				lastTerm = Util.and(m_Script,lastTerm, getFormulaforPos(i));
//			}
//			for (int i=endPos+1; i<m_AnnotSSA.length(); i++) {
//				if (m_Trace.isPendingCall(i)) {
//					interproceduralLinkPendingCalls = Util.and(m_Script,
//										interproceduralLinkPendingCalls, 
//										m_AnnotSSA.getTerms()[i]);
//				}
//				lastTerm = Util.and(m_Script,lastTerm, getFormulaforPos(i));
//			}
//		}
//		else {
//			lastTerm = Util.and(m_Script,lastTerm, interproceduralLinkPendingCalls);
//		}
//		interpolProb.set(j,lastTerm);
//		assert (interpolProb.size()-1 == indexTranslation.size());
//		
//		Term[] interpolInput = interpolProb.toArray(new Term[0]);
//
//		if (m_IterationPW != null) {
//			String line;
//			line = "=====InterpolationProblem starting from position " + k;
//			s_Logger.debug(line);
//			m_IterationPW.println(line);
////			dumpInterpolationInput(k, interpolInput, indexTranslation, (NestedRun<CodeBlock, Predicate>) m_Run, m_Script, m_IterationPW);
////			SmtManager.dumpInterpolProblem(interpolInput, m_Iteration, k, m_Pref.dumpPath(), m_Script);
//		}
//		Term[] interpolOutput = null;
//		if (interpolInput.length > 1) {
//			interpolOutput = m_SmtManager.computeInterpolants(interpolInput);
//		}
//	
//		
//		if (m_IterationPW != null) {
////			dumpInterpolationOutput(k, interpolOutput, indexTranslation,m_Run.getWord(), m_IterationPW);
//		}
//		
//		for (int jj = 0; jj<indexTranslation.size(); jj++) {
//			m_CraigInterpolants[indexTranslation.get(jj)-1] = interpolOutput[jj];
//		}
//		return false;
//	}
	

//	private Term getFormulaforPos(int i) {
//		Term iFormu;
//		if (m_Trace.isInternalPosition(i)) {
//			iFormu = m_AnnotSSA.getTerms()[i];
//		} else if (m_Trace.isCallPosition(i)) {
//			iFormu = m_SmtManager.getScript().term("true");
//		} else if (m_Trace.isReturnPosition(i)) {
//			iFormu = m_AnnotSSA.getTerms()[i];
//			int callPos = m_Trace.getCallPosition(i);
//			Util.and(m_Script, iFormu, m_AnnotSSA.getTerms()[callPos]);
//		} else {
//			throw new AssertionError();
//		}
//		return iFormu;
//	}	
	

//	//FIXME wrong - fixed?
//	private boolean isInterpolatedPosition(int i) {
//		if (m_InterpolatedPositions == null) {
//			return true;
//		}
//		//interpolate for cutpoint positions
////		if (m_cutpoints.contains(((NestedRun<CodeBlock, Predicate>) m_Run).getStateAtPosition(i).getProgramPoint())) {
////			return true;
////		}
//		//interpolate before calls
//		if (m_Trace.isCallPosition(i)) {
//			return true;
//		}
//		//interpolate after returns
//		if (i>0 && m_Trace.isReturnPosition(i-1)) {
//			return true;
//		}
//		return false;
//	}
	
	
	

	private IPredicate[] computePredicates() {
		IPredicate[] result = new IPredicate[m_Trace.length()-1];
		assert m_CraigInterpolants.length == craigInt2interpolantIndex.size();
//		assert m_InterpolatedPositions.size() == m_CraigInterpolants.length;
		FormulaWalker walker = new FormulaWalker(m_sfmv, m_Script);
		
		Map<Term,IPredicate> withIndices2Predicate =	new HashMap<Term,IPredicate>();
		
		int craigInterpolPos = 0;
		for (int resultPos=0; resultPos<m_Trace.length()-1; resultPos++) {
			int positionOfThisCraigInterpolant;
			if (craigInterpolPos == m_CraigInterpolants.length) {
				// special case where trace ends with return
				// we already added all CraigInterpolants
				// remaining interpolants are "unknown" and the implicit given 
				// false at the end
				assert m_Trace.isReturnPosition(m_Trace.length()-1);
				positionOfThisCraigInterpolant = Integer.MAX_VALUE;
			} else {
				positionOfThisCraigInterpolant = craigInt2interpolantIndex.get(craigInterpolPos);
			}
			assert positionOfThisCraigInterpolant >= resultPos;
			if (isInterpolatedPositio(resultPos)) {
					Term withIndices = m_CraigInterpolants[craigInterpolPos];
					assert resultPos == craigInt2interpolantIndex.get(craigInterpolPos);
					craigInterpolPos++;
					result[resultPos] = withIndices2Predicate.get(withIndices);
					if (result[resultPos] == null) {
						m_sfmv.clearVarsAndProc();
						Term withoutIndices = walker.process(new FormulaUnLet().unlet(withIndices));
						Set<BoogieVar> vars = m_sfmv.getVars();
						String[] procs = m_sfmv.getProcedure().toArray(new String[0]);
						result[resultPos] = m_PredicateBuilder.
								getOrConstructPredicate(withoutIndices, vars, procs);
						withIndices2Predicate.put(withIndices, result[resultPos]);
				}
			} else {
				result[resultPos] = m_SmtManager.newDontCarePredicate(null);
			}
		}
		assert craigInterpolPos == m_CraigInterpolants.length;
		return result;
	}

	



	
	
	
	private static void dumpInterpolationInput(
			int offset,
			Term[] interpolInput,
			List<Integer> indexTranslation,
			NestedRun<CodeBlock,IPredicate> run,
			Script theory,
			PrintWriter pW) {
		String line;
		int indentation = 0;
		int translatedPosition;
		FormulaUnLet unflet = new FormulaUnLet();
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
				line = BasicCegarLoop.addIndentation(indentation, 
						"Location " + translatedPosition + ": " + 
						((SPredicate) run.getStateAtPosition(translatedPosition)).getProgramPoint());
				s_Logger.debug(line);
				pW.println(line);
				if (run.isCallPosition(translatedPosition)) {
					indentation++;
				}
				line = BasicCegarLoop.addIndentation(indentation, 
						unflet.unlet(interpolInput[j]).toString());
				s_Logger.debug(line);
				pW.println(line);
				if (run.isReturnPosition(translatedPosition)) {
					indentation--;
				}
			}
			if (offset != 0) {
				int returnSuccPos = run.getWord().getReturnPosition(offset)+1;
				line = BasicCegarLoop.addIndentation(indentation, 
						"Location " + returnSuccPos + ": " + 
						((SPredicate) run.getStateAtPosition(returnSuccPos)).getProgramPoint());
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
			Term[] interpolOutput,
			List<Integer> indexTranslation,
			Word<CodeBlock> run,
			PrintWriter pW) {
		@SuppressWarnings("unchecked")
		NestedWord<CodeBlock> word = NestedWord.nestedWord(run);
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
				if (translatedPosition>1 && word.isCallPosition(translatedPosition-1)) {
					indentation++;
				}
				line = BasicCegarLoop.addIndentation(indentation, 
						"InterpolOutput"+translatedPosition+": "+interpolOutput[j]);
				s_Logger.debug(line);
				pW.println(line);
				if (word.isReturnPosition(translatedPosition)) {
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
			IPredicate[] stateFormulas,
			Word<CodeBlock> word,
			PrintWriter pW) {
		@SuppressWarnings("unchecked")
		NestedWord<CodeBlock> nw = NestedWord.nestedWord(word);
		assert (stateFormulas.length == word.length()+1);
		String line;
		int indentation = 0;
		try {
			line = "==NestedInterpolants";
			s_Logger.debug(line);
			pW.println(line);
			for (int j=0; j<stateFormulas.length; j++) {
				line = BasicCegarLoop.addIndentation(indentation, 
						j+": "+stateFormulas[j]);
				s_Logger.debug(line);
				pW.println(line);
				if (j!= stateFormulas.length-1) {
					pW.println(word.getSymbol(j));
					if (nw.isCallPosition(j)) {
						indentation++;
					}
					if (nw.isReturnPosition(j)) {
						indentation--;
					}
				}
			}
		} finally {
			pW.flush();
		}
	}
	
	
	private Term conjunction(Term[] formulas) {
		Term result = m_SmtManager.getScript().term("true");
		for (Term f : formulas) {
			result = Util.and(m_Script,result, f);
		}
		return result;
	}
	
}
