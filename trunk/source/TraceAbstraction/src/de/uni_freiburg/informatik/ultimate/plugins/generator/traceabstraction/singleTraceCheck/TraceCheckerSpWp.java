package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.InterproceduralSequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ParallelComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.TransFormula;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.BasicPredicateExplicitQuantifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.EdgeChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.PreferenceInitializer.INTERPOLATION;
import de.uni_freiburg.informatik.ultimate.util.DebugMessage;

public class TraceCheckerSpWp extends TraceChecker {
	/*
	 * Settings for SVComp:
	 * m_useUnsatCore = true;
	 * m_useUnsatCoreOfFineGranularity = true;
	 * m_useLiveVariables = true;
	 * m_LogInformation = false;
	 * m_CollectInformationAboutQuantifiedPredicates = false;
	 * m_ComputeInterpolantsSp = true;
	 * m_ComputeInterpolantsFp = true;
	 * m_ComputeInterpolantsBp = false;
	 * m_ComputeInterpolantsWp = false;
	 */
	
	
	protected IPredicate[] m_InterpolantsSp;
	protected IPredicate[] m_InterpolantsWp;
	
	// Forward relevant predicates
	protected IPredicate[] m_InterpolantsFp;
	// Backward relevant predicates
	protected IPredicate[] m_InterpolantsBp;
	
	
	private final static boolean m_useUnsatCore = true;
	private final static boolean m_useUnsatCoreOfFineGranularity = true;
	private final static boolean m_useLiveVariables = true;
	private final static boolean m_LogInformation = true;
	private final static boolean m_CollectInformationAboutQuantifiedPredicates = true;
	// m_NumberOfQuantifierFreePredicates[0] : #quantified predicates of SP
	// m_NumberOfQuantifierFreePredicates[1] : #quantified predicates of FP
	// m_NumberOfQuantifierFreePredicates[2] : #quantified predicates of WP
	// m_NumberOfQuantifierFreePredicates[3] : #quantified predicates of BP
	private int[] m_NumberOfQuantifiedPredicates;
	private boolean m_ComputeInterpolantsSp;
	private boolean m_ComputeInterpolantsFp;
	private boolean m_ComputeInterpolantsBp;
	private boolean m_ComputeInterpolantsWp;
	
	public TraceCheckerSpWp(IPredicate precondition, IPredicate postcondition,
			NestedWord<CodeBlock> trace, SmtManager smtManager,
			ModifiableGlobalVariableManager modifiedGlobals) {
		super(precondition, postcondition, null, trace, smtManager, modifiedGlobals);
		m_NumberOfQuantifiedPredicates = new int[4];
	}

	@Override
	public void computeInterpolants(Set<Integer> interpolatedPositions, 
			PredicateUnifier predicateUnifier, INTERPOLATION interpolation) {
		switch (interpolation) {
			case ForwardPredicates:
				m_ComputeInterpolantsSp = true;
				m_ComputeInterpolantsFp = true;
				m_ComputeInterpolantsWp = false;
				m_ComputeInterpolantsBp = false;
				break;
			case BackwardPredicates:
				m_ComputeInterpolantsSp = false;
				m_ComputeInterpolantsFp = false;
				m_ComputeInterpolantsWp = true;
				m_ComputeInterpolantsBp = true;
				break;
			case FPandSP:
				m_ComputeInterpolantsSp = true;
				m_ComputeInterpolantsFp = true;
				m_ComputeInterpolantsWp = true;
				m_ComputeInterpolantsBp = true;
				break;
			default:
				throw new UnsupportedOperationException("unsupportedInterpolation");
			}
		m_PredicateUnifier = predicateUnifier;
		
		if (m_useUnsatCore) {
			computeInterpolantsWithUsageOfUnsatCore(interpolatedPositions);
		} else {
			computeInterpolantsWithoutUsageOfUnsatCore(interpolatedPositions);
		}
	}
	
	public IPredicate getInterpolanstsSPAtPosition(int i) {
		assert m_InterpolantsSp != null : "InterpolantsSP hasn't been computed, yet.";
		assert i >= 0 && i < m_InterpolantsSp.length : ("The given position "+ i
				+ " is not a correct position. #Interpolants = " 
				+ m_InterpolantsSp.length);
		return m_InterpolantsSp[i];
	}
	
	public IPredicate getInterpolanstsWPAtPosition(int i) {
		assert m_InterpolantsWp != null : "InterpolantsWP hasn't been computed, yet.";
		assert i >= 0 && i < m_InterpolantsWp.length : "The given position "+ i + " is not a correct position!";
		return m_InterpolantsWp[i];
	}
	
	
	/**
	 * Computes the sequential composition of the statements from the given trace, where the trace doesn't contain
	 * Calls or Returns.
	 */
	private TransFormula computeSummaryForTrace(Word<CodeBlock> trace, RelevantTransFormulas rv, int offset) {
		TransFormula[] transFormulasToComputeSummaryFor = new TransFormula[trace.length()];
		for (int i = 0; i < trace.length(); i++) {
			if (trace.getSymbol(i) instanceof Call) {
				transFormulasToComputeSummaryFor[i] = rv.getLocalVarAssignment(i+offset);
			} else {
				transFormulasToComputeSummaryFor[i] = rv.getFormulaFromNonCallPos(i+offset);
			}
		}
		return TransFormula.sequentialComposition(m_SmtManager.getBoogie2Smt(), true, false, transFormulasToComputeSummaryFor);
	}
	
	private TransFormula computeSummaryForTrace(Word<CodeBlock> trace, TransFormula Call, 
			TransFormula Return, 
			TransFormula oldVarsAssignment,
			RelevantTransFormulas rv,
			int call_pos) {
		TransFormula procedureSummary = computeSummaryForTrace(trace, rv, call_pos);
		return TransFormula.sequentialCompositionWithCallAndReturn(m_SmtManager.getBoogie2Smt(), true, false, Call, oldVarsAssignment, procedureSummary, Return);
	}
	
	
	public boolean interpolantsSPComputed() {
		return m_ComputeInterpolantsSp;
	}

	public boolean interpolantsWPComputed() {
		return m_ComputeInterpolantsWp;
	}

	private void computeInterpolantsWithUsageOfUnsatCore(Set<Integer> interpolatedPositions) {
		m_NumberOfQuantifiedPredicates = new int[4];
		
		Term[] unsat_core = m_SmtManager.getScript().getUnsatCore();
		
		Set<Term> unsat_coresAsSet = new HashSet<Term>(Arrays.asList(unsat_core));
		
		if (!(interpolatedPositions instanceof AllIntegers)) {
			throw new UnsupportedOperationException();
		}
		IPredicate tracePrecondition = m_Precondition;
		IPredicate tracePostcondition = m_Postcondition;
		m_PredicateUnifier.declarePredicate(tracePrecondition);
		m_PredicateUnifier.declarePredicate(tracePostcondition);
		NestedWord<CodeBlock> trace = m_Trace;
		unlockSmtManager();
		RelevantTransFormulas rv = null;
		
		if (m_LogInformation) {
			if (m_AAA instanceof AnnotateAndAsserterConjuncts) {
				int totalNumberOfConjunctsInTrace = ((AnnotateAndAsserterConjuncts)m_AAA).getAnnotated2Original().keySet().size();
				s_Logger.debug("Total number of conjuncts in trace: " +  totalNumberOfConjunctsInTrace);
				s_Logger.debug("Number of conjuncts in unsatisfiable core: " + unsat_coresAsSet.size());
			}
		}
		
		if (!m_useUnsatCoreOfFineGranularity) {
			boolean[] localVarAssignmentAtCallInUnsatCore = new boolean[trace.length()];
			boolean[] oldVarAssignmentAtCallInUnsatCore = new boolean[trace.length()];
			// Filter out the statements, which doesn't occur in the unsat core.
			Set<CodeBlock> codeBlocksInUnsatCore = filterOutIrrelevantStatements(trace, unsat_coresAsSet, 
					localVarAssignmentAtCallInUnsatCore, 
					oldVarAssignmentAtCallInUnsatCore);
			rv = new RelevantTransFormulas(trace,
					m_Precondition, m_Postcondition, m_PendingContexts,
					codeBlocksInUnsatCore,
					m_ModifiedGlobals,
					localVarAssignmentAtCallInUnsatCore,
					oldVarAssignmentAtCallInUnsatCore,
					m_SmtManager);
		} else {
			rv = new RelevantTransFormulas(trace,
					m_Precondition, m_Postcondition, m_PendingContexts,
					unsat_coresAsSet,
					m_ModifiedGlobals,
					m_SmtManager,
					(AnnotateAndAsserterConjuncts)m_AAA);
			assert stillInfeasible(rv);
		}
		Set<BoogieVar>[] relevantVarsToUseForFPBP = null;
		
		if (m_useLiveVariables) {
			LiveVariables lvar = new LiveVariables(m_Nsb.getVariable2Constant(), m_Nsb.getConstants2BoogieVar(),
					m_Nsb.getIndexedVarRepresentative(),
					m_SmtManager, m_ModifiedGlobals);
			relevantVarsToUseForFPBP = lvar.getLiveVariables();
		} else {
			RelevantVariables rvar = new RelevantVariables(rv);
			relevantVarsToUseForFPBP = rvar.getRelevantVariables();
		}
		
		
		if (m_ComputeInterpolantsFp) {
			s_Logger.debug("Computing forward relevant predicates...");
			computeForwardRelevantPredicates(relevantVarsToUseForFPBP, rv, trace, tracePrecondition);
			s_Logger.debug("Checking inductivity of forward relevant predicates...");
			assert checkInterpolantsCorrect(m_InterpolantsFp, trace, tracePrecondition,
					tracePostcondition, "FP") : "invalid Hoare triple in FP";
		}
		
		if (m_LogInformation) {
			s_Logger.debug("Length of trace:" + trace.length());
//			new DebugMessage("#quantifiedPredicates in SP: {0}", m_NumberOfQuantifiedPredicates[0]);
			s_Logger.debug("#quantifiedPredicates in SP: " + m_NumberOfQuantifiedPredicates[0]);
			s_Logger.debug("#quantifiedPredicates in FP: " + m_NumberOfQuantifiedPredicates[1]);
		}
		
		if (m_ComputeInterpolantsSp && !m_ComputeInterpolantsFp) {
			m_InterpolantsSp = new IPredicate[trace.length()-1];

			s_Logger.debug("Computing strongest postcondition for given trace ...");
			
			if (trace.length() > 1) {
				if (trace.getSymbol(0) instanceof Call) {
					IPredicate p = m_SmtManager.strongestPostcondition(tracePrecondition,
							rv.getLocalVarAssignment(0),
							rv.getGlobalVarAssignment(0),
							rv.getOldVarAssignment(0),
							trace.isPendingCall(0));							
					m_InterpolantsSp[0] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(), p.getVars(),
							p.getProcedures());
				} else {
					IPredicate p = m_SmtManager.strongestPostcondition(tracePrecondition,
							rv.getFormulaFromNonCallPos(0));
					m_InterpolantsSp[0] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(), p.getVars(),
							p.getProcedures());
				}
			}

			for (int i=1; i<m_InterpolantsSp.length; i++) {
				if (trace.getSymbol(i) instanceof Call) {
					IPredicate p = m_SmtManager.strongestPostcondition(m_InterpolantsSp[i-1],
							rv.getLocalVarAssignment(i),
							rv.getGlobalVarAssignment(i),
							rv.getOldVarAssignment(i),
							((NestedWord<CodeBlock>) trace).isPendingCall(i));
						m_InterpolantsSp[i] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(), p.getVars(),
								p.getProcedures());
				} else if (trace.getSymbol(i) instanceof Return) {
						int call_pos = ((NestedWord<CodeBlock>)trace).getCallPosition(i);
						assert call_pos >= 0 && call_pos <= i : "Bad call position!";
						IPredicate callerPred = tracePrecondition;
						if (call_pos > 0) {
							callerPred = m_InterpolantsSp[call_pos - 1];
						}
						IPredicate p = m_SmtManager.strongestPostcondition(m_InterpolantsSp[i-1], 
								callerPred,
								rv.getFormulaFromNonCallPos(i),
								rv.getLocalVarAssignment(call_pos),
								rv.getGlobalVarAssignment(call_pos)
								);
						m_InterpolantsSp[i] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(), p.getVars(),
								p.getProcedures());

				} else {
						IPredicate p = m_SmtManager.strongestPostcondition(m_InterpolantsSp[i-1],
								rv.getFormulaFromNonCallPos(i));
						m_InterpolantsSp[i] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(), p.getVars(),
								p.getProcedures());
				}
			}
			s_Logger.debug("Checking strongest postcondition...");
			assert checkInterpolantsCorrect(m_InterpolantsSp, trace, tracePrecondition, 
					tracePostcondition, "SP with unsat core") : "invalid Hoare triple in SP with unsat core";
			
		}
		if (m_ComputeInterpolantsWp) {
			m_InterpolantsWp = new IPredicate[trace.length()-1];
			// Contains the predicates, which are computed during a Return with the second method, where the callerPred
			// is computed as wp(returnerPred, summaryOfCalledProcedure).
			Map<Integer, IPredicate> callerPredicatesComputed = new HashMap<Integer, IPredicate>();
			s_Logger.debug("Computing weakest precondition for given trace ...");
			if (trace.length() > 1) {
				if (trace.getSymbol(m_InterpolantsWp.length) instanceof Call) {
					// If the trace contains a Call statement, then it must be a NestedWord
					NestedWord<CodeBlock> traceAsNW = ((NestedWord<CodeBlock>) trace);
					IPredicate p = m_SmtManager.weakestPrecondition(
							tracePostcondition, 
							rv.getLocalVarAssignment(m_InterpolantsWp.length),
							rv.getGlobalVarAssignment(m_InterpolantsWp.length),
							rv.getOldVarAssignment(m_InterpolantsWp.length),
							traceAsNW.isPendingCall(m_InterpolantsWp.length));
					m_InterpolantsWp[m_InterpolantsWp.length-1] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(),
							p.getVars(), p.getProcedures());

				} else if (trace.getSymbol(m_InterpolantsWp.length) instanceof Return) {
					int call_pos = ((NestedWord<CodeBlock>)trace).getCallPosition(m_InterpolantsWp.length);
					IPredicate callerPred = null;
					TransFormula callTF = rv.getLocalVarAssignment(call_pos);
					TransFormula globalVarsAssignments = rv.getGlobalVarAssignment(call_pos);
					if ((m_InterpolantsWp.length - call_pos) >= call_pos) {
						TransFormula summary = computeSummaryForTrace(getSubTrace(0, call_pos, trace), rv, 0);
						callerPred = m_SmtManager.strongestPostcondition(m_Precondition, summary);
						// If callerPred contains quantifier, compute it via the 2nd method
						if(callerPred instanceof BasicPredicateExplicitQuantifier) {
							summary = computeSummaryForTrace(getSubTrace(call_pos, m_InterpolantsWp.length - 1, trace), callTF,
									rv.getFormulaFromNonCallPos(m_InterpolantsWp.length), 
									globalVarsAssignments,
									rv, call_pos);
							callerPred = m_SmtManager.weakestPrecondition(m_Postcondition, summary);
						}
					} else {
						// If the sub-trace between call_pos and returnPos (here: i) is shorter, than compute the
						// callerPred in this way.
						TransFormula summary = computeSummaryForTrace(getSubTrace(call_pos, m_InterpolantsWp.length - 1, trace), callTF,
								rv.getFormulaFromNonCallPos(m_InterpolantsWp.length), 
								globalVarsAssignments,
								rv, call_pos);
						callerPred = m_SmtManager.weakestPrecondition(m_Postcondition, summary);
					}
					callerPredicatesComputed.put(call_pos, callerPred);
					IPredicate p = m_SmtManager.weakestPrecondition(tracePostcondition,
							callerPred, 
							rv.getFormulaFromNonCallPos(m_InterpolantsWp.length),
							callTF, globalVarsAssignments);
					m_InterpolantsWp[m_InterpolantsWp.length-1] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(),
							p.getVars(), p.getProcedures());
				}
				else {
					IPredicate p = m_SmtManager.weakestPrecondition(
							tracePostcondition, rv.getFormulaFromNonCallPos(m_InterpolantsWp.length));
					m_InterpolantsWp[m_InterpolantsWp.length-1] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(),
							p.getVars(), p.getProcedures());
				}
			}
			for (int i=m_InterpolantsWp.length-2; i>=0; i--) {
				if (trace.getSymbol(i+1) instanceof Call) {
					if (callerPredicatesComputed.containsKey(i+1)) {
						IPredicate p = callerPredicatesComputed.get(i+1);
						m_InterpolantsWp[i] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(),
								p.getVars(), p.getProcedures());
					} else {
						IPredicate p = m_SmtManager.weakestPrecondition(
								m_InterpolantsWp[i+1], 
								rv.getLocalVarAssignment(i+1),
								rv.getGlobalVarAssignment(i+1),
								rv.getOldVarAssignment(i+1),
								true);
						m_InterpolantsWp[i] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(),
								p.getVars(), p.getProcedures());
						
					}
				} else if (trace.getSymbol(i+1) instanceof Return) {
					int call_pos = ((NestedWord<CodeBlock>)trace).getCallPosition(i+1);
					IPredicate callerPred = null;
					TransFormula callTF = rv.getLocalVarAssignment(call_pos);
					TransFormula globalVarsAssignments = rv.getGlobalVarAssignment(call_pos);
					
					TransFormula summary = computeSummaryForTrace(getSubTrace(0, call_pos, trace), rv, 0);
					callerPred = m_SmtManager.strongestPostcondition(m_Precondition, summary);
					// If callerPred contains quantifier, compute it via the 2nd method
					if(callerPred instanceof BasicPredicateExplicitQuantifier) {
						summary = computeSummaryForTrace(getSubTrace(call_pos, i, trace), callTF,
								rv.getFormulaFromNonCallPos(i+1), 
								globalVarsAssignments,
								rv, call_pos);
						callerPred = m_SmtManager.weakestPrecondition(m_InterpolantsWp[i+1], 
								summary);
					}
					callerPredicatesComputed.put(call_pos, callerPred);
					IPredicate p = m_SmtManager.weakestPrecondition(
							m_InterpolantsWp[i+1], 
							callerPred, 
							rv.getFormulaFromNonCallPos(i+1), callTF, 
							globalVarsAssignments); 
					m_InterpolantsWp[i] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(),
							p.getVars(), p.getProcedures());
				} else {
					IPredicate p = m_SmtManager.weakestPrecondition(
							m_InterpolantsWp[i+1], rv.getFormulaFromNonCallPos(i+1));
					m_InterpolantsWp[i] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(),
							p.getVars(), p.getProcedures());
				}
			}

			s_Logger.debug("Checking weakest precondition...");
			assert checkInterpolantsCorrect(m_InterpolantsWp, trace, tracePrecondition,
					tracePostcondition, "WP with unsat core") : "invalid Hoare triple in WP with unsat core";
			if (m_ComputeInterpolantsBp) {
				s_Logger.debug("Computing backward relevant predicates...");
				computeBackwardRelevantPredicates(relevantVarsToUseForFPBP);
				s_Logger.debug("Checking inductivity of backward relevant predicates...");
				assert checkInterpolantsCorrect(m_InterpolantsBp, trace, tracePrecondition,
						tracePostcondition, "BP") : "invalid Hoare triple in BP";
			}

		}
		if (m_ComputeInterpolantsSp && m_ComputeInterpolantsWp) {
			checkSPImpliesWP(m_InterpolantsSp, m_InterpolantsWp);
		}
		if (m_ComputeInterpolantsFp && m_ComputeInterpolantsBp) {
			selectInterpolantsOfBothType();
		} else if (m_ComputeInterpolantsFp) {
			m_Interpolants = m_InterpolantsFp;
		} else if (m_ComputeInterpolantsSp) {
			m_Interpolants = m_InterpolantsSp;
		} else {
			assert m_InterpolantsWp != null;
			m_Interpolants = m_InterpolantsWp;
		}
	}
	
	private void selectInterpolantsOfBothType() {
		assert m_InterpolantsFp.length == m_InterpolantsBp.length;
		m_Interpolants = new IPredicate[m_InterpolantsBp.length];
		int i = 0; // position of predicate computed by strongest post-condition
		int j = m_InterpolantsBp.length; // position of predicate computed by weakest precondition
		while (i != j) {
			if (!(m_InterpolantsBp[j-1] instanceof BasicPredicateExplicitQuantifier)) {
				m_Interpolants[j-1] = m_InterpolantsBp[j-1];
				j--;
			} else if (!(m_InterpolantsFp[i] instanceof BasicPredicateExplicitQuantifier)) {
				m_Interpolants[i] = m_InterpolantsFp[i];
				i++;
			} else {
				int numOfQuantifiedVarsInFp = ((BasicPredicateExplicitQuantifier) m_InterpolantsFp[i]).getQuantifiedVariables().size();
				int numOfQuantifiedVarsInBp = ((BasicPredicateExplicitQuantifier) m_InterpolantsBp[j-1]).getQuantifiedVariables().size();
				if (numOfQuantifiedVarsInFp < numOfQuantifiedVarsInBp) {
					m_Interpolants[i] = m_InterpolantsFp[i];
					i++;
				} else {
					m_Interpolants[j-1] = m_InterpolantsBp[j-1];
					j--;
				}
			}
		}
	}
	
	
	
	@Deprecated
	private boolean formulaContainsExistentialQuantifier(Term formula) {
		if (formula instanceof ApplicationTerm) {
			Term[] parameters = ((ApplicationTerm) formula).getParameters();
			for (int i = 0; i < parameters.length; i++) {
				if (formulaContainsExistentialQuantifier(parameters[i])) {
					return true;
				}
			}
		} else if (formula instanceof QuantifiedFormula) {
			if (((QuantifiedFormula) formula).getQuantifier() == QuantifiedFormula.EXISTS) {
				return true;
			} else {
				return false;
			}
		}
		return false;
	}
	
	
	/**
	 * TODO: documentation
	 */
	private boolean stillInfeasible(RelevantTransFormulas rv) {
		TraceChecker tc = new TraceChecker(rv.getPrecondition(), 
				rv.getPostcondition(), null, rv.getTrace(), m_SmtManager, m_ModifiedGlobals);
		tc.unlockSmtManager();
		boolean result = (tc.isCorrect() == LBool.UNSAT);
		return result;
	}
	
	private Set<CodeBlock> filterOutIrrelevantStatements(NestedWord<CodeBlock> trace, Set<Term> unsat_coresAsSet,
			boolean[] localVarAssignmentAtCallInUnsatCore,
			boolean[] oldVarAssignmentAtCallInUnsatCore ) {
		Set<CodeBlock> codeBlocksInUnsatCore = new HashSet<CodeBlock>();
		for (int i = 0; i < trace.length(); i++) {
			if (!trace.isCallPosition(i) && unsat_coresAsSet.contains(m_AAA.getAnnotatedSsa().getFormulaFromNonCallPos(i))) {
				codeBlocksInUnsatCore.add(trace.getSymbol(i));
			} else if (trace.isCallPosition(i) && 
					(unsat_coresAsSet.contains(m_AAA.getAnnotatedSsa().getGlobalVarAssignment(i))
							|| unsat_coresAsSet.contains(m_AAA.getAnnotatedSsa().getOldVarAssignment(i)))) {
				// The upper condition checks, whether the globalVarAssignments
				// is in unsat core, now check whether the local variable assignments
				// is in unsat core, if it is Call statement
					// Check whether the local variable assignments are also in unsat core.
				if (unsat_coresAsSet.contains(m_AAA.getAnnotatedSsa().getLocalVarAssignment(i))) {
					localVarAssignmentAtCallInUnsatCore[i] = true;
				}
				if (unsat_coresAsSet.contains(m_AAA.getAnnotatedSsa().getOldVarAssignment(i))) {
					oldVarAssignmentAtCallInUnsatCore[i] = true;
				}
				// Add the globalVarAssignments to the unsat_core, if it is a Call statement, otherwise it adds
				// the statement
				codeBlocksInUnsatCore.add(trace.getSymbol(i));
			} else {
				if (trace.getSymbol(i) instanceof Call) {
					if (unsat_coresAsSet.contains(m_AAA.getAnnotatedSsa().getLocalVarAssignment(i))) {
						localVarAssignmentAtCallInUnsatCore[i] = true;
					}
				}
			}
		}
		return codeBlocksInUnsatCore;
	}

	private void computeForwardRelevantPredicates(Set<BoogieVar>[] relevantVars) {
		assert m_InterpolantsSp != null : "Interpolants SP_i have not been computed!";
		m_InterpolantsFp = new IPredicate[m_InterpolantsSp.length];
		for (int i = 0; i < m_InterpolantsSp.length; i++) {
			IPredicate p = m_SmtManager.computeForwardRelevantPredicate(m_InterpolantsSp[i], relevantVars[i+1]);
			m_InterpolantsFp[i] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(),
					p.getVars(), p.getProcedures());
		}
	}
	
	/**
	 * Compute forward relevant predicates for each position directly after the strongest post-condition has been
	 * computed. Formally, we have
	 * FP[i] = EXISTS irrelevantVars[i]. strongest-post(FP[i-1], relevantTransformulas[i]) 
	 */
	private void computeForwardRelevantPredicates(Set<BoogieVar>[] relevantVars, RelevantTransFormulas rv,
			NestedWord<CodeBlock> trace,
			IPredicate tracePrecondition) {
		m_InterpolantsSp = new IPredicate[trace.length() - 1];
		m_InterpolantsFp = new IPredicate[m_InterpolantsSp.length];
		
		if (trace.length() > 1) {
			IPredicate sp = null;
			if (trace.getSymbol(0) instanceof Call) {
				IPredicate p = m_SmtManager.strongestPostcondition(tracePrecondition,
						rv.getLocalVarAssignment(0),
						rv.getGlobalVarAssignment(0),
						rv.getOldVarAssignment(0),
						trace.isPendingCall(0));							
				m_InterpolantsSp[0] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(), p.getVars(),
						p.getProcedures());
			} else {
				sp = m_SmtManager.strongestPostcondition(tracePrecondition,
						rv.getFormulaFromNonCallPos(0));
				m_InterpolantsSp[0] = m_PredicateUnifier.getOrConstructPredicate(sp.getFormula(), sp.getVars(),
						sp.getProcedures());
			}
			IPredicate fp = m_SmtManager.computeForwardRelevantPredicate(m_InterpolantsSp[0], relevantVars[1]);
			m_InterpolantsFp[0] = m_PredicateUnifier.getOrConstructPredicate(fp.getFormula(), fp.getVars(), fp.getProcedures());
			if (m_CollectInformationAboutQuantifiedPredicates) {
				if (sp instanceof BasicPredicateExplicitQuantifier) {
					m_NumberOfQuantifiedPredicates[0]++;
				}
				if (fp instanceof BasicPredicateExplicitQuantifier) {
					m_NumberOfQuantifiedPredicates[1]++;
				}
			}
		}
		
		for (int i=1; i<m_InterpolantsSp.length; i++) {
			IPredicate sp = null;
			if (trace.getSymbol(i) instanceof Call) {
				 sp = m_SmtManager.strongestPostcondition(m_InterpolantsFp[i-1],
						rv.getLocalVarAssignment(i),
						rv.getGlobalVarAssignment(i),
						rv.getOldVarAssignment(i),
						((NestedWord<CodeBlock>) trace).isPendingCall(i));
					m_InterpolantsSp[i] = m_PredicateUnifier.getOrConstructPredicate(sp.getFormula(), sp.getVars(),
							sp.getProcedures());
			} else if (trace.getSymbol(i) instanceof Return) {
					int call_pos = ((NestedWord<CodeBlock>)trace).getCallPosition(i);
					assert call_pos >= 0 && call_pos <= i : "Bad call position!";
					IPredicate callerPred = tracePrecondition;
					if (call_pos > 0) {
						callerPred = m_InterpolantsFp[call_pos - 1];
					}
					sp = m_SmtManager.strongestPostcondition(m_InterpolantsFp[i-1], 
							callerPred,
							rv.getFormulaFromNonCallPos(i),
							rv.getLocalVarAssignment(call_pos),
							rv.getGlobalVarAssignment(call_pos)
							);
					m_InterpolantsSp[i] = m_PredicateUnifier.getOrConstructPredicate(sp.getFormula(), sp.getVars(),
							sp.getProcedures());

			} else {
					sp = m_SmtManager.strongestPostcondition(m_InterpolantsFp[i-1],
							rv.getFormulaFromNonCallPos(i));
					m_InterpolantsSp[i] = m_PredicateUnifier.getOrConstructPredicate(sp.getFormula(), sp.getVars(),
							sp.getProcedures());
			}
			IPredicate fp = m_SmtManager.computeForwardRelevantPredicate(m_InterpolantsSp[i], relevantVars[i+1]);
			m_InterpolantsFp[i] = m_PredicateUnifier.getOrConstructPredicate(fp.getFormula(), fp.getVars(), fp.getProcedures());
			if (m_CollectInformationAboutQuantifiedPredicates) {
				if (sp != null && sp instanceof BasicPredicateExplicitQuantifier) {
					m_NumberOfQuantifiedPredicates[0]++;
				}
				if (fp instanceof BasicPredicateExplicitQuantifier) {
					m_NumberOfQuantifiedPredicates[1]++;
				}
			}
		}
		
	}
	
	
	private void computeBackwardRelevantPredicates(Set<BoogieVar>[] relevantVars) {
		assert m_InterpolantsWp != null : "Interpolants WP_i have not been computed!";
		m_InterpolantsBp = new IPredicate[m_InterpolantsWp.length];
		for (int i = 0; i < m_InterpolantsWp.length; i++) {
			IPredicate p = m_SmtManager.computeBackwardRelevantPredicate(m_InterpolantsWp[i], relevantVars[i+1]);
			m_InterpolantsBp[i]  = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(),
					p.getVars(), p.getProcedures());
		}
	}
	
	private void checkSPImpliesWP(IPredicate[] interpolantsSP, IPredicate[] interpolantsWP) {
		s_Logger.debug("Checking implication of SP and WP...");
		for (int i = 0; i < interpolantsSP.length; i++) {
			LBool result = m_SmtManager.isCovered(interpolantsSP[i], interpolantsWP[i]);
			s_Logger.debug("SP {" + interpolantsSP[i] + "} ==> WP {" + interpolantsWP[i] + "} is " + 
						(result == LBool.UNSAT ? "valid" :
						(result == LBool.SAT ? "not valid" : result)));
			assert(result == LBool.UNSAT || result == LBool.UNKNOWN) : "checkSPImpliesWP failed";	
		}
	}
	
	/**
	 * Returns a sub-trace of the given trace, from startPos to endPos.
	 */
 	private Word<CodeBlock> getSubTrace(int startPos, int endPos, Word<CodeBlock> trace) {
		CodeBlock[] codeBlocks = new CodeBlock[endPos - startPos];
		for (int i = startPos; i < endPos; i++) {
			codeBlocks[i - startPos] = trace.getSymbol(i);
		}
		return new Word<CodeBlock>(codeBlocks);
	}
	
 	@Deprecated
	private void computeInterpolantsWithoutUsageOfUnsatCore(Set<Integer> interpolatedPositions) {
		if (!(interpolatedPositions instanceof AllIntegers)) {
			throw new UnsupportedOperationException();
		}
		IPredicate tracePrecondition = m_Precondition;
		IPredicate tracePostcondition = m_Postcondition;
		m_PredicateUnifier.declarePredicate(tracePrecondition);
		m_PredicateUnifier.declarePredicate(tracePostcondition);
		
		Word<CodeBlock> trace = m_Trace;
		
		unlockSmtManager();
		
		if (m_ComputeInterpolantsSp) {
			m_InterpolantsSp = new IPredicate[trace.length()-1];
			if (trace.length() == 1) {
				m_Interpolants = m_InterpolantsSp;
				return;
			}
			s_Logger.debug("Computing strongest postcondition for given trace ...");

			if (trace.getSymbol(0) instanceof Call) {
				IPredicate p = m_SmtManager.strongestPostcondition(
						tracePrecondition, (Call) trace.getSymbol(0),
						((NestedWord<CodeBlock>) trace).isPendingCall(0));
				m_InterpolantsSp[0] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(), p.getVars(),
						p.getProcedures());
			} else {
				IPredicate p = m_SmtManager.strongestPostcondition(
						tracePrecondition, trace.getSymbol(0));
				m_InterpolantsSp[0] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(), p.getVars(),
						p.getProcedures());
			}
			for (int i=1; i<m_InterpolantsSp.length; i++) {
				if (trace.getSymbol(i) instanceof Call) {
//					if (trace.length() == 19) {
//						int test = 0;
//					}
					IPredicate p = m_SmtManager.strongestPostcondition(
							m_InterpolantsSp[i-1], (Call) trace.getSymbol(i),
							((NestedWord<CodeBlock>) trace).isPendingCall(i));
					m_InterpolantsSp[i] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(), p.getVars(),
							p.getProcedures());
				} else if (trace.getSymbol(i) instanceof Return) {
//					if (trace.length() == 19 && i >= 3) {
//						int test = 0;
//					}
					int call_pos = ((NestedWord<CodeBlock>)trace).getCallPosition(i);
					assert call_pos >= 0 && call_pos <= i : "Bad call position!";
					IPredicate callerPred = tracePrecondition;
					if (call_pos > 0) {
						callerPred = m_InterpolantsSp[call_pos - 1];
					}
					IPredicate p = m_SmtManager.strongestPostcondition(
							m_InterpolantsSp[i-1], callerPred, (Return) trace.getSymbol(i));
					m_InterpolantsSp[i] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(), p.getVars(),
							p.getProcedures());
					
				
				} else {
					IPredicate p = m_SmtManager.strongestPostcondition(
							m_InterpolantsSp[i-1],trace.getSymbol(i));
					m_InterpolantsSp[i] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(), p.getVars(),
							p.getProcedures());
				}
			}
			s_Logger.debug("Checking strongest postcondition...");
			assert checkInterpolantsCorrect(m_InterpolantsSp, trace, tracePrecondition, 
					tracePostcondition, "sp without unsat core") : "invalid Hoare triple in sp without unsat core";
		}

		if (m_ComputeInterpolantsWp) {
			m_InterpolantsWp = new IPredicate[trace.length()-1];
//			if (trace.length() == 1) {
//				m_Interpolants = m_InterpolantsWp;
//				return;
//			}
//			s_Logger.debug("Computing weakest precondition for given trace ...");
//			if (trace.getSymbol(m_InterpolantsWp.length) instanceof Call) {
//				// If the trace contains a Call statement, then it must be a NestedWord
//				NestedWord<CodeBlock> traceAsNW = ((NestedWord<CodeBlock>) trace);
//				int retPos = traceAsNW.getReturnPosition(m_InterpolantsWp.length);
//				IPredicate returnerPred = tracePostcondition;
//				if (retPos < m_InterpolantsWp.length) {
//					returnerPred = m_InterpolantsWp[retPos];
//				}
//				IPredicate p = m_SmtManager.weakestPrecondition(
//						tracePostcondition, returnerPred,
//						(Call) trace.getSymbol(m_InterpolantsWp.length),
//						(Return) trace.getSymbol(retPos) ,
//						traceAsNW.isPendingCall(m_InterpolantsWp.length));
//				m_InterpolantsWp[m_InterpolantsWp.length-1] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(),
//						p.getVars(), p.getProcedures());
//			} else if (trace.getSymbol(m_InterpolantsWp.length) instanceof Return) {
//				int call_pos = ((NestedWord<CodeBlock>)trace).getCallPosition(m_InterpolantsWp.length);
//				TransFormula summary = computeSummaryForTrace(getSubTrace(0, call_pos, trace));
//				IPredicate callerPred = m_SmtManager.strongestPostcondition(m_Precondition, summary);
//				// If the sub-trace between call_pos and returnPos (here: i) is shorter, than compute the
//				// callerPred in this way.
//				TransFormula callTF = ((Return) trace.getSymbol(m_InterpolantsWp.length)).getCorrespondingCall().getTransitionFormula();
//				TransFormula globalVarsAssignments = m_ModifiedGlobals.getGlobalVarsAssignment(((Return) trace.getSymbol(m_InterpolantsWp.length)).getCorrespondingCall().getCallStatement().getMethodName());
//				if ((m_InterpolantsWp.length - call_pos) < call_pos) {
//					summary = computeSummaryForTrace(getSubTrace(call_pos, m_InterpolantsWp.length - 1, trace), callTF,
//							trace.getSymbol(m_InterpolantsWp.length).getTransitionFormula(), globalVarsAssignments);
//					callerPred = m_SmtManager.weakestPrecondition(m_Postcondition, summary);
//				}
//				IPredicate p = m_SmtManager.weakestPrecondition(tracePostcondition,
//						callerPred, trace.getSymbol(m_InterpolantsWp.length).getTransitionFormula(),
//						callTF, globalVarsAssignments);
//				m_InterpolantsWp[m_InterpolantsWp.length-1] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(),
//						p.getVars(), p.getProcedures());
//			} else {
//				IPredicate p = m_SmtManager.weakestPrecondition(
//						tracePostcondition, trace.getSymbol(m_InterpolantsWp.length));
//				m_InterpolantsWp[m_InterpolantsWp.length-1] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(),
//						p.getVars(), p.getProcedures());
//			}
//
//			for (int i=m_InterpolantsWp.length-2; i>=0; i--) {
//				if (trace.getSymbol(i+1) instanceof Call) {
//					NestedWord<CodeBlock> traceAsNW = (NestedWord<CodeBlock>) trace;					
//					int retPos = traceAsNW.getReturnPosition(i+1);
//					IPredicate returnerPred = tracePostcondition;
//					if (retPos < m_InterpolantsWp.length) {
//						returnerPred = m_InterpolantsWp[retPos];
//					}
//					IPredicate p = m_SmtManager.weakestPrecondition(
//							m_InterpolantsWp[i+1], returnerPred, 
//							(Call) trace.getSymbol(i+1),
//							(Return) trace.getSymbol(retPos),
//							traceAsNW.isPendingCall(i+1));
//					m_InterpolantsWp[i] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(),
//							p.getVars(), p.getProcedures());
//				} else if (trace.getSymbol(i+1) instanceof Return) {
//					int call_pos = ((NestedWord<CodeBlock>)trace).getCallPosition(i+1);
//					TransFormula summary = computeSummaryForTrace(getSubTrace(0, call_pos, trace));
//					IPredicate callerPred = m_SmtManager.strongestPostcondition(m_Precondition, summary);
//					// If the sub-trace between call_pos and returnPos (here: i) is shorter, than compute the
//					// callerPred in this way.
//					TransFormula callTF = ((Return) trace.getSymbol(i)).getCorrespondingCall().getTransitionFormula();
//					TransFormula globalVarsAssignments = m_ModifiedGlobals.getGlobalVarsAssignment(((Return) trace.getSymbol(i)).getCorrespondingCall().getCallStatement().getMethodName());
//					if ((i - call_pos) < call_pos) {
//						summary = computeSummaryForTrace(getSubTrace(call_pos, i - 1, trace), callTF,
//								trace.getSymbol(i).getTransitionFormula(), globalVarsAssignments);
//						callerPred = m_SmtManager.weakestPrecondition(m_InterpolantsWp[i+1], 
//								summary);;
//					}
//					
//					IPredicate p = m_SmtManager.weakestPrecondition(
//							m_InterpolantsWp[i+1], callerPred, trace.getSymbol(i+1).getTransitionFormula(), callTF, globalVarsAssignments); 
//					m_InterpolantsWp[i] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(),
//							p.getVars(), p.getProcedures());
//				} else {
//					IPredicate p = m_SmtManager.weakestPrecondition(
//							m_InterpolantsWp[i+1], trace.getSymbol(i+1));
//					m_InterpolantsWp[i] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(),
//							p.getVars(), p.getProcedures());
//				}
//			}
			s_Logger.debug("Checking weakest precondition...");
			assert checkInterpolantsCorrect(m_InterpolantsWp, trace, tracePrecondition, 
					tracePostcondition, "wp without unsat core") : "invalid Hoare triple in wp without unsat core";
		}
		if (m_ComputeInterpolantsSp) {
			m_Interpolants = m_InterpolantsSp;
		} else {
			assert (m_ComputeInterpolantsWp);
			m_Interpolants = m_InterpolantsWp;
		}
	}

	boolean checkInterpolantsCorrect(IPredicate[] interpolants,
								  Word<CodeBlock> trace, 
								  IPredicate tracePrecondition, 
								  IPredicate tracePostcondition,
								  String computation) {
		LBool result;
		for (int i=-1; i<interpolants.length; i++) {
			 result = isHoareTriple(i+1, tracePrecondition, tracePostcondition, 
						interpolants, trace);
			 if (result == LBool.SAT) {
				 s_Logger.debug("Trace length: " + trace.length());
				 s_Logger.debug("Stmt: " + (i+1));
				 return false;
			 }
			 assert result == LBool.UNSAT || result == LBool.UNKNOWN : 
				 "invalid Hoare triple in " + computation;
		}
		return true;
	}
	
	private IPredicate getInterpolantAtPosition(int i, IPredicate tracePrecondition,
			IPredicate tracePostcondition, IPredicate[] interpolants) {
		assert (i>= -1 && i<= interpolants.length);
		if (i == -1) {
			return tracePrecondition;
		} else if (i == interpolants.length) {
			return tracePostcondition;
		} else {
			return interpolants[i];
		}
	}
	
	
	private LBool isHoareTriple(int i, IPredicate tracePrecondition, 
			IPredicate tracePostcondition, 
			IPredicate[] interpolants, Word<CodeBlock> trace) {
		IPredicate pre = getInterpolantAtPosition(i-1, tracePrecondition, 
				tracePostcondition, interpolants);
		IPredicate post = getInterpolantAtPosition(i, tracePrecondition, 
				tracePostcondition, interpolants);
		CodeBlock cb = trace.getSymbol(i);
		EdgeChecker ec = new EdgeChecker(m_SmtManager, m_ModifiedGlobals);
		ec.assertCodeBlock(cb);
		ec.assertPrecondition(pre);
		LBool result;
		if (cb instanceof Call) {
			result = ec.postCallImplies(post);
		} else if (cb instanceof Return) {
			NestedWord<CodeBlock> nw = (NestedWord<CodeBlock>) trace;
			assert nw.isReturnPosition(i);
			int callPosition = nw.getCallPosition(i); 
			IPredicate callPredecessor = getInterpolantAtPosition(callPosition-1, 
					tracePrecondition, tracePostcondition, interpolants);
			ec.assertHierPred(callPredecessor);
			result = ec.postReturnImplies(post);
			ec.unAssertHierPred();
		} else if (cb instanceof InterproceduralSequentialComposition) {
			result = ec.postInternalImplies(post); 
		} else {
			assert (cb instanceof SequentialComposition) || 
				(cb instanceof ParallelComposition) || 
				(cb instanceof StatementSequence) ||
				(cb instanceof Summary);
			result = ec.postInternalImplies(post); 
		}
		ec.unAssertPrecondition();
		ec.unAssertCodeBlock();
		s_Logger.debug("Hoare triple {" + pre + "}, " + cb + " {" 
											+ post + "} is " + (result == LBool.UNSAT ? "valid" :
												(result == LBool.SAT ? "not valid" : result)));
		return result;
	}
	
	
	@Override
	protected AnnotateAndAsserter getAnnotateAndAsserter(NestedFormulas<Term, Term> ssa) {
		if (m_useUnsatCoreOfFineGranularity) {
			return new AnnotateAndAsserterConjuncts(m_SmtManager, ssa, m_DefaultTransFormulas); 
		} else {
			return new AnnotateAndAsserter(m_SmtManager, ssa);
		}
	}
	
	
	


}
