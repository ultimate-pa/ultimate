package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants;

import java.util.ArrayList;
import java.util.Map;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lassoranker.LinearTransition;
import de.uni_freiburg.informatik.ultimate.lassoranker.exceptions.TermException;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.AddAxioms;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.DNF;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.MatchInVars;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.RemoveNegation;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.RewriteBooleans;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.RewriteDivision;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.RewriteEquality;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.RewriteIte;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.RewriteStrictInequalities;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.RewriteTrueFalse;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.SimplifyPreprocessor;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.TransitionPreProcessor;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.TransFormulaLR;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.TermVarsProc;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.IInvariantPatternProcessor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.IInvariantPatternProcessorFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.IInterpolantGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;

/**
 * Represents a map of invariants to a run, that has been generated using a
 * {@link IInvariantPatternProcessor} on the run-projected CFG.
 */
public class PathInvariantsGenerator implements IInterpolantGenerator {

	private final IUltimateServiceProvider m_Services;
	private final Logger m_Logger;

	private final NestedRun<CodeBlock, IPredicate> m_Run;
	private final IPredicate m_Precondition;
	private final IPredicate m_Postcondition;
	private final PredicateUnifier m_PredicateUnifier;
	private final ModifiableGlobalVariableManager m_ModifiableGlobalVariableManager;
	private final SmtManager m_SmtManager;
	private final IPredicate[] m_Interpolants;
	
	/**
	 * Generates a map of invariants to a given run, using an
	 * {@link IInvariantPatternProcessor} produced by the default
	 * {@link IInvariantPatternProcessorFactory} (with default settings).
	 * 
	 * @param services Service provider to aquire a logging service through 
	 * @param run an infeasible run to project into a CFG
	 * @param precondition the predicate to use for the first program point in
	 * the run
	 * @param postcondition the predicate to use for the last program point in
	 * the run
	 * @param predicateUnifier the predicate unifier to unify final predicates
	 * with
	 * @param smtManager manager to access SMT stuff(TM) TODO
	 * @param modGlobVarManager ??? TODO
	 */
	public PathInvariantsGenerator(IUltimateServiceProvider services,
			NestedRun<CodeBlock, IPredicate> run, IPredicate precondition,
			IPredicate postcondition, PredicateUnifier predicateUnifier,
			SmtManager smtManager,
			ModifiableGlobalVariableManager modGlobVarManager) {
		throw new UnsupportedOperationException("Not implemented.");
	}
	
	/**
	 * Generates a map of invariants to a given run, using an
	 * {@link IInvariantPatternProcessor} produced by a given
	 * {@link IInvariantPatternProcessorFactory}.
	 * 
	 * @param services Service provider to aquire a logging service through 
	 * @param run an infeasible run to project into a CFG
	 * @param precondition the predicate to use for the first program point in
	 * the run
	 * @param postcondition the predicate to use for the last program point in
	 * the run
	 * @param predicateUnifier the predicate unifier to unify final predicates
	 * with
	 * @param smtManager manager to access SMT stuff(TM) TODO
	 * @param modGlobVarManager ??? TODO
	 * @param invPatternProcFactory the factory to generate the
	 * {@link IInvariantPatternProcessor} to use
	 */
	public PathInvariantsGenerator(final IUltimateServiceProvider services,
			final NestedRun<CodeBlock, IPredicate> run,
			final IPredicate precondition,
			final IPredicate postcondition,
			final PredicateUnifier predicateUnifier,
			final SmtManager smtManager,
			final ModifiableGlobalVariableManager modGlobVarManager,
			final IInvariantPatternProcessorFactory invPatternProcFactory) {
		super();
		m_Services = services;
		m_Logger = services.getLoggingService()
				.getLogger(Activator.s_PLUGIN_ID);
		m_Run = run;
		m_Precondition = precondition;
		m_Postcondition = postcondition;
		m_PredicateUnifier = predicateUnifier;
		m_ModifiableGlobalVariableManager = modGlobVarManager;
		m_SmtManager = smtManager;

		ArrayList<ProgramPoint> sequenceOfProgramPoints = new ArrayList<>();
		for (IPredicate pred : m_Run.getStateSequence()) {
			sequenceOfProgramPoints
					.add(((ISLPredicate) pred).getProgramPoint());
		}
		
		// TODO:
		// 1. Project run into internal.ControlFlowGraph
		// 2. Use CFGInvariantsGenerator on CFG with pre- and postcondition
		// 3. Store result in m_Interpolants
		
		// Matthias: You obtain the transition formulas as follows. 
		m_Run.getSymbol(0).getTransitionFormula(); 

		
		// Matthias: Given a term, that represents a set of program states, you
		// obtain the corresponding IPredicate as follows.
		// Each free variable in the term has to be bv.getTermVariable() for
		// some BoogieVar bv.
		Term term = null;
		m_PredicateUnifier.getOrConstructPredicate(
				TermVarsProc.computeTermVarsProc(term, m_SmtManager.getBoogie2Smt()));
		throw new UnsupportedOperationException("Not implemented.");
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public Word<CodeBlock> getTrace() {
		return m_Run.getWord();
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public IPredicate getPrecondition() {
		return m_Precondition;
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public IPredicate getPostcondition() {
		return m_Postcondition;
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public Map<Integer, IPredicate> getPendingContexts() {
		throw new UnsupportedOperationException("Call/Return not supported yet");
	}

	/**
	 * Returns a sequence of interpolants (see definition in
	 * {@link IInterpolantGenerator}) the trace which is m_Run.getWord() with an
	 * additional property. If the ProgramPoint and position i and k coincide
	 * the the interpolants at position i and k coincide.
	 * 
	 * @return sequence of interpolants according to the run provided in the
	 * constructor
	 */
	@Override
	public IPredicate[] getInterpolants() {
		return m_Interpolants;
	}

}
