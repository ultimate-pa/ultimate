package de.uni_freiburg.informatik.ultimate.pea2boogie;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.BoogieDeclarations;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.InitialTransition;
import de.uni_freiburg.informatik.ultimate.lib.pea.Phase;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseSmt;
import de.uni_freiburg.informatik.ultimate.lib.pea.Transition;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.ExternalSolver;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class PeaCddToSmt {

	private final Script mScript;
	private final ManagedScript mManagedScript;
	private final Term mTrue;
	private final Term mFalse;
	private final CddToSmt mCddToSmt;
	private final Boogie2SMT mBoogieToSmt;
	private final IReqSymbolTable mReqSymbolTable;
	private final PeaResultUtil mPeaResultUtil;

	private final ILogger mLogger;

	public PeaCddToSmt(final ILogger logger, final IUltimateServiceProvider services,
			final IReqSymbolTable symboltable) {
		mLogger = logger;

		mReqSymbolTable = symboltable;
		mScript = buildSolver(services);
		mManagedScript = new ManagedScript(services, mScript);
		mTrue = mScript.term("true");
		mFalse = mScript.term("false");

		final List<Declaration> decls = new ArrayList<>();
		decls.addAll(mReqSymbolTable.getDeclarations());
		final BoogieDeclarations boogieDeclarations = new BoogieDeclarations(decls, mLogger);

		// TODO: what to do with this result util
		mPeaResultUtil = new PeaResultUtil(mLogger, services);
		mBoogieToSmt = new Boogie2SMT(mManagedScript, boogieDeclarations, services, false);
		mCddToSmt = new CddToSmt(services, mPeaResultUtil, mScript, mBoogieToSmt, boogieDeclarations, mReqSymbolTable);
	}

	public PhaseEventAutomata<CDD> toTermPea(PhaseEventAutomata<CDD> cddPea) {
		// just return identity for testing
		return cddPea;
	}

	public PhaseEventAutomata<Term> toTermPeaFuture(PhaseEventAutomata<CDD> cddPea) {
		Map<String, PhaseSmt> termPhases = new HashMap<String, PhaseSmt>();
		List<InitialTransition<Term>> initPhases = new ArrayList<InitialTransition<Term>>();

		for (Phase<CDD> inPhase : cddPea.getPhases()) {
			Term invariant = mCddToSmt.toSmt(inPhase.getStateInvariant());
			Term clockInvariant = mCddToSmt.toSmt(inPhase.getClockInvariant());

			PhaseSmt termPhase = new PhaseSmt(inPhase.getName(), invariant, clockInvariant, mScript);
			termPhase.setInit(inPhase.isInit());
			if (termPhase.isInit) {
				initPhases.add(new InitialTransition<Term>(mTrue, termPhase));
			}
			// termPhase.phaseBits = inPhase.getPhaseBits()
			termPhases.put(inPhase.getName(), termPhase);

		}

		for (Phase<CDD> inPhase : cddPea.getPhases()) {
			PhaseSmt termPhase = termPhases.get(inPhase.getName());
			for (Transition<CDD> trans : inPhase.getTransitions()) {
				Term guard = mCddToSmt.toSmt(trans.getGuard());
				PhaseSmt dest = termPhases.get(trans.getDest().getName());

				termPhase.addTransition(dest, guard, trans.getResets());
			}
		}

		return new PhaseEventAutomata<Term>(cddPea.getName(), new ArrayList<Phase<Term>>(termPhases.values()),
				initPhases, cddPea.getClocks(), cddPea.getVariables(), cddPea.getEvents(), cddPea.getDeclarations());
	}

	private static Script buildSolver(final IUltimateServiceProvider services) throws AssertionError {

		SolverSettings settings = SolverBuilder.constructSolverSettings()
				.setSolverMode(SolverMode.External_ModelsAndUnsatCoreMode).setUseExternalSolver(ExternalSolver.Z3);
		/*
		 * if (SOLVER_LOG_DIR != null) { settings = settings.setDumpSmtScriptToFile(true, SOLVER_LOG_DIR,
		 * RtInconcistencyConditionGenerator.class.getSimpleName(), false); }
		 */
		return SolverBuilder.buildAndInitializeSolver(services, settings, "PeaCddToSmtSolver");
	}

}
