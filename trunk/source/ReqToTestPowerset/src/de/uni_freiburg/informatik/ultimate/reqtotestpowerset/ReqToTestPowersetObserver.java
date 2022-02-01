package de.uni_freiburg.informatik.ultimate.reqtotestpowerset;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.lib.models.ObjectContainer;
import de.uni_freiburg.informatik.ultimate.core.lib.observers.BaseObserver;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.BoogieDeclarations;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.pea2boogie.CddToSmt;
import de.uni_freiburg.informatik.ultimate.pea2boogie.PeaResultUtil;
import de.uni_freiburg.informatik.ultimate.reqtotest.req.Req2TestReqSymbolTable;
import de.uni_freiburg.informatik.ultimate.reqtotest.req.ReqToDeclarations;
import de.uni_freiburg.informatik.ultimate.reqtotestpowerset.graph.BuchiGraph;
import de.uni_freiburg.informatik.ultimate.reqtotestpowerset.graph.GuardGraph;
import de.uni_freiburg.informatik.ultimate.reqtotestpowerset.graph.InputDetSuccConstruction;
import de.uni_freiburg.informatik.ultimate.reqtotestpowerset.graph.PowersetConstruction;

public class ReqToTestPowersetObserver extends BaseObserver {

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;

	private final ManagedScript mManagedScript;
	private final Script mScript;

	public ReqToTestPowersetObserver(final ILogger logger, final IUltimateServiceProvider services) {
		mLogger = logger;
		mServices = services;
		final SolverSettings settings =
				SolverBuilder.constructSolverSettings().setSolverMode(SolverMode.External_DefaultMode)
						.setUseExternalSolver(true, SolverBuilder.COMMAND_Z3_NO_TIMEOUT, Logics.ALL);
		mScript = SolverBuilder.buildAndInitializeSolver(services, settings, "RtInconsistencySolver");

		mManagedScript = new ManagedScript(services, mScript);
	}

	@Override
	public boolean process(final IElement root) throws Throwable {
		if (!(root instanceof ObjectContainer)) {
			return false;
		}

		@SuppressWarnings("unchecked")
		final List<PatternType<?>> rawPatterns = ((ObjectContainer<List<PatternType<?>>>) root).getValue();
		final Req2TestReqSymbolTable symbolTable = new ReqToDeclarations(mLogger).initPatternToSymbolTable(rawPatterns);
		final BoogieDeclarations boogieDeclarations =
				new BoogieDeclarations(symbolTable.constructVariableDeclarations(), mLogger);
		final Boogie2SMT boogie2Smt = new Boogie2SMT(mManagedScript, boogieDeclarations, false, mServices, false);
		final PeaResultUtil resultUtil = new PeaResultUtil(mLogger, mServices);
		final CddToSmt cddToSmt =
				new CddToSmt(mServices, resultUtil, mScript, boogie2Smt, boogieDeclarations, symbolTable);

		final BuchiGraph reqToBuchi = new BuchiGraph(mLogger, mScript, cddToSmt);
		final List<GuardGraph> automata = reqToBuchi.patternListToBuechi(rawPatterns);
		final GuardGraph setAutomaton = new PowersetConstruction(mLogger, automata, mScript).getProduct();
		mLogger.warn("SBPA");
		mLogger.warn(setAutomaton.getNrOfNodes());
		mLogger.warn(setAutomaton.getNrOfEdges());

		final GuardGraph inputDetAutomaton =
				new InputDetSuccConstruction(mManagedScript, mServices, mLogger, setAutomaton, mScript, symbolTable)
						.getAutomaton();
		mLogger.warn("IDA");
		mLogger.warn(inputDetAutomaton.getNrOfNodes());
		mLogger.warn(inputDetAutomaton.getNrOfEdges());
		mLogger.warn(inputDetAutomaton);
		// TODO remove this; just for debug

		return false;
	}

	public IElement getAst() {
		// TODO Auto-generated method stub
		return null;
	}

}
