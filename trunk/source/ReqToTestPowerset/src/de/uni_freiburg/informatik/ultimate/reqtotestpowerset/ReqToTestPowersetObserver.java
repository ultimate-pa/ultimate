package de.uni_freiburg.informatik.ultimate.reqtotestpowerset;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.lib.models.ObjectContainer;
import de.uni_freiburg.informatik.ultimate.core.lib.observers.BaseObserver;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.BoogieDeclarations;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.pea2boogie.CddToSmt;
import de.uni_freiburg.informatik.ultimate.reqtotest.req.ReqSymbolTable;
import de.uni_freiburg.informatik.ultimate.reqtotest.req.ReqToDeclarations;
import de.uni_freiburg.informatik.ultimate.reqtotestpowerset.graph.BuchiGraph;
import de.uni_freiburg.informatik.ultimate.reqtotestpowerset.graph.GuardGraph;
import de.uni_freiburg.informatik.ultimate.reqtotestpowerset.graph.InputDetSuccConstruction;
import de.uni_freiburg.informatik.ultimate.reqtotestpowerset.graph.PowersetConstruction;

public class ReqToTestPowersetObserver extends BaseObserver{

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private final IToolchainStorage mStorage;
	
	private final ManagedScript mManagedScript;
	private final Script mScript;
	
	public ReqToTestPowersetObserver(final ILogger logger, final IUltimateServiceProvider services,
			final IToolchainStorage storage) {
		mLogger = logger;
		mServices = services;
		mStorage = storage;
		
		final SolverSettings settings = SolverBuilder.constructSolverSettings("", SolverMode.External_DefaultMode,
				false, SolverBuilder.COMMAND_Z3_NO_TIMEOUT, false, null);
		mScript = SolverBuilder.buildAndInitializeSolver(services, storage, SolverMode.External_DefaultMode, settings,
				false, false, Logics.ALL.toString(), "RtInconsistencySolver");

		mManagedScript = new ManagedScript(services, mScript);
	}

	@Override
	public boolean process(IElement root) throws Throwable {
		if (!(root instanceof ObjectContainer)) {
		return false;
		}
		
		final List<PatternType> rawPatterns = ((ObjectContainer<List<PatternType>>) root).getValue();
		final ReqSymbolTable symbolTable =  new ReqToDeclarations(mLogger).initPatternToSymbolTable(rawPatterns);
		BoogieDeclarations boogieDeclarations = new BoogieDeclarations(symbolTable.constructVariableDeclarations(), mLogger);
		Boogie2SMT boogie2Smt = new Boogie2SMT(mManagedScript, boogieDeclarations, false, mServices, false);
		CddToSmt cddToSmt = new CddToSmt(mServices, mStorage, mScript, boogie2Smt, boogieDeclarations, symbolTable);
		
		final BuchiGraph reqToBuchi = new BuchiGraph(mLogger, mScript, cddToSmt);
		final List<GuardGraph> automata = reqToBuchi.patternListToBuechi(rawPatterns);
		final GuardGraph setAutomaton = new PowersetConstruction(mLogger, automata, mScript).getProduct();
		mLogger.warn("SBPA");
		mLogger.warn(setAutomaton.getNrOfNodes());
		mLogger.warn(setAutomaton.getNrOfEdges());
		
		final GuardGraph inputDetAutomaton = new InputDetSuccConstruction(mManagedScript, mServices, mLogger, setAutomaton, mScript, symbolTable).getAutomaton();
		mLogger.warn("IDA");
		mLogger.warn(inputDetAutomaton.getNrOfNodes());
		mLogger.warn(inputDetAutomaton.getNrOfEdges());
		mLogger.warn(inputDetAutomaton);
//		TODO remove this; just for debug
		
		
		return false;
	}


	public IElement getAst() {
		// TODO Auto-generated method stub
		return null;
	}


}
