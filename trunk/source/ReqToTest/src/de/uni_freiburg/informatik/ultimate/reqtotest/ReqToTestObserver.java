package de.uni_freiburg.informatik.ultimate.reqtotest;

import java.util.List;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.core.lib.models.ObjectContainer;
import de.uni_freiburg.informatik.ultimate.core.lib.observers.BaseObserver;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
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
import de.uni_freiburg.informatik.ultimate.reqtotest.graphtransformer.AuxVarGen;
import de.uni_freiburg.informatik.ultimate.reqtotest.graphtransformer.GraphToBoogie;
import de.uni_freiburg.informatik.ultimate.reqtotest.req.Req2TestReqSymbolTable;
import de.uni_freiburg.informatik.ultimate.reqtotest.req.ReqGuardGraph;
import de.uni_freiburg.informatik.ultimate.reqtotest.req.ReqToDeclarations;
import de.uni_freiburg.informatik.ultimate.reqtotest.req.ReqToGraph;
import de.uni_freiburg.informatik.ultimate.reqtotest.req.ReqToInOut;
import de.uni_freiburg.informatik.ultimate.reqtotest.testgenerator.CounterExampleToTest;

public class ReqToTestObserver extends BaseObserver {

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private IElement mBoogieAst;
	private CounterExampleToTest mResultTransformer;

	private final ManagedScript mManagedScript;
	private final Script mScript;

	// set true for outputting the whole counter example instead of a test representation of the cs.
	private final boolean RETURN_RESULT_AS_COUNTEREXAMPLE = false;

	public ReqToTestObserver(final ILogger logger, final IUltimateServiceProvider services) {
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
		final Req2TestReqSymbolTable reqSymbolTable =
				new ReqToDeclarations(mLogger).initPatternToSymbolTable(rawPatterns);
		final BoogieDeclarations boogieDeclarations =
				new BoogieDeclarations(reqSymbolTable.constructVariableDeclarations(), mLogger);
		final Boogie2SMT boogie2Smt = new Boogie2SMT(mManagedScript, boogieDeclarations, false, mServices, false);
		final PeaResultUtil resultUtil = new PeaResultUtil(mLogger, mServices);
		final CddToSmt cddToSmt =
				new CddToSmt(mServices, resultUtil, mScript, boogie2Smt, boogieDeclarations, reqSymbolTable);
		if (reqSymbolTable.getOutputVars().isEmpty()) {
			final ReqToInOut reqToInOut = new ReqToInOut(mLogger, reqSymbolTable, cddToSmt);
			reqToInOut.requirementToInOut(rawPatterns);
		}
		final AuxVarGen auxVarGen = new AuxVarGen(mLogger, mScript, reqSymbolTable);
		final ReqToGraph reqToBuchi = new ReqToGraph(mLogger, auxVarGen, mScript, cddToSmt, reqSymbolTable);
		final List<ReqGuardGraph> automata = reqToBuchi.patternListToBuechi(rawPatterns);
		final GraphToBoogie graphToBoogie =
				new GraphToBoogie(mLogger, mServices, reqSymbolTable, auxVarGen, automata, mScript, mManagedScript);
		mBoogieAst = graphToBoogie.getAst();

		if (!RETURN_RESULT_AS_COUNTEREXAMPLE) {
			mResultTransformer = new CounterExampleToTest(mLogger, mServices, reqSymbolTable, auxVarGen);
			final Function<IResult, IResult> resultTransformer = mResultTransformer::convertCounterExampleToTest;
			mServices.getResultService().registerTransformer("CexToTest", resultTransformer);
		}

		return false;
	}

	public IElement getAst() {
		return mBoogieAst;
	}

}
