package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg;

import java.util.Collections;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.IResultReporter;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.RcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.result.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution.ProgramState;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.result.PositiveResult;

public class RcfgResultReporter implements IResultReporter<CodeBlock> {

	private final IUltimateServiceProvider mServices;
	private final BaseRcfgAbstractStateStorageProvider mStorageProvider;

	public RcfgResultReporter(IUltimateServiceProvider services, BaseRcfgAbstractStateStorageProvider storageProvider) {
		mServices = services;
		mStorageProvider = storageProvider;
	}

	@Override
	public void reportPossibleError(CodeBlock start, CodeBlock end) {
		IResult result = new CounterExampleResult<ProgramPoint, CodeBlock, Expression>((ProgramPoint) end.getTarget(),
				Activator.PLUGIN_ID, mServices.getBacktranslationService(), getProgramExecution(start, end));
		mServices.getResultService().reportResult(Activator.PLUGIN_ID, result);
	}

	private IProgramExecution<CodeBlock, Expression> getProgramExecution(CodeBlock start, CodeBlock end) {
		List<CodeBlock> trace = mStorageProvider.getTrace(start, end);
		Map<Integer, ProgramState<Expression>> map = Collections.emptyMap();
		RcfgProgramExecution pe = new RcfgProgramExecution(trace, map);
		return pe;
	}

	@Override
	public void reportSafe(CodeBlock start) {
		mServices.getResultService().reportResult(
				Activator.PLUGIN_ID,
				new PositiveResult<RCFGNode>(Activator.PLUGIN_ID, start.getSource(), mServices
						.getBacktranslationService()));
	}

}
