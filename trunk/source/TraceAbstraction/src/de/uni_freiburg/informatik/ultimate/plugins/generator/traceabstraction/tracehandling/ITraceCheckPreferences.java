package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling;

import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.UnsatCores;

public interface ITraceCheckPreferences<LETTER extends IIcfgTransition<?>> {

	boolean getUseSeparateSolverForTracechecks();

	AssertCodeBlockOrder getAssertCodeBlocksOrder();

	IToolchainStorage getToolchainStorage();

	String getPathOfDumpedScript();

	boolean getDumpSmtScriptToFile();

	boolean getUseWeakestPreconditionForPathInvariants();

	boolean getUseAbstractInterpretation();

	boolean getUseVarsFromUnsatCore();

	boolean getUseNonlinearConstraints();

	IIcfg<?> getIcfgContainer();

	boolean getUseLiveVariables();

	UnsatCores getUnsatCores();

	SimplificationTechnique getSimplificationTechnique();

	XnfConversionTechnique getXnfConversionTechnique();

	CfgSmtToolkit getCfgSmtToolkit();

	boolean collectInterpolantStatistics();

	boolean computeCounterexample();

}