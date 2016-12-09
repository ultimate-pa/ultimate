/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.tool;

import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.Set;
import java.util.function.BiFunction;
import java.util.function.Supplier;

import de.uni_freiburg.informatik.ultimate.abstractinterpretation.model.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.abstractinterpretation.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.AbstractInterpretationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.FixpointEngine;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.FixpointEngineParameters;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.ILoopDetector;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.IResultReporter;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.ITransitionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.generic.SilentReporter;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.nwa.NWAPathProgramTransitionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RCFGLiteralCollector;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgLibraryModeResultReporter;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgLoopDetector;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgResultReporter;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgTransitionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgUtils;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.dataflow.DataflowDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.dataflow.DataflowState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.tool.initializer.FixpointEngineFutureParameterFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.tool.initializer.FixpointEngineParameterFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.util.AbsIntUtil;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * Should be used by other tools to run abstract interpretation on various parts of the RCFG.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public final class AbstractInterpreter {
	
	/**
	 * Run abstract interpretation on the whole RCFG.
	 *
	 * Suppress all exceptions except {@link OutOfMemoryError}, {@link ToolchainCanceledException},
	 * {@link IllegalArgumentException}. Produce no results.
	 *
	 */
	public static <STATE extends IAbstractState<STATE, CodeBlock, IBoogieVar>>
			IAbstractInterpretationResult<STATE, CodeBlock, IBoogieVar, BoogieIcfgLocation>
			runSilently(final BoogieIcfgContainer root, final Collection<CodeBlock> initials,
					final IProgressAwareTimer timer, final IUltimateServiceProvider services) {
		final ILogger logger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		final Supplier<IAbstractInterpretationResult<STATE, CodeBlock, IBoogieVar, BoogieIcfgLocation>> fun =
				() -> run(root, initials, timer, services, true);
		return runSilently(fun, logger);
	}
	
	/**
	 * Run abstract interpretation on the whole RCFG.
	 *
	 */
	public static <STATE extends IAbstractState<STATE, CodeBlock, IBoogieVar>>
			IAbstractInterpretationResult<STATE, CodeBlock, IBoogieVar, BoogieIcfgLocation>
			run(final BoogieIcfgContainer root, final IProgressAwareTimer timer,
					final IUltimateServiceProvider services) {
		return run(root, RcfgUtils.getInitialEdges(root), timer, services, false);
	}
	
	/**
	 * Run abstract interpretation on a path program constructed from a counterexample.
	 *
	 * @param pathProgramProjection
	 *
	 */
	public static <STATE extends IAbstractState<STATE, CodeBlock, IBoogieVar>>
			IAbstractInterpretationResult<STATE, CodeBlock, IBoogieVar, BoogieIcfgLocation> runOnPathProgram(
					final IIcfg<BoogieIcfgLocation> root, final INestedWordAutomatonSimple<CodeBlock, ?> abstraction,
					final NestedRun<CodeBlock, ?> counterexample, final Set<CodeBlock> pathProgramProjection,
					final IProgressAwareTimer timer, final IUltimateServiceProvider services) {
		assert counterexample != null && counterexample.getLength() > 0 : "Invalid counterexample";
		assert abstraction != null;
		assert root != null;
		assert services != null;
		assert timer != null;
		
		final ILogger logger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		try {
			final NWAPathProgramTransitionProvider transProvider =
					new NWAPathProgramTransitionProvider(counterexample, pathProgramProjection, services, root);
			final CodeBlock initial = counterexample.getSymbol(0);
			final Script script = root.getCfgSmtToolkit().getManagedScript().getScript();
			final FixpointEngineParameterFactory domFac =
					new FixpointEngineParameterFactory(root, () -> new RCFGLiteralCollector(root), services);
			final FixpointEngineParameters<STATE, CodeBlock, IBoogieVar, BoogieIcfgLocation, Expression> params =
					domFac.createParamsPathProgram(timer, transProvider, transProvider);
			final FixpointEngine<STATE, CodeBlock, IBoogieVar, BoogieIcfgLocation, Expression> fxpe =
					new FixpointEngine<>(params);
			final AbstractInterpretationResult<STATE, CodeBlock, IBoogieVar, BoogieIcfgLocation> result =
					fxpe.run(initial, script);
			if (!result.hasReachedError()) {
				logger.info("NWA was safe (error state unreachable)");
			} else {
				logger.info("Could not show that NWA was safe (error state reachable)");
			}
			if (logger.isDebugEnabled()) {
				logger.debug("Found the following predicates:");
				AbsIntUtil.logPredicates(Collections.singletonMap(initial, result.getLoc2Term()), script,
						logger::debug);
			}
			logger.info(result.getBenchmark());
			return result;
		} catch (final ToolchainCanceledException tce) {
			// suppress timeout results / timeouts
			logger.warn("Abstract interpretation run out of time");
			return null;
		}
	}
	
	private static <STATE extends IAbstractState<STATE, CodeBlock, IBoogieVar>>
			IAbstractInterpretationResult<STATE, CodeBlock, IBoogieVar, BoogieIcfgLocation>
			run(final BoogieIcfgContainer root, final Collection<CodeBlock> initials, final IProgressAwareTimer timer,
					final IUltimateServiceProvider services, final boolean isSilent) {
		if (initials == null) {
			throw new IllegalArgumentException("No initial edges provided");
		}
		if (timer == null) {
			throw new IllegalArgumentException("timer is null");
		}
		
		final ITransitionProvider<CodeBlock, BoogieIcfgLocation> transProvider = new RcfgTransitionProvider();
		final Collection<CodeBlock> filteredInitialElements = transProvider.filterInitialElements(initials);
		
		if (filteredInitialElements.isEmpty()) {
			getReporter(services, false, false).reportSafe(null, "The program is empty");
			return null;
		}
		
		final Script script = root.getCfgSmtToolkit().getManagedScript().getScript();
		final FixpointEngineParameterFactory domFac =
				new FixpointEngineParameterFactory(root, () -> new RCFGLiteralCollector(root), services);
		final boolean isLib = filteredInitialElements.size() > 1;
		final Iterator<CodeBlock> iter = filteredInitialElements.iterator();
		final ILoopDetector<CodeBlock> loopDetector = new RcfgLoopDetector<>();
		
		AbstractInterpretationResult<STATE, CodeBlock, IBoogieVar, BoogieIcfgLocation> result = null;
		
		// TODO: If an if is at the beginning of a method, this method will be analyzed two times
		while (iter.hasNext()) {
			final CodeBlock initial = iter.next();
			
			final FixpointEngineParameters<STATE, CodeBlock, IBoogieVar, BoogieIcfgLocation, Expression> params =
					domFac.createParams(timer, transProvider, loopDetector);
			
			final FixpointEngine<STATE, CodeBlock, IBoogieVar, BoogieIcfgLocation, Expression> fxpe =
					new FixpointEngine<>(params);
			result = fxpe.run(initial, script, result);
		}
		
		final ILogger logger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		if (result == null) {
			logger.error("Could not run because no initial element could be found");
			return null;
		}
		if (result.hasReachedError()) {
			final IResultReporter<STATE, CodeBlock, IBoogieVar, BoogieIcfgLocation> reporter =
					getReporter(services, isLib, isSilent);
			result.getCounterexamples().forEach(cex -> reporter.reportPossibleError(cex));
		} else {
			getReporter(services, false, isSilent).reportSafe(null);
		}
		if (logger.isDebugEnabled()) {
			logger.debug("Found the following predicates:");
			AbsIntUtil.logPredicates(result.getLoc2Term(), logger::debug);
		}
		logger.info(result.getBenchmark());
		return result;
	}
	
	/**
	 * Run abstract interpretation on the RCFG of the future (experimental).
	 *
	 * @param logger
	 *
	 */
	public static <STATE extends IAbstractState<STATE, CodeBlock, IProgramVar>>
			IAbstractInterpretationResult<STATE, CodeBlock, IProgramVar, BoogieIcfgLocation>
			runFuture(final IIcfg<?> root, final IProgressAwareTimer timer, final IUltimateServiceProvider services,
					final boolean isSilent, final ILogger logger) {
		return runFuture(root, timer, services, logger, isSilent, (fac, log) -> fac.selectDomainFutureCfg());
	}
	
	/**
	 * so far, this is a copy of runFuture(..), except some parameters (e.g. abstract domain) are not taken from the
	 * settings but hardcoded
	 *
	 * @param logger
	 *
	 */
	public static IAbstractInterpretationResult<VPState, CodeBlock, IProgramVar, BoogieIcfgLocation>
			runFutureEqualityDomain(final IIcfg<?> root, final IProgressAwareTimer timer,
					final IUltimateServiceProvider services, final boolean isSilent, final ILogger logger) {
		return runFuture(root, timer, services, logger, isSilent,
				(fac, log) -> fac.selectDomainFutureCfg(VPDomain.class, log));
	}
	
	public static IAbstractInterpretationResult<DataflowState, CodeBlock, IProgramVar, BoogieIcfgLocation>
			runFutureDataflowDomain(final IIcfg<?> root, final IProgressAwareTimer timer,
					final IUltimateServiceProvider services, final boolean isSilent, final ILogger logger) {
		return runFuture(root, timer, services, logger, isSilent,
				(fac, log) -> fac.selectDomainFutureCfg(DataflowDomain.class, log));
	}
	
	private static <STATE extends IAbstractState<STATE, CodeBlock, IProgramVar>>
			IAbstractInterpretationResult<STATE, CodeBlock, IProgramVar, BoogieIcfgLocation>
			runFuture(final IIcfg<?> root, final IProgressAwareTimer timer, final IUltimateServiceProvider services,
					final ILogger logger, final boolean isSilent,
					final BiFunction<FixpointEngineFutureParameterFactory, ILogger, IAbstractDomain<STATE, CodeBlock, IProgramVar>> fun) {
		
		final ITransitionProvider<CodeBlock, BoogieIcfgLocation> transProvider = new RcfgTransitionProvider();
		final Collection<CodeBlock> filteredInitialElements =
				transProvider.filterInitialElements(RcfgUtils.getInitialEdges(root));
		
		if (filteredInitialElements.isEmpty()) {
			getReporter(services, false, false).reportSafe(null, "The program is empty");
			return null;
		}
		
		final Script script = root.getCfgSmtToolkit().getManagedScript().getScript();
		final FixpointEngineFutureParameterFactory domFac = new FixpointEngineFutureParameterFactory(root, services);
		final ILoopDetector<CodeBlock> loopDetector = new RcfgLoopDetector<>();
		
		AbstractInterpretationResult<STATE, CodeBlock, IProgramVar, BoogieIcfgLocation> result = null;
		
		final Iterator<CodeBlock> iter = filteredInitialElements.iterator();
		while (iter.hasNext()) {
			final CodeBlock initial = iter.next();
			final FixpointEngineParameters<STATE, CodeBlock, IProgramVar, BoogieIcfgLocation, Expression> params =
					domFac.createParamsFuture(timer, transProvider, loopDetector, fun.apply(domFac, logger));
			final FixpointEngine<STATE, CodeBlock, IProgramVar, BoogieIcfgLocation, Expression> fxpe =
					new FixpointEngine<>(params);
			result = fxpe.run(initial, script, result);
		}
		
		if (result == null) {
			logger.error("Could not run because no initial element could be found");
			return null;
		}
		
		final boolean isLib = filteredInitialElements.size() > 1;
		if (result.hasReachedError()) {
			final IResultReporter<STATE, CodeBlock, IProgramVar, BoogieIcfgLocation> reporter =
					getReporter(services, isLib, isSilent);
			result.getCounterexamples().forEach(cex -> reporter.reportPossibleError(cex));
		} else {
			getReporter(services, false, isSilent).reportSafe(null);
		}
		
		logger.info(result.getBenchmark());
		return result;
	}
	
	private static <STATE extends IAbstractState<STATE, CodeBlock, VARDECL>, VARDECL, LOC>
			IAbstractInterpretationResult<STATE, CodeBlock, VARDECL, LOC>
			
			runSilently(final Supplier<IAbstractInterpretationResult<STATE, CodeBlock, VARDECL, LOC>> fun,
					final ILogger logger) {
		try {
			return fun.get();
		} catch (final OutOfMemoryError oom) {
			throw oom;
		} catch (final IllegalArgumentException iae) {
			throw iae;
		} catch (final ToolchainCanceledException tce) {
			// suppress timeout results / timeouts
			return null;
		} catch (final Throwable t) {
			logger.fatal("Suppressed exception in AIv2: " + t.getMessage());
			return null;
		}
	}
	
	private static <STATE extends IAbstractState<STATE, CodeBlock, VARDECL>, VARDECL>
			IResultReporter<STATE, CodeBlock, VARDECL, BoogieIcfgLocation>
			getReporter(final IUltimateServiceProvider services, final boolean isLibrary, final boolean isSilent) {
		if (isSilent) {
			return new SilentReporter<>();
		}
		if (isLibrary) {
			return new RcfgLibraryModeResultReporter<>(services);
		}
		return new RcfgResultReporter<>(services);
	}
}
