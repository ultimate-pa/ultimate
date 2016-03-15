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

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.boogie.type.PreprocessorAnnotation;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.core.services.model.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.model.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SmtSymbolTable;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.AbstractInterpretationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.FixpointEngine;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.FixpointEngineParameters;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.ILoopDetector;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.IResultReporter;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.ITransitionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.generic.SilentReporter;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.nwa.NWAPathProgramTransitionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.AnnotatingRcfgAbstractStateStorageProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.BaseRcfgAbstractStateStorageProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RCFGLiteralCollector;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgAbstractStateStorageProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgDebugHelper;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgLibraryModeResultReporter;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgLoopDetector;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgResultReporter;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgTransitionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgVariableProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.compound.CompoundDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.compound.CompoundDomainPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.empty.EmptyDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.congruence.CongruenceDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval.IntervalDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.sign.SignDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon.OctagonDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.vp.VPDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.preferences.AbsIntPrefInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.util.AbsIntUtil;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.util.ToolchainCanceledException;

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
	 * @return
	 */
	public static IAbstractInterpretationResult<?, CodeBlock, IBoogieVar, ProgramPoint> runSilently(final RootNode root,
			final Collection<CodeBlock> initials, final IProgressAwareTimer timer,
			final IUltimateServiceProvider services) {
		final Logger logger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		try {
			return runOnRCFG(root, initials, timer, services, true);
		} catch (OutOfMemoryError oom) {
			throw oom;
		} catch (IllegalArgumentException iae) {
			throw iae;
		} catch (ToolchainCanceledException tce) {
			// suppress timeout results / timeouts
			return null;
		} catch (Throwable t) {
			logger.fatal("Suppressed exception in AIv2: " + t.getMessage());
			return null;
		}
	}

	/**
	 * Run abstract interpretation on a path program constructed from a counterexample.
	 * 
	 */
	public static IAbstractInterpretationResult<?, CodeBlock, IBoogieVar, ?> runSilently(
			final NestedRun<CodeBlock, ?> counterexample,
			final INestedWordAutomatonOldApi<CodeBlock, ?> currentAutomata, final RootNode root,
			final IProgressAwareTimer timer, final IUltimateServiceProvider services) {
		assert counterexample != null && counterexample.getLength() > 0 : "Invalid counterexample";
		assert currentAutomata != null;
		assert root != null;
		assert services != null;
		assert timer != null;

		final Logger logger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		try {
			final NWAPathProgramTransitionProvider transProvider = new NWAPathProgramTransitionProvider(
					counterexample, services, root.getRootAnnot());
			return runSilentlyOnNWA(transProvider, counterexample.getSymbol(0), root, timer, services);
		} catch (OutOfMemoryError oom) {
			throw oom;
		} catch (IllegalArgumentException iae) {
			throw iae;
		} catch (ToolchainCanceledException tce) {
			// suppress timeout results / timeouts
			return null;
		} catch (Throwable t) {
			logger.fatal("Suppressed exception in AIv2: " + t.getClass().getSimpleName() + " with message "
					+ t.getMessage());
			t.printStackTrace();
			return null;
		}
	}

	private static AbstractInterpretationResult<?, CodeBlock, IBoogieVar, ?> runSilentlyOnNWA(
			final NWAPathProgramTransitionProvider transProvider, final CodeBlock initial, final RootNode root,
			final IProgressAwareTimer timer, final IUltimateServiceProvider services) throws Throwable {

		final BoogieSymbolTable symbolTable = getSymbolTable(root);
		if (symbolTable == null) {
			throw new IllegalArgumentException("Could not get BoogieSymbolTable");
		}

		final RootAnnot rootAnnot = root.getRootAnnot();
		final Boogie2SMT bpl2smt = rootAnnot.getBoogie2SMT();
		final Script script = rootAnnot.getScript();
		final Boogie2SmtSymbolTable boogieVarTable = bpl2smt.getBoogie2SmtSymbolTable();

		final IAbstractDomain<?, CodeBlock, IBoogieVar> domain = selectDomain(() -> new RCFGLiteralCollector(root),
				symbolTable, services, rootAnnot);

		return runSilentlyOnNWA(initial, timer, services, symbolTable, bpl2smt, script, boogieVarTable, domain,
				transProvider, transProvider, rootAnnot);
	}

	private static <STATE extends IAbstractState<STATE, CodeBlock, IBoogieVar>, LOC> AbstractInterpretationResult<STATE, CodeBlock, IBoogieVar, LOC> runSilentlyOnNWA(
			final CodeBlock initial, final IProgressAwareTimer timer, final IUltimateServiceProvider services,
			final BoogieSymbolTable symbolTable, final Boogie2SMT bpl2smt, final Script script,
			final Boogie2SmtSymbolTable boogieVarTable, final IAbstractDomain<STATE, CodeBlock, IBoogieVar> domain,
			final ITransitionProvider<CodeBlock, LOC> transitionProvider, final ILoopDetector<CodeBlock> loopDetector,
			final RootAnnot rootAnnot) {

		final RcfgDebugHelper<STATE, LOC> debugHelper = new RcfgDebugHelper<STATE, LOC>(rootAnnot, services);
		final FixpointEngineParameters<STATE, CodeBlock, IBoogieVar, LOC> params = new FixpointEngineParameters<STATE, CodeBlock, IBoogieVar, LOC>()
				.addDomain(domain).addLoopDetector(loopDetector)
				.addStorage(new RcfgAbstractStateStorageProvider<STATE, LOC>(domain.getMergeOperator(), services,
						transitionProvider))
				.addTransitionProvider(transitionProvider)
				.addVariableProvider(new RcfgVariableProvider<STATE, LOC>(symbolTable, boogieVarTable, services))
				.addDebugHelper(debugHelper);

		final FixpointEngine<STATE, CodeBlock, IBoogieVar, LOC> fxpe = new FixpointEngine<STATE, CodeBlock, IBoogieVar, LOC>(
				services, timer, params);
		final Logger logger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		try {
			final AbstractInterpretationResult<STATE, CodeBlock, IBoogieVar, LOC> result = fxpe.run(initial, script,
					bpl2smt);
			if (!result.hasReachedError()) {
				logger.info("NWA was safe (error state unreachable)");
			}
			if (logger.isDebugEnabled()) {
				logger.debug("Found the following predicates:");
				AbsIntUtil.logPredicates(Collections.singletonMap(initial, result.getLoc2Term()), script,
						logger::debug);
			}
			logger.info(result.getBenchmark());
			return result;
		} catch (ToolchainCanceledException c) {
			throw c;
		}
	}

	/**
	 * Run abstract interpretation on the whole RCFG.
	 * 
	 */
	public static IAbstractInterpretationResult<?, CodeBlock, IBoogieVar, ProgramPoint> runOnRCFG(final RootNode root,
			final Collection<CodeBlock> initials, final IProgressAwareTimer timer,
			final IUltimateServiceProvider services, final boolean isSilent) throws Throwable {
		if (initials == null) {
			throw new IllegalArgumentException("No initial edges provided");
		}
		if (timer == null) {
			throw new IllegalArgumentException("timer is null");
		}

		final BoogieSymbolTable symbolTable = getSymbolTable(root);
		if (symbolTable == null) {
			throw new IllegalArgumentException("Could not get BoogieSymbolTable");
		}

		final RootAnnot rootAnnot = root.getRootAnnot();
		final Boogie2SMT bpl2smt = rootAnnot.getBoogie2SMT();
		final Script script = rootAnnot.getScript();
		final Boogie2SmtSymbolTable boogieVarTable = bpl2smt.getBoogie2SmtSymbolTable();
		final ITransitionProvider<CodeBlock, ProgramPoint> transitionProvider = new RcfgTransitionProvider();
		final ILoopDetector<CodeBlock> loopDetector = new RcfgLoopDetector<>(rootAnnot.getLoopLocations().keySet(),
				transitionProvider);

		final IAbstractDomain<?, CodeBlock, IBoogieVar> domain = selectDomain(() -> new RCFGLiteralCollector(root),
				symbolTable, services, rootAnnot);
		return runOnRCFG(initials, timer, services, symbolTable, bpl2smt, script, boogieVarTable, loopDetector, domain,
				transitionProvider, rootAnnot, isSilent);
	}

	private static <STATE extends IAbstractState<STATE, CodeBlock, IBoogieVar>> AbstractInterpretationResult<STATE, CodeBlock, IBoogieVar, ProgramPoint> runOnRCFG(
			final Collection<CodeBlock> initials, final IProgressAwareTimer timer,
			final IUltimateServiceProvider services, final BoogieSymbolTable symbolTable, final Boogie2SMT bpl2smt,
			final Script script, final Boogie2SmtSymbolTable boogieVarTable,
			final ILoopDetector<CodeBlock> loopDetector, final IAbstractDomain<STATE, CodeBlock, IBoogieVar> domain,
			final ITransitionProvider<CodeBlock, ProgramPoint> transitionProvider, final RootAnnot rootAnnot,
			final boolean isSilent) {
		final UltimatePreferenceStore ups = new UltimatePreferenceStore(Activator.PLUGIN_ID);

		final Collection<CodeBlock> filteredInitialElements = transitionProvider.filterInitialElements(initials);
		final boolean persist = ups.getBoolean(AbsIntPrefInitializer.LABEL_PERSIST_ABS_STATES);

		if (filteredInitialElements.isEmpty()) {
			getReporter(services, false, false).reportSafe(null, "The program is empty");
			return null;
		}

		final Logger logger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		final boolean isLib = filteredInitialElements.size() > 1;

		final Iterator<CodeBlock> iter = filteredInitialElements.iterator();
		AbstractInterpretationResult<STATE, CodeBlock, IBoogieVar, ProgramPoint> result = null;
		// TODO: If an if is at the beginning of a method, this method will be analyzed two times
		while (iter.hasNext()) {
			final CodeBlock initial = iter.next();

			final FixpointEngineParameters<STATE, CodeBlock, IBoogieVar, ProgramPoint> params = new FixpointEngineParameters<STATE, CodeBlock, IBoogieVar, ProgramPoint>()
					.addDomain(domain).addLoopDetector(loopDetector)
					.addStorage(createStorage(services, domain, transitionProvider, persist))
					.addTransitionProvider(transitionProvider)
					.addVariableProvider(
							new RcfgVariableProvider<STATE, ProgramPoint>(symbolTable, boogieVarTable, services))
					.addDebugHelper(new RcfgDebugHelper<>(rootAnnot, services));

			final FixpointEngine<STATE, CodeBlock, IBoogieVar, ProgramPoint> fxpe = new FixpointEngine<>(services,
					timer, params);
			result = fxpe.run(initial, script, bpl2smt, result);
		}

		if (result.hasReachedError()) {
			final IResultReporter<STATE, CodeBlock, IBoogieVar, ProgramPoint> reporter = getReporter(services, isLib,
					isSilent);
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

	private static <STATE extends IAbstractState<STATE, CodeBlock, IBoogieVar>, LOC> BaseRcfgAbstractStateStorageProvider<STATE, LOC> createStorage(
			final IUltimateServiceProvider services, final IAbstractDomain<STATE, CodeBlock, IBoogieVar> domain,
			final ITransitionProvider<CodeBlock, LOC> transprovider, final boolean persist) {
		final BaseRcfgAbstractStateStorageProvider<STATE, LOC> storage;
		if (persist) {
			storage = new AnnotatingRcfgAbstractStateStorageProvider<STATE, LOC>(domain.getMergeOperator(), services,
					transprovider);
		} else {
			storage = new RcfgAbstractStateStorageProvider<STATE, LOC>(domain.getMergeOperator(), services,
					transprovider);
		}
		return storage;
	}

	private static BoogieSymbolTable getSymbolTable(final RootNode root) {
		final PreprocessorAnnotation pa = PreprocessorAnnotation.getAnnotation(root);
		if (pa == null) {
			return null;
		}
		return pa.getSymbolTable();
	}

	private static IAbstractDomain<?, CodeBlock, IBoogieVar> selectDomain(
			final LiteralCollectorFactory literalCollector, final BoogieSymbolTable symbolTable,
			final IUltimateServiceProvider services, final RootAnnot rootAnnotation) {
		final UltimatePreferenceStore ups = new UltimatePreferenceStore(Activator.PLUGIN_ID);
		final String selectedDomain = ups.getString(AbsIntPrefInitializer.LABEL_ABSTRACT_DOMAIN);
		final Logger logger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		// use the literal collector result if you need it
		// new LiteralCollector(root).getResult();

		if (EmptyDomain.class.getSimpleName().equals(selectedDomain)) {
			return new EmptyDomain<>();
		} else if (SignDomain.class.getSimpleName().equals(selectedDomain)) {
			return new SignDomain(services);
		} else if (IntervalDomain.class.getSimpleName().equals(selectedDomain)) {
			return new IntervalDomain(logger, symbolTable, literalCollector.create().getLiteralCollection());
		} else if (OctagonDomain.class.getSimpleName().equals(selectedDomain)) {
			return new OctagonDomain(logger, symbolTable, literalCollector);
		} else if (VPDomain.class.getSimpleName().equals(selectedDomain)) {
			return new VPDomain(services);
		} else if (CongruenceDomain.class.getSimpleName().equals(selectedDomain)) {
			return new CongruenceDomain(logger, symbolTable);
		} else if (CompoundDomain.class.getSimpleName().equals(selectedDomain)) {
			@SuppressWarnings("rawtypes")
			List<IAbstractDomain> domainList = new ArrayList<>();
			if (ups.getBoolean(CompoundDomainPreferences.LABEL_USE_EMPTY_DOMAIN)) {
				domainList.add(new EmptyDomain<>());
			}
			if (ups.getBoolean(CompoundDomainPreferences.LABEL_USE_SIGN_DOMAIN)) {
				domainList.add(new SignDomain(services));
			}
			if (ups.getBoolean(CompoundDomainPreferences.LABEL_USE_CONGRUENCE_DOMAIN)) {
				domainList.add(new CongruenceDomain(logger, symbolTable));
			}
			if (ups.getBoolean(CompoundDomainPreferences.LABEL_USE_INTERVAL_DOMAIN)) {
				domainList
						.add(new IntervalDomain(logger, symbolTable, literalCollector.create().getLiteralCollection()));
			}
			if (ups.getBoolean(CompoundDomainPreferences.LABEL_USE_OCTAGON_DOMAIN)) {
				domainList.add(new OctagonDomain(logger, symbolTable, literalCollector));
			}
			return new CompoundDomain(services, domainList, rootAnnotation);
		}
		throw new UnsupportedOperationException("The value \"" + selectedDomain + "\" of preference \""
				+ AbsIntPrefInitializer.LABEL_ABSTRACT_DOMAIN + "\" was not considered before! ");
	}

	private static <STATE extends IAbstractState<STATE, CodeBlock, VARDECL>, VARDECL> IResultReporter<STATE, CodeBlock, VARDECL, ProgramPoint> getReporter(
			final IUltimateServiceProvider services, final boolean isLibrary, final boolean isSilent) {
		if (isSilent) {
			return new SilentReporter<>();
		}
		if (isLibrary) {
			return new RcfgLibraryModeResultReporter<STATE, VARDECL>(services);
		} else {
			return new RcfgResultReporter<STATE, VARDECL>(services);
		}
	}

	@FunctionalInterface
	public interface LiteralCollectorFactory {
		RCFGLiteralCollector create();
	}
}
