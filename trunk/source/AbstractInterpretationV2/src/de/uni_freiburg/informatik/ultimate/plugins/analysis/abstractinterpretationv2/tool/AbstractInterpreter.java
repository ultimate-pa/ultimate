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
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.boogie.type.PreprocessorAnnotation;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.core.services.model.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SmtSymbolTable;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.AbstractInterpretationBenchmark;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.FixpointEngine;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.ILoopDetector;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.IResultReporter;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.ITransitionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.IVariableProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.generic.LiteralCollection;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.generic.SilentReporter;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.nwa.NWAPathProgramTransitionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.AnnotatingRcfgAbstractStateStorageProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.BaseRcfgAbstractStateStorageProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RCFGLiteralCollector;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgAbstractStateStorageProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgLibraryModeResultReporter;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgLoopDetector;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgResultReporter;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgTransitionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgVariableProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.empty.EmptyDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval.IntervalDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.sign.SignDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon.OctagonDomain;
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
	 */
	public static Map<CodeBlock, Map<ProgramPoint, Term>> runSilently(final RootNode root,
			final Collection<CodeBlock> initials, final IProgressAwareTimer timer,
			final IUltimateServiceProvider services) {
		final Logger logger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		final Map<CodeBlock, Map<ProgramPoint, Term>> predicates = new HashMap<CodeBlock, Map<ProgramPoint, Term>>();
		try {
			runOnRCFG(root, initials, timer, services, (a, b, isLib) -> new SilentReporter<>(), predicates);
		} catch (OutOfMemoryError oom) {
			throw oom;
		} catch (IllegalArgumentException iae) {
			throw iae;
		} catch (ToolchainCanceledException tce) {
			// suppress timeout results / timeouts
			return predicates;
		} catch (Throwable t) {
			logger.fatal("Suppressed exception in AIv2: " + t.getMessage());
			return predicates;
		}
		return predicates;
	}

	/**
	 * Run abstract interpretation on a path program constructed from a counterexample.
	 * 
	 * @param counterexample
	 * @param currentAutomata
	 * @param timer
	 * @param mServices
	 * @return
	 */
	public static <LOC> Map<LOC, Term> runSilently(final NestedRun<CodeBlock, LOC> counterexample,
			final INestedWordAutomatonOldApi<CodeBlock, LOC> currentAutomata, final RootNode root,
			final IProgressAwareTimer timer, final IUltimateServiceProvider services) {
		assert counterexample != null && counterexample.getLength() > 0 : "Invalid counterexample";
		assert currentAutomata != null;
		assert root != null;
		assert services != null;
		assert timer != null;

		final Logger logger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		final Map<LOC, Term> predicates = new HashMap<>();
		try {
			final NWAPathProgramTransitionProvider<LOC> transProvider = new NWAPathProgramTransitionProvider<>(
					currentAutomata, counterexample, services, root.getRootAnnot());
			runSilentlyOnNWA(transProvider, counterexample.getSymbol(0), root, timer, services, predicates);
		} catch (OutOfMemoryError oom) {
			throw oom;
		} catch (IllegalArgumentException iae) {
			throw iae;
		} catch (ToolchainCanceledException tce) {
			// suppress timeout results / timeouts
			return predicates;
		} catch (Throwable t) {
			logger.fatal("Suppressed exception in AIv2: " + t.getClass().getSimpleName() + " with message "
					+ t.getMessage());
			throw new RuntimeException(t);
			// return predicates;
		}
		return predicates;
	}

	private static <LOC> void runSilentlyOnNWA(final NWAPathProgramTransitionProvider<LOC> transProvider,
			final CodeBlock initial, final RootNode root, final IProgressAwareTimer timer,
			final IUltimateServiceProvider services, final Map<LOC, Term> predicates) throws Throwable {
		// TODO Auto-generated method stub

		final BoogieSymbolTable symbolTable = getSymbolTable(root);
		if (symbolTable == null) {
			throw new IllegalArgumentException("Could not get BoogieSymbolTable");
		}

		final RootAnnot rootAnnot = root.getRootAnnot();
		final Boogie2SMT bpl2smt = rootAnnot.getBoogie2SMT();
		final Script script = rootAnnot.getScript();
		final Boogie2SmtSymbolTable boogieVarTable = bpl2smt.getBoogie2SmtSymbolTable();

		final IAbstractDomain<?, CodeBlock, IBoogieVar> domain = selectDomain(
				() -> new RCFGLiteralCollector(root), symbolTable, services);

		runSilentlyOnNWA(initial, timer, services, predicates, symbolTable, bpl2smt, script, boogieVarTable, domain,
				transProvider, transProvider);
	}

	private static <STATE extends IAbstractState<STATE, CodeBlock, IBoogieVar>, LOC> void runSilentlyOnNWA(
			CodeBlock initial, IProgressAwareTimer timer, IUltimateServiceProvider services, Map<LOC, Term> predicates,
			final BoogieSymbolTable symbolTable, final Boogie2SMT bpl2smt, final Script script,
			final Boogie2SmtSymbolTable boogieVarTable, final IAbstractDomain<STATE, CodeBlock, IBoogieVar> domain,
			final ITransitionProvider<CodeBlock, LOC> transitionProvider, ILoopDetector<CodeBlock> loopDetector) {

		final BaseRcfgAbstractStateStorageProvider<STATE, LOC> storage = new RcfgAbstractStateStorageProvider<STATE, LOC>(
				domain.getMergeOperator(), services, transitionProvider);
		final IResultReporter<CodeBlock> reporter = new SilentReporter<>();
		final IVariableProvider<STATE, CodeBlock, IBoogieVar, LOC> varProvider = new RcfgVariableProvider<STATE, LOC>(
				symbolTable, boogieVarTable, services);
		
		final AbstractInterpretationBenchmark<CodeBlock, LOC> benchmark = new AbstractInterpretationBenchmark<>();
		final FixpointEngine<STATE, CodeBlock, IBoogieVar, LOC> fxpe = new FixpointEngine<STATE, CodeBlock, IBoogieVar, LOC>(
				services, timer, transitionProvider, storage, domain, varProvider, loopDetector, reporter,benchmark);
		final Logger logger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		try {
			boolean safe = fxpe.run(initial);
			if (safe) {
				logger.info("NWA was safe (error state unreachable)");
			}
		} catch (ToolchainCanceledException c) {
			predicates.putAll(storage.getTerms(initial, script, bpl2smt));
			throw c;
		}
		predicates.putAll(storage.getTerms(initial, script, bpl2smt));
		logPredicates(logger, initial, predicates, script);
		logger.info(benchmark);
	}

	/**
	 * Run abstract interpretation on the whole RCFG.
	 * 
	 */
	public static Map<CodeBlock, Map<ProgramPoint, Term>> run(final RootNode root, final Collection<CodeBlock> initials,
			final IProgressAwareTimer timer, final IUltimateServiceProvider services) throws Throwable {
		final Map<CodeBlock, Map<ProgramPoint, Term>> predicates = new HashMap<CodeBlock, Map<ProgramPoint, Term>>();
		runOnRCFG(root, initials, timer, services,
				(a, b, libMode) -> libMode ? new RcfgLibraryModeResultReporter(a, b) : new RcfgResultReporter(a, b),
				predicates);
		return predicates;
	}

	private static void runOnRCFG(final RootNode root, final Collection<CodeBlock> initials,
			final IProgressAwareTimer timer, final IUltimateServiceProvider services,
			final ReporterFactory funCreateReporter, final Map<CodeBlock, Map<ProgramPoint, Term>> predicates)
					throws Throwable {
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

		final IAbstractDomain<?, CodeBlock, IBoogieVar> domain = selectDomain(
				() -> new RCFGLiteralCollector(root), symbolTable, services);
		runOnRCFG(initials, timer, services, funCreateReporter, predicates, symbolTable, bpl2smt, script,
				boogieVarTable, loopDetector, domain, transitionProvider);
	}

	private static <STATE extends IAbstractState<STATE, CodeBlock, IBoogieVar>> void runOnRCFG(
			final Collection<CodeBlock> initials, final IProgressAwareTimer timer,
			final IUltimateServiceProvider services, final ReporterFactory funCreateReporter,
			final Map<CodeBlock, Map<ProgramPoint, Term>> predicates, final BoogieSymbolTable symbolTable,
			final Boogie2SMT bpl2smt, final Script script, final Boogie2SmtSymbolTable boogieVarTable,
			final ILoopDetector<CodeBlock> loopDetector, final IAbstractDomain<STATE, CodeBlock, IBoogieVar> domain,
			final ITransitionProvider<CodeBlock, ProgramPoint> transitionProvider) {
		final UltimatePreferenceStore ups = new UltimatePreferenceStore(Activator.PLUGIN_ID);

		final Collection<CodeBlock> filteredInitialElements = transitionProvider.filterInitialElements(initials);
		final boolean persist = ups.getBoolean(AbsIntPrefInitializer.LABEL_PERSIST_ABS_STATES);

		if (filteredInitialElements.isEmpty()) {
			final BaseRcfgAbstractStateStorageProvider<STATE, ProgramPoint> storage = createStorage(services, domain,
					transitionProvider, persist);
			final IResultReporter<CodeBlock> reporter = funCreateReporter.create(services, storage, false);
			reporter.reportSafe(null, "The program is empty");
			return;
		}

		final AbstractInterpretationBenchmark<CodeBlock, ProgramPoint> benchmark = new AbstractInterpretationBenchmark<>();
		final Logger logger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		boolean allSafe = true;
		final boolean isLib = filteredInitialElements.size() > 1;

		final Iterator<CodeBlock> iter = filteredInitialElements.iterator();
		// TODO: If an if is at the beginning of a method, this method will be analyzed two times
		while (iter.hasNext()) {
			final CodeBlock initial = iter.next();
			final BaseRcfgAbstractStateStorageProvider<STATE, ProgramPoint> storage = createStorage(services, domain,
					transitionProvider, persist);
			final IResultReporter<CodeBlock> reporter = funCreateReporter.create(services, storage, isLib);
			final IVariableProvider<STATE, CodeBlock, IBoogieVar, ProgramPoint> varProvider = new RcfgVariableProvider<STATE, ProgramPoint>(
					symbolTable, boogieVarTable, services);
			
			final FixpointEngine<STATE, CodeBlock, IBoogieVar, ProgramPoint> fxpe = new FixpointEngine<STATE, CodeBlock, IBoogieVar, ProgramPoint>(
					services, timer, transitionProvider, storage, domain, varProvider, loopDetector, reporter,
					benchmark);
			try {
				allSafe = fxpe.run(initial) && allSafe;
			} catch (ToolchainCanceledException c) {
				predicates.put(initial, storage.getTerms(initial, script, bpl2smt));
				throw c;
			}
			final Map<ProgramPoint, Term> localPredicates = storage.getTerms(initial, script, bpl2smt);
			predicates.put(initial, localPredicates);
			if (!iter.hasNext() && allSafe) {
				// report all safe
				funCreateReporter.create(services, storage, false).reportSafe(null);
			}
			
			logPredicates(logger, initial, localPredicates, script);
		}
		
		logger.info(benchmark);
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
			final IUltimateServiceProvider services) {
		final UltimatePreferenceStore ups = new UltimatePreferenceStore(Activator.PLUGIN_ID);
		final String selectedDomain = ups.getString(AbsIntPrefInitializer.LABEL_ABSTRACT_DOMAIN);

		// use the literal collector result if you need it
		// new LiteralCollector(root).getResult();

		if (EmptyDomain.class.getSimpleName().equals(selectedDomain)) {
			return new EmptyDomain<>();
		} else if (SignDomain.class.getSimpleName().equals(selectedDomain)) {
			return new SignDomain(services);
		} else if (IntervalDomain.class.getSimpleName().equals(selectedDomain)) {
			return new IntervalDomain(services.getLoggingService().getLogger(Activator.PLUGIN_ID), symbolTable,
					literalCollector.create().getLiteralCollection());
		} else if (OctagonDomain.class.getSimpleName().equals(selectedDomain)) {
			Logger logger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
			return new OctagonDomain(logger, symbolTable, literalCollector);
		}
		throw new UnsupportedOperationException("The value \"" + selectedDomain + "\" of preference \""
				+ AbsIntPrefInitializer.LABEL_ABSTRACT_DOMAIN + "\" was not considered before! ");
	}

	private static void logPredicates(Logger logger, CodeBlock initial, Map<?, Term> predicates, Script script) {
		logger.info("Found the following predicates:");
		AbsIntUtil.logPredicates(Collections.singletonMap(initial, predicates), script, logger::info);
	}

	@FunctionalInterface
	private interface ReporterFactory {
		IResultReporter<CodeBlock> create(final IUltimateServiceProvider services,
				final BaseRcfgAbstractStateStorageProvider<?, ?> storage, final boolean isLibrary);
	}

	@FunctionalInterface
	public interface LiteralCollectorFactory {
		RCFGLiteralCollector create();
	}
}
