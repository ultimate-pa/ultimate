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
import java.util.HashMap;
import java.util.Map;
import java.util.function.BiFunction;

import org.apache.log4j.Logger;

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
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.LiteralCollector;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.FixpointEngine;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.ILoopDetector;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.IResultReporter;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.ITransitionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.IVariableProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.AnnotatingRcfgAbstractStateStorageProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.BaseRcfgAbstractStateStorageProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.DummyReporter;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgAbstractStateStorageProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgLoopDetector;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgResultReporter;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgTransitionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgVariableProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.empty.EmptyDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval.IntervalDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.sign.SignDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.preferences.AbsIntPrefInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.loopdetector.RCFGLoopDetector;
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
		final Map<CodeBlock, Map<ProgramPoint, Term>> rtr = new HashMap<CodeBlock, Map<ProgramPoint, Term>>();
		try {
			runInternal(root, initials, timer, services, (a, b) -> new DummyReporter<>(), rtr);
		} catch (OutOfMemoryError oom) {
			throw oom;
		} catch (IllegalArgumentException iae) {
			throw iae;
		} catch (ToolchainCanceledException tce) {
			// suppress timeout results / timeouts
			return rtr;
		} catch (Throwable t) {
			logger.fatal("Suppressed exception in AIv2: " + t.getMessage());
			return rtr;
		}
		return rtr;
	}

	/**
	 * Run abstract interpretation on the whole RCFG.
	 * 
	 */
	public static Map<CodeBlock, Map<ProgramPoint, Term>> run(final RootNode root, final Collection<CodeBlock> initials,
	        final IProgressAwareTimer timer, final IUltimateServiceProvider services) throws Throwable {
		final Map<CodeBlock, Map<ProgramPoint, Term>> rtr = new HashMap<CodeBlock, Map<ProgramPoint, Term>>();
		runInternal(root, initials, timer, services, (a, b) -> new RcfgResultReporter(a, b), rtr);
		return rtr;
	}

	private static void runInternal(final RootNode root, final Collection<CodeBlock> initials,
	        final IProgressAwareTimer timer, final IUltimateServiceProvider services,
	        BiFunction<IUltimateServiceProvider, BaseRcfgAbstractStateStorageProvider<?>, IResultReporter<CodeBlock>> funCreateReporter,
	        Map<CodeBlock, Map<ProgramPoint, Term>> predicates) throws Throwable {
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

		final RCFGLoopDetector externalLoopDetector = new RCFGLoopDetector(services);
		externalLoopDetector.process(root);

		final IAbstractDomain<?, CodeBlock, IBoogieVar> domain = selectDomain(root, symbolTable, services);
		runInternal(initials, timer, services, funCreateReporter, predicates, symbolTable, bpl2smt, script,
		        boogieVarTable, externalLoopDetector, domain);
	}

	private static <STATE extends IAbstractState<STATE, CodeBlock, IBoogieVar>> void runInternal(
	        final Collection<CodeBlock> initials, final IProgressAwareTimer timer,
	        final IUltimateServiceProvider services,
	        BiFunction<IUltimateServiceProvider, BaseRcfgAbstractStateStorageProvider<?>, IResultReporter<CodeBlock>> funCreateReporter,
	        Map<CodeBlock, Map<ProgramPoint, Term>> predicates, final BoogieSymbolTable symbolTable,
	        final Boogie2SMT bpl2smt, final Script script, final Boogie2SmtSymbolTable boogieVarTable,
	        final RCFGLoopDetector externalLoopDetector, final IAbstractDomain<STATE, CodeBlock, IBoogieVar> domain) {
		final UltimatePreferenceStore ups = new UltimatePreferenceStore(Activator.PLUGIN_ID);
		final ITransitionProvider<CodeBlock> transitionProvider = new RcfgTransitionProvider();

		final ILoopDetector<CodeBlock> loopDetector = new RcfgLoopDetector(externalLoopDetector);

		final Collection<CodeBlock> filteredInitialElements = transitionProvider.filterInitialElements(initials);
		final boolean persist = ups.getBoolean(AbsIntPrefInitializer.LABEL_PERSIST_ABS_STATES);

		if (filteredInitialElements.isEmpty()) {
			final BaseRcfgAbstractStateStorageProvider<?> storage = createStorage(services, domain, persist);
			final IResultReporter<CodeBlock> reporter = funCreateReporter.apply(services, storage);
			reporter.reportSafe("The program is empty");
			return;
		}

		for (final CodeBlock initial : filteredInitialElements) {
			final BaseRcfgAbstractStateStorageProvider<STATE> storage = createStorage(services, domain, persist);
			final IResultReporter<CodeBlock> reporter = funCreateReporter.apply(services, storage);
			final IVariableProvider<STATE, CodeBlock, IBoogieVar, ProgramPoint> varProvider = new RcfgVariableProvider<STATE>(
			        symbolTable, boogieVarTable, services);
			final FixpointEngine<STATE, CodeBlock, IBoogieVar, ProgramPoint> interpreter = new FixpointEngine<STATE, CodeBlock, IBoogieVar, ProgramPoint>(
			        services, timer, transitionProvider, storage, domain, varProvider, loopDetector, reporter);
			try {
				interpreter.run(initial);
			} catch (ToolchainCanceledException c) {
				predicates.put(initial, storage.getTerms(initial, script, bpl2smt));
				throw c;
			}
			predicates.put(initial, storage.getTerms(initial, script, bpl2smt));
		}
	}

	private static <STATE extends IAbstractState<STATE, CodeBlock, IBoogieVar>> BaseRcfgAbstractStateStorageProvider<STATE> createStorage(
	        final IUltimateServiceProvider services, final IAbstractDomain<STATE, CodeBlock, IBoogieVar> domain,
	        final boolean persist) {
		final BaseRcfgAbstractStateStorageProvider<STATE> storage;
		if (persist) {
			storage = new AnnotatingRcfgAbstractStateStorageProvider<STATE>(domain.getMergeOperator(), services);
		} else {
			storage = new RcfgAbstractStateStorageProvider<STATE>(domain.getMergeOperator(), services);
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

	private static IAbstractDomain<?, CodeBlock, IBoogieVar> selectDomain(final RootNode root,
	        final BoogieSymbolTable symbolTable, final IUltimateServiceProvider services) {
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
			        new LiteralCollector(root));
		}
		throw new UnsupportedOperationException("The value \"" + selectedDomain + "\" of preference \""
		        + AbsIntPrefInitializer.LABEL_ABSTRACT_DOMAIN + "\" was not considered before! ");
	}
}
