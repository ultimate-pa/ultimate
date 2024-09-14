/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2010-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2018 Lars Nitzke (lars.nitzke@mailfence.com)
 * Copyright (C) 2024 Niklas Kult (niklas111098@gmail.com)
 * Copyright (C) 2015 University of Freiburg
 *
 *
 * This file is part of the ULTIMATE RCFGBuilder plug-in.
 *
 * The ULTIMATE RCFGBuilder plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgBuilder plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE RCFGBuilder plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE RCFGBuilder plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE RCFGBuilder plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.icfgbuilder.cfg;

import java.io.File;
import java.io.IOException;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.Stack;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayStoreExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AtomicStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BreakStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.EnsuresSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ForkStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.GotoStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.JoinStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Label;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LoopInvariantSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.RequiresSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ReturnStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WhileStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WildcardExpression;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.ConditionAnnotation;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.LoopEntryAnnotation;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.LoopEntryAnnotation.LoopEntryType;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.LoopExitAnnotation;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.LoopExitAnnotation.LoopExitType;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.ITranslator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.BoogieDeclarations;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.Statements2TransFormula.TranslationResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ConcurrencyInformation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ThreadInstance;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgElement;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgJoinTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.LoopEntryDebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.OrdinaryDebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.ProcedureEntryDebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.ProcedureErrorDebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.ProcedureErrorDebugIdentifier.ProcedureErrorType;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.ProcedureErrorWithCheckDebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.ProcedureExitDebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.ProcedureFinalDebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.StringDebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfgbuilder.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfgbuilder.IcfgBacktranslator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfgbuilder.WeakestPrecondition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfgbuilder.preferences.IcfgPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfgbuilder.preferences.IcfgPreferenceInitializer.CodeBlockSize;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfgbuilder.util.TransFormulaAdder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.AtomicBlockInfo;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlockFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ForkThreadCurrent;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.GotoEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.JoinThreadCurrent;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.LargeBlockEncoding;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.LargeBlockEncoding.InternalLbeMode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.LiveIcfgUtils;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence.Origin;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;

/**
 * This class generates a recursive control flow graph (in the style of POPL'10
 * - Heizmann, Hoenicke, Podelski - Nested Interpolants) from an Boogie AST
 * which contains only unstructured Code (i.e., no while (and others??)
 * statements). The input for this classs has to be unstructured Boogie Code
 * (e.g., no while loops) for example the output of the BoogiePreprocessor.
 *
 * @author heizmann@informatik.uni-freiburg.de
 */

// TODO How to give every location the right line number
public class CfgBuilder {

	private static final String ULTIMATE_START = "ULTIMATE.start";

	/**
	 * ILogger for this plugin.
	 */
	private final ILogger mLogger;

	/**
	 * Root Node of this Ultimate model. I use this to store information that should
	 * be passed to the next plugin. The Successors of this node are exactly the
	 * entry nodes of procedures.
	 */
	private final BoogieIcfgContainer mIcfg;

	private final Boogie2SMT mBoogie2Smt;
	private final BoogieDeclarations mBoogieDeclarations;
	private TransFormulaAdder mTransFormulaAdder;

	private final Collection<Summary> mImplementationSummarys = new LinkedHashSet<>();

	private final Map<IIcfgForkTransitionThreadCurrent<IcfgLocation>, List<ThreadInstance>> mForks = new HashMap<>();
	private final List<IIcfgJoinTransitionThreadCurrent<IcfgLocation>> mJoins = new ArrayList<>();

	private final IcfgBacktranslator mIcfgBacktranslator;

	private final CodeBlockSize mCodeBlockSize;
	private final boolean mCtxSwitchOnlyAtAtomicBoundaries;

	private final IUltimateServiceProvider mServices;

	private final boolean mAddAssumeForEachAssert;

	private final CodeBlockFactory mCbf;

	private Stack<BoogieIcfgLocation> mWhileExits;
	private Stack<BoogieIcfgLocation> mConditionalStarts;
	private final int mRemovedAssumeTrueStatements = 0;

	private static final SimplificationTechnique SIMPLIFICATION_TECHNIQUE = SimplificationTechnique.POLY_PAC;
	private static final XnfConversionTechnique XNF_CONVERSION_TECHNIQUE = XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION;

	private final Set<String> mAllGotoTargets;

	private final boolean mRemoveAssumeTrueStmt;
	private final boolean mFutureLiveOptimization;

	public CfgBuilder(final Unit unit, final IUltimateServiceProvider services) throws IOException {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		final IPreferenceProvider prefs = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
		mAddAssumeForEachAssert = prefs.getBoolean(IcfgPreferenceInitializer.LABEL_ASSUME_FOR_ASSERT);
		mRemoveAssumeTrueStmt = prefs.getBoolean(IcfgPreferenceInitializer.LABEL_REMOVE_ASSUME_TRUE);

		final String pathAndFilename = ILocation.getAnnotation(unit).getFileName();
		final String filename = new File(pathAndFilename).getName();
		final Script script = constructAndInitializeSolver(services, filename);
		final ManagedScript mgdScript = new ManagedScript(mServices, script);

		mBoogieDeclarations = new BoogieDeclarations(unit, mLogger);
		final boolean simplePartialSkolemization = prefs
				.getBoolean(IcfgPreferenceInitializer.LABEL_SIMPLE_PARTIAL_SKOLEMIZATION);
		final ForkAndGotoInformation fgInfo = new ForkAndGotoInformation(mBoogieDeclarations);
		mAllGotoTargets = fgInfo.getAllGotoTargets();

		final CodeBlockSize userDefineCodeBlockSize = prefs.getEnum(IcfgPreferenceInitializer.LABEL_CODE_BLOCK_SIZE,
				CodeBlockSize.class);
		if ((userDefineCodeBlockSize == CodeBlockSize.LoopFreeBlock
				|| userDefineCodeBlockSize == CodeBlockSize.SequenceOfStatements) && fgInfo.hasSomeForkEdge()) {
			mCodeBlockSize = CodeBlockSize.OneNontrivialStatement;
			mLogger.warn("User set CodeBlockSize to " + userDefineCodeBlockSize
					+ " but program contains fork statements. Overwriting the user preferences and setting CodeBlockSize to "
					+ mCodeBlockSize);
		} else {
			mCodeBlockSize = userDefineCodeBlockSize;
		}
		mCtxSwitchOnlyAtAtomicBoundaries = prefs
				.getBoolean(IcfgPreferenceInitializer.LABEL_CONTEXT_SWITCH_ONLY_AT_ATOMIC_BOUNDARIES);

		mFutureLiveOptimization = prefs.getBoolean(IcfgPreferenceInitializer.LABEL_FUTURE_LIVE);

		mBoogie2Smt = new Boogie2SMT(mgdScript, mBoogieDeclarations, mServices, simplePartialSkolemization);
		final IcfgBacktranslator backtranslator = new IcfgBacktranslator(mLogger);
		backtranslator.setTerm2Expression(mBoogie2Smt.getTerm2Expression());
		mIcfgBacktranslator = backtranslator;

		final ConcurrencyInformation ci = new ConcurrencyInformation(mForks, Collections.emptyMap(), mJoins);
		mIcfg = new BoogieIcfgContainer(mServices, mBoogieDeclarations, mBoogie2Smt, ci);
		mCbf = mIcfg.getCodeBlockFactory();
		mCbf.storeFactory(mServices.getStorage());
	}

	/**
	 * Build a recursive control flow graph for an unstructured boogie program.
	 *
	 * @param Unit that encodes a program.
	 * @return RootNode of a recursive control flow graph.
	 */
	public IIcfg<BoogieIcfgLocation> createIcfg(final Unit unit) {
		mLogger.info("Building ICFG");
		mTransFormulaAdder = new TransFormulaAdder(mBoogie2Smt, mServices);

		// Build entry, final and exit node for all procedures that have an
		// implementation
		final BoogieIcfgContainer icfg = mIcfg;
		for (final String procName : mBoogieDeclarations.getProcImplementation().keySet()) {
			final Body body = mBoogieDeclarations.getProcImplementation().get(procName).getBody();
			final Statement firstStatement;
			if (body.getBlock().length == 0) {
				firstStatement = new ReturnStatement(
						mBoogieDeclarations.getProcImplementation().get(procName).getLocation());
			} else {
				firstStatement = body.getBlock()[0];
			}
			final BoogieIcfgLocation entryNode = new BoogieIcfgLocation(new ProcedureEntryDebugIdentifier(procName),
					procName, false, firstStatement);
			// We have to use some ASTNode for final and exit node. Let's take
			// the procedure implementation.
			final Procedure impl = mBoogieDeclarations.getProcImplementation().get(procName);
			icfg.getProcedureEntryNodes().put(procName, entryNode);
			final BoogieIcfgLocation finalNode = new BoogieIcfgLocation(new ProcedureFinalDebugIdentifier(procName),
					procName, false, impl);
			icfg.mFinalNode.put(procName, finalNode);
			final BoogieIcfgLocation exitNode = new BoogieIcfgLocation(new ProcedureExitDebugIdentifier(procName),
					procName, false, impl);
			icfg.getProcedureExitNodes().put(procName, exitNode);

			// new RootEdge(mGraphroot, mRootAnnot.mentryNode.get(procName));
		}

		// Build a control flow graph for each procedure
		mLogger.info("Building CFG for each procedure with an implementation");
		final ProcedureCfgBuilder procCfgBuilder = new ProcedureCfgBuilder();
		for (final String procName : mBoogieDeclarations.getProcSpecification().keySet()) {
			if (mBoogieDeclarations.getProcImplementation().containsKey(procName)) {
				procCfgBuilder.buildProcedureCfgFromImplementation(procName);
			} else {
				// procCfgBuilder.buildProcedureCfgWithoutImplementation(procName);
			}
		}

		// Transform CFGs to a recursive CFG
		for (final Summary se : mImplementationSummarys) {
			addCallTransitionAndReturnTransition(se, SIMPLIFICATION_TECHNIQUE);
		}

		if (mFutureLiveOptimization) {
			if (icfg.getCfgSmtToolkit().getConcurrencyInformation().getThreadInstanceMap().isEmpty()) {
				LiveIcfgUtils.applyFutureLiveOptimization(mServices, icfg);
			} else {
				mLogger.info("Ommited future-live optimization because the input is a concurrent program.");
			}
		}

		mLogger.info("Performing block encoding");
		switch (mCodeBlockSize) {
		case LoopFreeBlock:
			new LargeBlockEncoding(mServices, mIcfg, mCbf, InternalLbeMode.ALL);
			break;
		case SequenceOfStatements: // handled in ProcedureCfgBuilder
		case OneNontrivialStatement:
		case SingleStatement:
			final var internalMode = mCtxSwitchOnlyAtAtomicBoundaries ? InternalLbeMode.ALL_EXCEPT_ATOMIC_BOUNDARIES
					: InternalLbeMode.ONLY_ATOMIC_BLOCK;
			new LargeBlockEncoding(mServices, mIcfg, mCbf, internalMode);
			break;
		default:
			throw new AssertionError("unknown value: " + mCodeBlockSize);
		}
		ensureAtomicCompositionComplete();

		final Set<BoogieIcfgLocation> initialNodes = icfg.getProcedureEntryNodes().entrySet().stream()
				.filter(a -> a.getKey().equals(ULTIMATE_START)).map(Entry::getValue).collect(Collectors.toSet());
		if (initialNodes.isEmpty()) {
			mLogger.info("Using library mode");
			icfg.getInitialNodes().addAll(icfg.getProcedureEntryNodes().values());
		} else {
			mLogger.info("Using the " + initialNodes.size() + " location(s) as analysis (start of procedure "
					+ ULTIMATE_START + ")");
			icfg.getInitialNodes().addAll(initialNodes);
		}
		ModelUtils.copyAnnotations(unit, icfg);
		mLogger.info("Removed " + mRemovedAssumeTrueStatements + " assume(true) statements.");

		return icfg;
	}

	private Stream<BoogieIcfgLocation> getAllLocations() {
		return mIcfg.getProgramPoints().entrySet().stream().flatMap(e -> e.getValue().values().stream());
	}

	private Stream<IcfgEdge> getAllEdges() {
		return getAllLocations().flatMap(loc -> loc.getOutgoingEdges().stream()).distinct();
	}

	private void ensureAtomicCompositionComplete() {
		final Iterable<IcfgEdge> edges = getAllEdges()::iterator;
		for (final var edge : edges) {
			ensureAtomicCompositionComplete(edge);
		}
	}

	private void ensureAtomicCompositionComplete(final IcfgEdge edge) {
		if (AtomicBlockInfo.isEndOfAtomicBlock(edge)) {
			// We must never have any dangling ends of atomic blocks;
			// such an edge should have been fused with the corresponding start of the
			// atomic block.
			throw new UnsupportedOperationException("Incomplete atomic composition (dangling end of atomic block: "
					+ edge + "). Is there illegal control flow (e.g. loops) within an atomic block?");
		}

		// If the edge is neither the start nor the end of an atomic block, everything
		// is fine.
		if (!AtomicBlockInfo.isStartOfAtomicBlock(edge)) {
			// Edge may be marked as complete atomic block.
			// If so, remove the annotation as it is only for internal use.
			AtomicBlockInfo.removeAnnotation(edge);
			return;
		}

		final var successor = (BoogieIcfgLocation) edge.getTarget();
		if (successor.isErrorLocation()) {
			// Assert statements in atomic blocks are ok.
			// Remove the annotation as it is only for internal use.
			AtomicBlockInfo.removeAnnotation(edge);
			return;
		}

		// We tolerate nodes without successors inside atomic blocks, such as thread
		// exit locations.
		final boolean successorIsSink = successor.getOutgoingEdges().isEmpty();
		if (!successorIsSink) {
			throw new UnsupportedOperationException("Incomplete atomic composition (dangling start of atomic block: "
					+ edge + "). Is there illegal control flow (e.g. loops) within an atomic block?");
		}
		mLogger.warn("Unexpected successor node of atomic block begin: %s is not an error location.", successor);

		// Remove the annotation as it is only for internal use.
		AtomicBlockInfo.removeAnnotation(edge);
	}

	public Boogie2SMT getBoogie2Smt() {
		return mBoogie2Smt;
	}

	/**
	 * @param services
	 * @param filename
	 */
	private Script constructAndInitializeSolver(final IUltimateServiceProvider services, final String filename) {

		final IPreferenceProvider prefs = mServices.getPreferenceProvider(Activator.PLUGIN_ID);

		final SolverMode solverMode = prefs.getEnum(IcfgPreferenceInitializer.LABEL_SOLVER, SolverMode.class);

		final boolean fakeNonIncrementalScript = prefs
				.getBoolean(IcfgPreferenceInitializer.LABEL_FAKE_NON_INCREMENTAL_SCRIPT);

		final boolean dumpSmtScriptToFile = prefs.getBoolean(IcfgPreferenceInitializer.LABEL_DUMP_TO_FILE);
		final boolean compressSmtScript = prefs.getBoolean(IcfgPreferenceInitializer.LABEL_COMPRESS_SMT_DUMP_FILE);
		final String pathOfDumpedScript = prefs.getString(IcfgPreferenceInitializer.LABEL_DUMP_PATH);

		final String commandExternalSolver = prefs.getString(IcfgPreferenceInitializer.LABEL_EXT_SOLVER_COMMAND);

		final boolean dumpUnsatCoreTrackBenchmark = prefs
				.getBoolean(IcfgPreferenceInitializer.LABEL_DUMP_UNSAT_CORE_BENCHMARK);

		final boolean dumpMainTrackBenchmark = prefs
				.getBoolean(IcfgPreferenceInitializer.LABEL_DUMP_MAIN_TRACK_BENCHMARK);

		final Map<String, String> additionalSmtOptions = prefs
				.getKeyValueMap(IcfgPreferenceInitializer.LABEL_ADDITIONAL_SMT_OPTIONS);

		final Logics logicForExternalSolver = Logics
				.valueOf(prefs.getString(IcfgPreferenceInitializer.LABEL_EXT_SOLVER_LOGIC));
		final SolverSettings solverSettings = SolverBuilder.constructSolverSettings()
				.setUseFakeIncrementalScript(fakeNonIncrementalScript)
				.setDumpSmtScriptToFile(dumpSmtScriptToFile, pathOfDumpedScript, filename, compressSmtScript)
				.setDumpUnsatCoreTrackBenchmark(dumpUnsatCoreTrackBenchmark)
				.setDumpMainTrackBenchmark(dumpMainTrackBenchmark)
				.setUseExternalSolver(true, commandExternalSolver, logicForExternalSolver).setSolverMode(solverMode)
				.setAdditionalOptions(additionalSmtOptions);

		return SolverBuilder.buildAndInitializeSolver(services, solverSettings, "CfgBuilderScript");
	}

	private static Expression getNegation(final Expression expr) {
		if (expr == null) {
			return null;
		}
		return new UnaryExpression(expr.getLocation(), BoogieType.TYPE_BOOL, UnaryExpression.Operator.LOGICNEG, expr);
	}

	/**
	 * Add CallEdge from SummaryEdge source to the entry location of the called
	 * procedure. Add ReturnEdge from the called procedures exit node to the summary
	 * edges target.
	 *
	 * @param simplificationTechnique
	 *
	 * @param SummaryEdge             that summarizes execution of an implemented
	 *                                procedure.
	 */
	private void addCallTransitionAndReturnTransition(final Summary edge,
			final SimplificationTechnique simplificationTechnique) {
		final CallStatement st = edge.getCallStatement();
		final String callee = st.getMethodName();
		assert mIcfg.getProcedureEntryNodes().containsKey(callee)
				: "Source code contains" + " call of " + callee + " but no such procedure.";

		// Add call transition from callerNode to procedures entry node
		final BoogieIcfgLocation callerNode = (BoogieIcfgLocation) edge.getSource();
		final BoogieIcfgLocation calleeEntryLoc = mIcfg.getProcedureEntryNodes().get(callee);

		final String caller = callerNode.getProcedure();

		final TranslationResult arguments2InParams = mIcfg.getBoogie2SMT().getStatements2TransFormula()
				.inParamAssignment(st, simplificationTechnique);
		final TranslationResult outParams2CallerVars = mIcfg.getBoogie2SMT().getStatements2TransFormula()
				.resultAssignment(st, caller, simplificationTechnique);
		final Map<String, ILocation> overapproximations = new HashMap<>();
		overapproximations.putAll(arguments2InParams.getOverapproximations());
		overapproximations.putAll(outParams2CallerVars.getOverapproximations());

		final Call call = mCbf.constructCall(callerNode, calleeEntryLoc, st);
		call.setTransitionFormula(arguments2InParams.getTransFormula());
		if (!overapproximations.isEmpty()) {
			new Overapprox(overapproximations).annotate(call);
		}

		final BoogieIcfgLocation returnNode = (BoogieIcfgLocation) edge.getTarget();
		final BoogieIcfgLocation calleeExitLoc = mIcfg.getProcedureExitNodes().get(callee);
		final Return returnAnnot = mCbf.constructReturn(calleeExitLoc, returnNode, call);
		returnAnnot.setTransitionFormula(outParams2CallerVars.getTransFormula());
	}

	/**
	 * construct error location BoogieASTNode in procedure procName add constructed
	 * location to mprocLocNodes and mErrorNodes.
	 *
	 * @return
	 */
	private BoogieIcfgLocation addErrorNode(final String procName, final BoogieASTNode boogieASTNode,
			final Map<DebugIdentifier, BoogieIcfgLocation> procLocNodes) {
		Set<BoogieIcfgLocation> errorNodes = mIcfg.getProcedureErrorNodes().get(procName);
		final int locNodeNumber;
		if (errorNodes == null) {
			errorNodes = new LinkedHashSet<>();
			mIcfg.getProcedureErrorNodes().put(procName, errorNodes);
			locNodeNumber = 0;
		} else {
			locNodeNumber = errorNodes.size();
		}

		final ProcedureErrorType type;
		if (boogieASTNode instanceof AssertStatement) {
			type = ProcedureErrorType.ASSERT_VIOLATION;
		} else if (boogieASTNode instanceof EnsuresSpecification) {
			type = ProcedureErrorType.ENSURES_VIOLATION;
		} else if (boogieASTNode instanceof RequiresSpecification) {
			type = ProcedureErrorType.REQUIRES_VIOLATION;
		} else if (boogieASTNode instanceof ForkStatement) {
			type = ProcedureErrorType.INUSE_VIOLATION;
		} else {
			throw new IllegalArgumentException();
		}

		final ProcedureErrorDebugIdentifier errorLocLabel;
		final Check check = Check.getAnnotation(boogieASTNode);
		if (check == null) {
			throw new IllegalArgumentException(
					"Constructing error location without specification for the following AST node: " + boogieASTNode);
		}
		errorLocLabel = new ProcedureErrorWithCheckDebugIdentifier(procName, locNodeNumber, type, check);
		final BoogieIcfgLocation errorLocNode = new BoogieIcfgLocation(errorLocLabel, procName, true, boogieASTNode);
		check.annotate(errorLocNode);
		procLocNodes.put(errorLocLabel, errorLocNode);
		errorNodes.add(errorLocNode);
		return errorLocNode;
	}

	public ITranslator<IIcfgTransition<IcfgLocation>, BoogieASTNode, Term, Expression, IcfgLocation, String, ILocation> getBacktranslator() {
		return mIcfgBacktranslator;
	}

	/**
	 * Provides two informations that can be obtained by traversing all statements.
	 * <ul>
	 * <li>information whether some {@link ForkStatement} occurs.
	 * <li>the identifiers of all {@link Label}s that are target of some
	 * {@link GotoStatement}
	 * </ul>
	 * Expects that the input has been "unstructured", i.e., all
	 * {@link WhileStatement}s and {@link IfStatement}s have been removed.
	 */
	private static class ForkAndGotoInformation {

		private boolean mHasSomeForkStatement;
		private final Set<String> mAllGotoTargets;

		public ForkAndGotoInformation(final BoogieDeclarations boogieDeclarations) {
			mAllGotoTargets = new HashSet<>();
			for (final Entry<String, Procedure> entry : boogieDeclarations.getProcImplementation().entrySet()) {
				final Procedure proc = entry.getValue();
				final Body body = proc.getBody();
				processStatements(body.getBlock());
			}
		}

		private void processStatements(final Statement[] statements) {
			for (final Statement st : statements) {
				if (st instanceof ForkStatement) {
					mHasSomeForkStatement = true;
				} else if (st instanceof GotoStatement) {
					mAllGotoTargets.addAll(Arrays.asList(((GotoStatement) st).getLabels()));
				} else if (st instanceof AtomicStatement) {
					processStatements(((AtomicStatement) st).getBody());
				} else if (st instanceof AssignmentStatement || st instanceof AssumeStatement
						|| st instanceof HavocStatement || st instanceof Label || st instanceof JoinStatement
						|| st instanceof CallStatement || st instanceof ReturnStatement || st instanceof AssertStatement
						|| st instanceof BreakStatement) {
					// do nothing
				} else if (st instanceof IfStatement) {
					processStatements(((IfStatement) st).getThenPart());
					processStatements(((IfStatement) st).getElsePart());
				} else if (st instanceof WhileStatement) {
					processStatements(((WhileStatement) st).getBody());
				} else {
					throw new UnsupportedOperationException(
							"Did not expect statement of type " + st.getClass().getSimpleName());
				}
			}
		}

		public boolean hasSomeForkEdge() {
			return mHasSomeForkStatement;
		}

		public Set<String> getAllGotoTargets() {
			return mAllGotoTargets;
		}
	}

	/**
	 * Build control flow graph of single procedures.
	 *
	 * @author heizmann@informatik.uni-freiburg.de
	 */
	private final class ProcedureCfgBuilder {

		/**
		 * Maps a position identifier to the LocNode that represents this position in
		 * the CFG.
		 */
		private Map<DebugIdentifier, BoogieIcfgLocation> mProcLocNodes;

		/**
		 * Maps a Label identifier to the LocNode that represents this Label in the CFG.
		 */
		private Map<DebugIdentifier, BoogieIcfgLocation> mLabel2LocNodes;

		/**
		 * Set of all labels that occurred in the procedure. If an element is inserted
		 * twice this is an error.
		 */
		// private Set<String> mLabels;

		/**
		 * Maps the Name of a Label to its Statement.
		 */
		private Map<String, Label> mLabelString2Statement;

		/**
		 * Name of that last Label for which we constructed a LocNode
		 */
		private DebugIdentifier mLastLabelName;

		/**
		 * Distance to the last LocNode that was constructed as representative of a
		 * label.
		 */
		// int mlocSuffix;

		/**
		 * Element at which we continue building the CFG. This should be a - LocNode if
		 * the last processed Statement was a Label or a CallStatement - TransEdge if
		 * the last processed Statement was Assume, Assignment, Havoc or Assert. - null
		 * if the last processed Statement was Goto or Return.
		 */
		IElement mCurrent;

		/**
		 * List of auxiliary edges, which represent Gotos and get removed later.
		 */
		List<GotoEdge> mGotoEdges;

		/**
		 * Name of the procedure for which the CFG is build (at the moment)
		 */
		String mCurrentProcedureName;

		/**
		 * The non goto edges of this procedure.
		 */
		Set<CodeBlock> mEdges;

		/**
		 * Stores the number of constructed DebugIdentifiers/Nodes for each line per
		 * procedure, to construct unique DebugIdentifiers.
		 */
		Map<Integer, Integer> mNameCache;

		/**
		 * Builds the control flow graph of a single procedure according to a given
		 * implementation.
		 *
		 * @param Identifier of the procedure for which the CFG will be build.
		 */
		private void buildProcedureCfgFromImplementation(final String procName) {
			mCurrentProcedureName = procName;
			mEdges = new HashSet<>();
			mGotoEdges = new LinkedList<>();
			mNameCache = new HashMap<>();
			mWhileExits = new Stack<>();
			mConditionalStarts = new Stack<>();
			mLabelString2Statement = new HashMap<>();

			final Statement[] statements = mBoogieDeclarations.getProcImplementation().get(procName).getBody()
					.getBlock();
			if (statements.length == 0) {
				mEdges = new HashSet<>();
			}

			mLabel2LocNodes = new HashMap<>();

			// find all Labels in procedure
			findLabels(statements);

			// initialize the Map from labels to LocNodes for this procedure
			mProcLocNodes = new HashMap<>();
			mIcfg.getProgramPoints().put(procName, mProcLocNodes);

			mLogger.debug("Start construction of the CFG for" + procName);
			{
				// first LocNode is the entry node of the procedure
				final BoogieIcfgLocation locNode = mIcfg.getProcedureEntryNodes().get(procName);
				mLastLabelName = locNode.getDebugIdentifier();
				// mlocSuffix = 0;
				mProcLocNodes.put(mLastLabelName, locNode);
				mCurrent = locNode;
			}

			// build cfg
			BoogieIcfgLocation graph = buildCodeBlock(statements, mIcfg.mFinalNode.get(procName));

			graph = assumeRequires(graph, false);
			// if procedure has 0 statements
			if (graph == mIcfg.mFinalNode.get(procName)) {
				mIcfg.getProcedureEntryNodes().put(procName, graph);
				mergeLocNodes(mIcfg.getProcedureEntryNodes().get(procName), graph, true);
			} else {
				mergeLocNodes(graph, mIcfg.getProcedureEntryNodes().get(procName), true);
			}

			assertAndAssumeEnsures();

			// Remove auxiliary GotoTransitions
			final boolean removeGotoEdges = mServices.getPreferenceProvider(Activator.PLUGIN_ID)
					.getBoolean(IcfgPreferenceInitializer.LABEL_REMOVE_GOTO_EDGES);
			if (removeGotoEdges) {
				mLogger.debug("Starting removal of auxiliaryGotoTransitions");
				while (!mGotoEdges.isEmpty()) {
					final GotoEdge gotoEdge = mGotoEdges.remove(0);
					final boolean wasRemoved = removeAuxiliaryGoto(gotoEdge, true);
					assert wasRemoved : "goto not removed";
				}
			} else {
				for (final GotoEdge gotoEdge : mGotoEdges) {
					final boolean wasRemoved = removeAuxiliaryGoto(gotoEdge, false);
					if (!wasRemoved) {
						mEdges.add(gotoEdge);
					}
				}
			}

			for (final CodeBlock transEdge : mEdges) {
				mTransFormulaAdder.addTransitionFormulas(transEdge, procName, SIMPLIFICATION_TECHNIQUE);
			}

			// Remove unreachable nodes and unreachable edges

			final BoogieIcfgLocation initial = mIcfg.getProcedureEntryNodes().get(procName);
			final Set<BoogieIcfgLocation> reachablePPs = computeReachableLocations(initial);
			final BoogieIcfgLocation exit = mIcfg.getProcedureExitNodes().get(procName);
			final Map<DebugIdentifier, BoogieIcfgLocation> constructedPPs = mProcLocNodes;
			removeUnreachableProgramPoints(reachablePPs, constructedPPs, exit);

		}

		private Boolean isAssuAssiHavoc(final Statement st) {
			return st instanceof AssumeStatement || st instanceof AssignmentStatement || st instanceof HavocStatement;
		}

		private void findLabels(final Statement[] codeblock) {
			for (final Statement statement : codeblock) {
				if (statement instanceof Label) {
					mLabelString2Statement.put(((Label) statement).getName(), (Label) statement);
				} else if (statement instanceof WhileStatement) {
					findLabels(((WhileStatement) statement).getBody());
				} else if (statement instanceof IfStatement) {
					findLabels(((IfStatement) statement).getThenPart());
					findLabels(((IfStatement) statement).getElsePart());
				} else if (statement instanceof AtomicStatement) {
					findLabels(((AtomicStatement) statement).getBody());
				}
			}
		}

		private BoogieIcfgLocation buildCodeBlock(final Statement[] codeblock, final BoogieIcfgLocation endLoc) {
			return (BoogieIcfgLocation) buildCodeBlock(codeblock, endLoc, true);
		}

		private IIcfgElement buildCodeBlock(final Statement[] codeblock, final IIcfgElement endLoc,
				final boolean endStatementSequence) {
			IIcfgElement currentLocation = endLoc;
			for (int i = codeblock.length - 1; i >= 0; i--) {
				final Statement st = codeblock[i];
				if (currentLocation instanceof StatementSequence
						&& !(st instanceof CallStatement || isAssuAssiHavoc(st))) {
					currentLocation = endStatementSequence((StatementSequence) currentLocation);
				}
				if (st instanceof WhileStatement) {
					currentLocation = buildWhile((BoogieIcfgLocation) currentLocation, (WhileStatement) st);
				} else if (st instanceof IfStatement) {
					currentLocation = buildIf((BoogieIcfgLocation) currentLocation, (IfStatement) st);
				} else if (st instanceof AssertStatement) {
					currentLocation = buildAssert((BoogieIcfgLocation) currentLocation, (AssertStatement) st);
				} else if (isAssuAssiHavoc(st)) {
					currentLocation = buildAssuAssiHavoc(currentLocation, st, Origin.IMPLEMENTATION);
				} else if (st instanceof ReturnStatement) {
					currentLocation = buildReturn((BoogieIcfgLocation) currentLocation, (ReturnStatement) st);
				} else if (st instanceof BreakStatement) {
					currentLocation = buildBreak((BoogieIcfgLocation) currentLocation, (BreakStatement) st);
				} else if (st instanceof Label) {
					currentLocation = buildLabel((BoogieIcfgLocation) currentLocation, (Label) st);
				} else if (st instanceof GotoStatement) {
					currentLocation = buildGoto((BoogieIcfgLocation) currentLocation, (GotoStatement) st);
				} else if (st instanceof ForkStatement) {
					currentLocation = buildFork((BoogieIcfgLocation) currentLocation, (ForkStatement) st);
				} else if (st instanceof JoinStatement) {
					currentLocation = buildJoin((BoogieIcfgLocation) currentLocation, (JoinStatement) st);
				} else if (st instanceof AtomicStatement) {
					currentLocation = buildAtomic((BoogieIcfgLocation) currentLocation, (AtomicStatement) st);
				} else if (st instanceof CallStatement) {
					currentLocation = buildCall(currentLocation, (CallStatement) st);
				} else {
					throw new UnsupportedOperationException("Statement " + st.getClass() + " not supported");
				}

			}
			// end StatementSequence if required
			if (endStatementSequence && currentLocation instanceof StatementSequence) {
				currentLocation = endStatementSequence((StatementSequence) currentLocation);
			}
			return currentLocation;
		}

		private BoogieIcfgLocation buildIf(BoogieIcfgLocation currentLocation, final IfStatement st) {
			mConditionalStarts.add(currentLocation);
			final IIcfgElement thenPart = buildCodeBlock(st.getThenPart(), currentLocation, false);
			final IIcfgElement elsePart = buildCodeBlock(st.getElsePart(), mConditionalStarts.peek(), false);
			currentLocation = mConditionalStarts.pop();
			AssumeStatement thenStatement;
			AssumeStatement elseStatement;

			// use Assume true statements for WildcardExpression
			if (st.getCondition() instanceof WildcardExpression) {
				thenStatement = new AssumeStatement(st.getLocation(),
						ExpressionFactory.createBooleanLiteral(st.getLocation(), true));
				elseStatement = thenStatement;
			} else {
				thenStatement = new AssumeStatement(st.getLocation(), st.getCondition());
				elseStatement = new AssumeStatement(st.getLocation(), getNegation(st.getCondition()));
				new ConditionAnnotation(false).annotate(thenStatement);
				new ConditionAnnotation(true).annotate(elseStatement);
			}

			// backtranslation
			mIcfgBacktranslator.putAux(thenStatement, new BoogieASTNode[] { st });
			mIcfgBacktranslator.putAux(elseStatement, new BoogieASTNode[] { st });

			final BoogieIcfgLocation srcLoc = buildNewIcfgLocation(st);
			buildBranching(st, thenStatement, thenPart, elseStatement, elsePart, srcLoc);
			return srcLoc;
		}

		private BoogieIcfgLocation buildWhile(final BoogieIcfgLocation currentLocation, final WhileStatement st) {
			final BoogieIcfgLocation start = new BoogieIcfgLocation(constructLocDebugIdentifier(st),
					mCurrentProcedureName, false, st);
			BoogieIcfgLocation afterInvariants;
			// detect and handle invariants
			if (st.getInvariants().length == 0) {
				afterInvariants = start;
			} else {
				final Statement afterInvSt = new AssignmentStatement(st.getLoc(), null, null);
				afterInvariants = new BoogieIcfgLocation(constructLocDebugIdentifier(afterInvSt), mCurrentProcedureName,
						false, afterInvSt);
				mProcLocNodes.put(afterInvariants.getDebugIdentifier(), afterInvariants);
				IIcfgElement currentElement = afterInvariants;
				// build each invariant
				for (Integer i = st.getInvariants().length - 1; i >= 0; i--) {
					final LoopInvariantSpecification spec = st.getInvariants()[i];
					if (spec.isFree()) {
						final AssumeStatement newStatement = new AssumeStatement(spec.getLocation(), spec.getFormula());
						ModelUtils.copyAnnotations(spec, newStatement);
						currentElement = buildAssuAssiHavoc(currentElement, newStatement, Origin.IMPLEMENTATION);
					} else {
						if (currentElement instanceof StatementSequence) {
							currentElement = endStatementSequence((StatementSequence) currentElement);
						}
						final AssertStatement newStatement = new AssertStatement(spec.getLocation(), spec.getFormula());
						ModelUtils.copyAnnotations(spec, newStatement);
						currentElement = buildAssert((BoogieIcfgLocation) currentElement, newStatement);
					}
				}
				if (currentElement instanceof StatementSequence) {
					currentElement = endStatementSequence((StatementSequence) currentElement);
				}
				mergeLocNodes((BoogieIcfgLocation) currentElement, start, false);

			}

			mProcLocNodes.put(start.getDebugIdentifier(), start);
			mIcfg.getLoopLocations().add(start);
			mWhileExits.add(currentLocation);
			mConditionalStarts.add(afterInvariants);
			AssumeStatement condTrue;
			AssumeStatement condFalse;
			if (st.getCondition() instanceof WildcardExpression) {
				condTrue = new AssumeStatement(st.getLocation(),
						ExpressionFactory.createBooleanLiteral(st.getLocation(), true));
				condFalse = condTrue;
			} else {
				condTrue = new AssumeStatement(st.getLocation(), st.getCondition());
				condFalse = new AssumeStatement(st.getLocation(), getNegation(st.getCondition()));
				new ConditionAnnotation(false).annotate(condTrue);
				new ConditionAnnotation(true).annotate(condFalse);
			}
			mIcfgBacktranslator.putAux(condTrue, new BoogieASTNode[] { st });
			mIcfgBacktranslator.putAux(condFalse, new BoogieASTNode[] { st });
			buildBranching(st, condTrue, buildCodeBlock(st.getBody(), start, false), condFalse, currentLocation,
					afterInvariants);
			assert (mWhileExits.pop() == currentLocation);
			if (mConditionalStarts.peek() != start) {
				mergeLocNodes(start, mConditionalStarts.peek(), true);
			}
			return mConditionalStarts.pop();
		}

		private Expression getLHSExpression(final LeftHandSide lhs) {
			Expression expr;
			if (lhs instanceof ArrayLHS) {
				final ArrayLHS arrlhs = (ArrayLHS) lhs;
				final Expression array = getLHSExpression(arrlhs.getArray());
				expr = new ArrayAccessExpression(lhs.getLocation(), lhs.getType(), array, arrlhs.getIndices());
			} else {
				final VariableLHS varlhs = (VariableLHS) lhs;
				expr = new IdentifierExpression(lhs.getLocation(), lhs.getType(), varlhs.getIdentifier(),
						varlhs.getDeclarationInformation());
			}
			return expr;
		}

		private IIcfgElement buildAssuAssiHavoc(IIcfgElement currentLocation, Statement st, final Origin origin) {
			// convert ArrayLHS to ArrayStoreExpression
			if (st instanceof AssignmentStatement) {
				final AssignmentStatement assign = (AssignmentStatement) st;
				final LeftHandSide[] lhs = assign.getLhs();
				final Expression[] rhs = assign.getRhs();
				boolean changed = false;
				for (int i = 0; i < lhs.length; i++) {
					while (lhs[i] instanceof ArrayLHS) {
						final LeftHandSide array = ((ArrayLHS) lhs[i]).getArray();
						final Expression[] indices = ((ArrayLHS) lhs[i]).getIndices();
						final Expression arrayExpr = getLHSExpression(array);
						rhs[i] = new ArrayStoreExpression(lhs[i].getLocation(), array.getType(), arrayExpr, indices,
								rhs[i]);
						lhs[i] = array;
						changed = true;
					}
				}
				if (changed) {
					st = assign;
				}
			}

			switch (mCodeBlockSize) {
			case OneNontrivialStatement:
				if (currentLocation instanceof StatementSequence && !StatementSequence.isAssumeTrueStatement(st)
						&& !((StatementSequence) currentLocation).isTrivial()) {
					currentLocation = endStatementSequence((StatementSequence) currentLocation);
				}
			case LoopFreeBlock:
			case SequenceOfStatements:
				if (currentLocation instanceof StatementSequence) {
					addStatementToStatementSequence(st, (StatementSequence) currentLocation);
					return currentLocation;
				} else {
					return startNewStatementSequenceAndAddStatement((BoogieIcfgLocation) currentLocation, st, origin);
				}
			case SingleStatement:
				if (currentLocation instanceof StatementSequence) {
					if (((StatementSequence) currentLocation).getStatements().isEmpty()) {
						addStatementToStatementSequence(st, (StatementSequence) currentLocation);
						return currentLocation;
					}
					currentLocation = endStatementSequence((StatementSequence) currentLocation);
				}
				final StatementSequence sequence = startNewStatementSequenceAndAddStatement(
						(BoogieIcfgLocation) currentLocation, st, origin);
				return endStatementSequence(sequence);
			default:
				throw new AssertionError("Unknown value: " + mCodeBlockSize);
			}
		}

		private BoogieIcfgLocation buildAssert(final BoogieIcfgLocation currentLocation, final AssertStatement st) {
			final BoogieIcfgLocation error = addErrorNode(mCurrentProcedureName, st, mProcLocNodes);
			mProcLocNodes.put(error.getDebugIdentifier(), error);
			AssumeStatement assumeTrue;
			if (mAddAssumeForEachAssert) {
				assumeTrue = new AssumeStatement(st.getLocation(), st.getFormula());
			} else {
				assumeTrue = new AssumeStatement(st.getLocation(),
						ExpressionFactory.createBooleanLiteral(st.getLocation(), true));
			}

			new ConditionAnnotation(false).annotate(assumeTrue);
			final AssumeStatement assumeFalse = new AssumeStatement(st.getLocation(), getNegation(st.getFormula()));
			new ConditionAnnotation(true).annotate(assumeFalse);
			mIcfgBacktranslator.putAux(assumeTrue, new BoogieASTNode[] { st });
			mIcfgBacktranslator.putAux(assumeFalse, new BoogieASTNode[] { st });
			final BoogieIcfgLocation srcLoc = buildNewIcfgLocation(st);
			buildBranching(st, assumeTrue, currentLocation, assumeFalse, error, srcLoc);
			return srcLoc;
		}

		/**
		 * Prepend an {@link AssumeStatement} to part of our ICFG that we currently
		 * build.
		 *
		 * @param st      {@link Statement} from which the the {@link AssumeStatement}
		 *                originates.
		 * @param cond    Condition represented by an {@link AssumeStatement}.
		 * @param current Part of the ICFG that we currently build. Either a
		 *                {@link StatementSequence} or an {@link IcfgLocation}.
		 * @param srcLoc  The {@link IcfgLocation} the becomes the source location of
		 *                the edge that contains the {@link AssumeStatement}.
		 */
		private void prependOneAssume(final Statement st, final AssumeStatement cond, final IIcfgElement current,
				final BoogieIcfgLocation srcLoc) {
			if (current instanceof StatementSequence && (mCodeBlockSize == CodeBlockSize.SequenceOfStatements
					|| mCodeBlockSize == CodeBlockSize.LoopFreeBlock
					|| mCodeBlockSize == CodeBlockSize.OneNontrivialStatement
							&& (((StatementSequence) current).isTrivial()
									|| StatementSequence.isAssumeTrueStatement(cond)))) {
				((StatementSequence) current).addStatement(cond, 0);
				ModelUtils.copyAnnotations(st, current);
				ModelUtils.copyAnnotations(cond, current);
				endStatementSequence((StatementSequence) current, srcLoc);
			} else {
				StatementSequence newEdge1;
				if (current instanceof StatementSequence) {
					newEdge1 = mCbf.constructStatementSequence(srcLoc,
							endStatementSequence((StatementSequence) current), cond);
				} else {
					newEdge1 = mCbf.constructStatementSequence(srcLoc, (BoogieIcfgLocation) current, cond);
				}
				mEdges.add(newEdge1);
				ModelUtils.copyAnnotations(st, newEdge1);
				ModelUtils.copyAnnotations(cond, newEdge1);
			}
		}

		private BoogieIcfgLocation buildNewIcfgLocation(final Statement st) {
			final BoogieIcfgLocation start = new BoogieIcfgLocation(constructLocDebugIdentifier(st),
					mCurrentProcedureName, false, st);
			mProcLocNodes.put(start.getDebugIdentifier(), start);
			return start;
		}

		/**
		 * Build a branching that connects two parts of the ICFG. We prepend an
		 * {@link AssumeStatement} to each part of the ICFG.
		 *
		 * @param st {@link Statement} from which the the branching originates.
		 * @param srcLoc The {@link IcfgLocation} the becomes the source location of
		 *                the edges that contains the {@link AssumeStatement}s.
		 */
		private void buildBranching(final Statement st, final AssumeStatement cond1,
				final IIcfgElement part1, final AssumeStatement cond2, final IIcfgElement part2,
				final BoogieIcfgLocation srcLoc) {
			prependOneAssume(st, cond1, part1, srcLoc);
			prependOneAssume(st, cond2, part2, srcLoc);
		}

		private BoogieIcfgLocation buildReturn(final BoogieIcfgLocation currentLocation, final ReturnStatement st) {
			return mIcfg.mFinalNode.get(mCurrentProcedureName);
		}

		private BoogieIcfgLocation buildBreak(final BoogieIcfgLocation currentLocation, final BreakStatement st) {
			ModelUtils.copyAnnotations(st, mWhileExits.peek());
			new LoopExitAnnotation(LoopExitType.BREAK).annotate(mWhileExits.peek());
			return mWhileExits.peek();
		}

		private BoogieIcfgLocation buildLabel(final BoogieIcfgLocation currentLocation, final Label st) {
			final BoogieIcfgLocation newLocation = getLocNodeForLabel(new StringDebugIdentifier(st.getName()), st);
			mergeLocNodes(currentLocation, newLocation, true);
			if (currentLocation == mIcfg.mFinalNode.get(mCurrentProcedureName)) {
				mIcfg.mFinalNode.put(mCurrentProcedureName, newLocation);
			}
			if (!mConditionalStarts.empty() && mConditionalStarts.peek() == currentLocation) {
				mConditionalStarts.pop();
				mConditionalStarts.add(newLocation);
			}
			return newLocation;
		}

		private BoogieIcfgLocation buildGoto(final BoogieIcfgLocation currentLocation, final GotoStatement st) {
			final BoogieIcfgLocation newLocation = new BoogieIcfgLocation(constructLocDebugIdentifier(st),
					mCurrentProcedureName, false, st);
			mProcLocNodes.put(newLocation.getDebugIdentifier(), newLocation);
			for (final String label : st.getLabels()) {
				final GotoEdge gotoEdge = mCbf.constructGotoEdge(newLocation,
						getLocNodeForLabel(new StringDebugIdentifier(label), mLabelString2Statement.get(label)));
				ModelUtils.copyAnnotations(st, gotoEdge);
				mGotoEdges.add(gotoEdge);
				mEdges.add(gotoEdge);
			}
			return newLocation;
		}

		private BoogieIcfgLocation buildFork(final BoogieIcfgLocation currentLocation, final ForkStatement st) {
			final BoogieIcfgLocation newLocation = new BoogieIcfgLocation(constructLocDebugIdentifier(st),
					mCurrentProcedureName, false, st);
			mProcLocNodes.put(newLocation.getDebugIdentifier(), newLocation);
			ForkThreadCurrent newEdge;
			if (mBoogieDeclarations.getProcImplementation().containsKey(st.getProcedureName())) {
				newEdge = mCbf.constructForkCurrentThread(newLocation, currentLocation, st, true);
				ModelUtils.copyAnnotations(st, newEdge);
				mForks.put(newEdge, null);
			} else {
				newEdge = mCbf.constructForkCurrentThread(newLocation, currentLocation, st, false);
				ModelUtils.copyAnnotations(st, newEdge);
			}
			mEdges.add(newEdge);
			return newLocation;
		}

		private BoogieIcfgLocation buildJoin(final BoogieIcfgLocation currentLocation, final JoinStatement st) {
			final BoogieIcfgLocation newLocation = new BoogieIcfgLocation(constructLocDebugIdentifier(st),
					mCurrentProcedureName, false, st);
			mProcLocNodes.put(newLocation.getDebugIdentifier(), newLocation);
			final JoinThreadCurrent newEdge = mCbf.constructJoinCurrentThread(newLocation, currentLocation, st);
			ModelUtils.copyAnnotations(st, newEdge);
			mJoins.add(newEdge);
			mEdges.add(newEdge);
			return newLocation;
		}

		/**
		 * Construct auxiliary edge that is labeled by an annotation that indicates that
		 * an atomic block ends here. We return the source location of the auxiliary
		 * edge.
		 * <p>
		 * (An alternative could be to return an unfinished {@link StatementSequence}.
		 * This alternative turned our to be too complicated because some cases
		 * the @link StatementSequence} is empty and {@link CfgBuilder#buildCodeBlock}
		 * has to take care of this special case.)
		 */
		private IIcfgElement beginAtomicBlockFromBottom(final BoogieIcfgLocation currentLocation, final Statement st) {
			final StatementSequence newEdge = startNewStatementSequence(currentLocation, Origin.IMPLEMENTATION);
			AtomicBlockInfo.addEndAnnotation(newEdge);
			return endStatementSequence(newEdge, st);
		}

		private BoogieIcfgLocation endAtomicBlockAtTop(final IIcfgElement curElement, final Statement st) {
			assert (curElement instanceof BoogieIcfgLocation || curElement instanceof StatementSequence);
			final StatementSequence stSeq;
			if (!(curElement instanceof StatementSequence)) {
				stSeq = startNewStatementSequence((BoogieIcfgLocation) curElement, Origin.IMPLEMENTATION);
			} else {
				stSeq = (StatementSequence) curElement;
			}
			if (AtomicBlockInfo.isEndOfAtomicBlock(stSeq)) {
				// if current edge is both start and end of an atomic block, it is already
				// atomic -- nothing else to do
				AtomicBlockInfo.removeAnnotation(stSeq);
				AtomicBlockInfo.addCompleteAnnotation(stSeq);
			} else {
				// mark current edge as start of atomic block
				AtomicBlockInfo.addBeginAnnotation(stSeq);
			}
			return endStatementSequence(stSeq, st);
		}

		private BoogieIcfgLocation buildAtomic(final BoogieIcfgLocation currentLocation, final AtomicStatement st) {
			IIcfgElement curElement = beginAtomicBlockFromBottom(currentLocation, st);
			curElement = buildCodeBlock(st.getBody(), curElement, false);
			return endAtomicBlockAtTop(curElement, st);
		}

		private IIcfgElement buildCall(final IIcfgElement currentLocation, final CallStatement st) {
			final String callee = st.getMethodName();
			if ("__VERIFIER_atomic_begin".equals(callee)) {
				return endAtomicBlockAtTop(currentLocation, st);
			}
			if ("__VERIFIER_atomic_end".equals(callee)) {
				final BoogieIcfgLocation locAfterAtomicBlock;
				if (currentLocation instanceof StatementSequence) {
					locAfterAtomicBlock = endStatementSequence((StatementSequence) currentLocation);
				} else if (currentLocation instanceof BoogieIcfgLocation) {
					locAfterAtomicBlock = (BoogieIcfgLocation) currentLocation;
				} else {
					throw new AssertionError("Expected StatementSequence or BoogieIcfgLocation");
				}
				return beginAtomicBlockFromBottom(locAfterAtomicBlock, st);
			}

			final List<RequiresSpecification> requiresNonFree = mBoogieDeclarations.getRequiresNonFree().get(callee);
			final boolean procedureHasImplementation = mBoogieDeclarations.getProcImplementation().containsKey(callee);
			final boolean nonFreeRequiresIsEmpty = requiresNonFree == null || requiresNonFree.isEmpty();

			if ((mCodeBlockSize == CodeBlockSize.SequenceOfStatements || mCodeBlockSize == CodeBlockSize.LoopFreeBlock)
					&& !procedureHasImplementation && nonFreeRequiresIsEmpty) {
				if (currentLocation instanceof BoogieIcfgLocation) {
					return startNewStatementSequenceAndAddStatement((BoogieIcfgLocation) currentLocation, st,
							Origin.IMPLEMENTATION);
				} else if (currentLocation instanceof StatementSequence) {
					return addStatementToStatementSequence(st, (StatementSequence) currentLocation);
				} else {
					throw new AssertionError("mCurrent must be CodeBlock or BoogieIcfgLocation");
				}
			}

			BoogieIcfgLocation locNode;
			if (currentLocation instanceof StatementSequence) {
				locNode = endStatementSequence((StatementSequence) currentLocation, st);
			} else if (currentLocation instanceof BoogieIcfgLocation) {
				locNode = (BoogieIcfgLocation) currentLocation;
			} else {
				// currentLocation must be either LocNode or StatementSequence
				throw new AssertionError();
			}

			final BoogieIcfgLocation newLocation = new BoogieIcfgLocation(constructLocDebugIdentifier(st),
					mCurrentProcedureName, false, st);
			mProcLocNodes.put(newLocation.getDebugIdentifier(), newLocation);
			ModelUtils.mergeAnnotations(st, newLocation);
			Summary summaryEdge;
			if (mBoogieDeclarations.getProcImplementation().containsKey(st.getMethodName())) {
				summaryEdge = mCbf.constructSummary(newLocation, locNode, st, true);
				ModelUtils.copyAnnotations(st, summaryEdge);
				mImplementationSummarys.add(summaryEdge);
			} else {
				summaryEdge = mCbf.constructSummary(newLocation, locNode, st, false);
				ModelUtils.copyAnnotations(st, summaryEdge);
			}
			mEdges.add(summaryEdge);
			if (requiresNonFree != null && !requiresNonFree.isEmpty()) {
				for (final RequiresSpecification spec : requiresNonFree) {
					Procedure proc;
					if (mBoogieDeclarations.getProcImplementation().containsKey(callee)) {
						proc = mBoogieDeclarations.getProcImplementation().get(callee);
					} else {
						proc = mBoogieDeclarations.getProcSpecification().get(callee);
					}
					final Expression violatedRequires = getNegation(
							new WeakestPrecondition(spec.getFormula(), st, proc).getResult());
					AssumeStatement assumeSt;
					assumeSt = new AssumeStatement(st.getLocation(), violatedRequires);
					final Statement st1 = assumeSt;
					ModelUtils.copyAnnotations(st, st1);
					mIcfgBacktranslator.putAux(assumeSt, new BoogieASTNode[] { st, spec });
					final BoogieIcfgLocation errorLocNode = addErrorNode(mCurrentProcedureName, spec, mProcLocNodes);
					final StatementSequence errorCB = mCbf.constructStatementSequence(newLocation, errorLocNode,
							assumeSt, Origin.REQUIRES);
					ModelUtils.copyAnnotations(spec, errorCB);
					ModelUtils.copyAnnotations(spec, errorLocNode);
					mEdges.add(errorCB);
				}
			}
			return newLocation;
		}

		private BoogieIcfgLocation endStatementSequence(final StatementSequence currentLoc,
				final BoogieIcfgLocation loc) {
			((CodeBlock) currentLoc).connectSource(loc);
			return loc;
		}

		private BoogieIcfgLocation endStatementSequence(final StatementSequence currentLoc, final Statement st) {
			final DebugIdentifier locName = constructLocDebugIdentifier(st);
			final BoogieIcfgLocation locNode = new BoogieIcfgLocation(locName, mCurrentProcedureName, false, st);
			mProcLocNodes.put(locName, locNode);
			return endStatementSequence(currentLoc, locNode);
		}

		private BoogieIcfgLocation endStatementSequence(final StatementSequence currentLoc) {
			return endStatementSequence(currentLoc, currentLoc.getStatements().get(0));
		}

		private StatementSequence startNewStatementSequenceAndAddStatement(final BoogieIcfgLocation currentLocation,
				final Statement st, final Origin origin) {
			assert isIntraproceduralBranchFreeStatement(st) : "cannot add statement to code block " + st;
			final StatementSequence codeBlock = mCbf.constructStatementSequence(null, currentLocation, st, origin);
			ModelUtils.copyAnnotations(st, codeBlock);
			mEdges.add(codeBlock);
			return codeBlock;
		}

		private StatementSequence startNewStatementSequence(final BoogieIcfgLocation currentLocation,
				final Origin origin) {
			final StatementSequence codeBlock = mCbf.constructStatementSequence(null, currentLocation, List.of(),
					origin);
			mEdges.add(codeBlock);
			return codeBlock;
		}

		private StatementSequence addStatementToStatementSequence(final Statement st,
				final StatementSequence currentLoc) {
			assert isIntraproceduralBranchFreeStatement(st) : "cannot add statement to code block " + st;
			currentLoc.addStatement(st, 0);
			ModelUtils.copyAnnotations(st, currentLoc);
			return currentLoc;
		}

		/**
		 * Given constructed and reachable {@link BoogieIcfgLocation}s. Remove the ones
		 * that are not reachable (and the adjacent edges) from the CFG. Only exception
		 * is the exit node of the procedure. (exit node is kept even if unreachable).
		 */
		private void removeUnreachableProgramPoints(final Set<BoogieIcfgLocation> reachablePPs,
				final Map<DebugIdentifier, BoogieIcfgLocation> constructedPPs, final BoogieIcfgLocation exitPP) {
			final Iterator<Entry<DebugIdentifier, BoogieIcfgLocation>> it = constructedPPs.entrySet().iterator();
			while (it.hasNext()) {
				final Entry<DebugIdentifier, BoogieIcfgLocation> entry = it.next();
				if (reachablePPs.contains(entry.getValue())) {
					// do nothing
				} else if (exitPP == entry.getValue()) {
					// do nothing
				} else {
					it.remove();
					final List<IcfgEdge> outgoingEdges = new ArrayList<>(entry.getValue().getOutgoingEdges());
					for (final IcfgEdge outEdge : outgoingEdges) {
						outEdge.disconnectSource();
						outEdge.disconnectTarget();
						mLogger.info("dead code at ProgramPoint " + entry.getValue() + ": " + outEdge);
						mImplementationSummarys.remove(outEdge);
					}
				}
			}
		}

		/**
		 * Compute set of {@link BoogieIcfgLocation}s that a reachable from a given
		 * starting {@link BoogieIcfgLocation}
		 */
		private Set<BoogieIcfgLocation> computeReachableLocations(final BoogieIcfgLocation start) {
			final Set<BoogieIcfgLocation> reachable;
			{
				reachable = new HashSet<>();
				final ArrayDeque<BoogieIcfgLocation> worklist = new ArrayDeque<>();
				worklist.add(start);
				reachable.add(start);
				while (!worklist.isEmpty()) {
					final BoogieIcfgLocation loc = worklist.removeFirst();
					for (final IcfgLocation succLoc : loc.getOutgoingNodes()) {
						if (!reachable.contains(succLoc)) {
							reachable.add((BoogieIcfgLocation) succLoc);
							worklist.add((BoogieIcfgLocation) succLoc);
						}
					}
				}
			}
			return reachable;
		}

		/**
		 * @return List of {@code EnsuresSpecification}s that contains only one
		 *         {@code EnsuresSpecification} which is true.
		 */
		private List<EnsuresSpecification> getDummyEnsuresSpecifications(final ILocation loc) {
			final Expression dummyExpr = ExpressionFactory.createBooleanLiteral(loc, true);
			final EnsuresSpecification dummySpec = new EnsuresSpecification(loc, false, dummyExpr);
			final ArrayList<EnsuresSpecification> dummySpecs = new ArrayList<>(1);
			dummySpecs.add(dummySpec);
			return dummySpecs;
		}

		/**
		 * @return List of {@code RequiresSpecification}s that contains only one
		 *         {@code RequiresSpecification} which is true.
		 */
		private List<RequiresSpecification> getDummyRequiresSpecifications() {
			final Expression dummyExpr = new BooleanLiteral(null, BoogieType.TYPE_BOOL, true);
			final RequiresSpecification dummySpec = new RequiresSpecification(null, false, dummyExpr);
			final ArrayList<RequiresSpecification> dummySpecs = new ArrayList<>(1);
			dummySpecs.add(dummySpec);
			return dummySpecs;
		}

		/**
		 * Remove GotoEdge from a CFG. If allowMultiplicationOfEdges is false, we try to
		 * remove the goto by only merging locations. This is not always possible hence
		 * there is no guarantee that the goto is removed. If allowMultiplicationOfEdges
		 * is true, we guarantee that the goto is removed but in some cases will not
		 * only merge locations but also multiply existing edges.
		 *
		 * @return true iff we removed the gotoEdge.
		 */
		private boolean removeAuxiliaryGoto(final GotoEdge gotoEdge, final boolean allowMultiplicationOfEdges) {
			final BoogieIcfgLocation mother = (BoogieIcfgLocation) gotoEdge.getSource();
			final BoogieIcfgLocation child = (BoogieIcfgLocation) gotoEdge.getTarget();

			// Target of a goto should never be an error location.
			// If this assertion will fail some day. A fix might be that
			// mother has to become an error location.
			assert !child.isErrorLocation();

			for (final IcfgEdge grandchild : child.getOutgoingEdges()) {
				if (grandchild instanceof Call) {
					mLogger.warn("Will not remove gotoEdge" + gotoEdge + "since this would involve adding/removing call"
							+ "and return edges and bring my naive goto"
							+ " replacing algorithm into terrible trouble");
					return false;
				}
			}

			mLogger.debug("Removed GotoEdge from" + mother + " to " + child);
			if (mother == child) {
				mother.removeOutgoing(gotoEdge);
				gotoEdge.setSource(null);
				gotoEdge.setTarget(null);
				child.removeIncoming(gotoEdge);
				final ILocation loc = mother.getBoogieASTNode().getLocation();
				final StatementSequence gotoSelfloopSubstitute = mCbf.constructStatementSequence(mother, child,
						new AssumeStatement(loc, ExpressionFactory.createBooleanLiteral(loc, true)));
				gotoSelfloopSubstitute.setTransitionFormula(
						TransFormulaBuilder.getTrivialTransFormula(mBoogie2Smt.getManagedScript()));
				mLogger.debug("GotoEdge was selfloop");
				return true;
			}
			assert !child.getIncomingEdges().isEmpty() : "there should be at least the goto that might be removed";
			assert !mother.getOutgoingEdges().isEmpty() : "there should be at least the goto that might be removed";
			if (child.getIncomingEdges().size() == 1 || mother.getOutgoingEdges().size() == 1) {
				mother.removeOutgoing(gotoEdge);
				gotoEdge.setSource(null);
				gotoEdge.setTarget(null);
				child.removeIncoming(gotoEdge);

				// transfer goto-loop annotations to the outgoing edges of child
				for (final IcfgEdge out : child.getOutgoingEdges()) {
					ModelUtils.copyAnnotations(gotoEdge, out, LoopEntryAnnotation.class);
					// TODO: Where to put the LoopExitAnnotation
					ModelUtils.copyAnnotations(gotoEdge, out, LoopExitAnnotation.class);
				}

				final boolean childIsLoopEntry = (LoopEntryAnnotation.getAnnotation(mother) != null);
				if (childIsLoopEntry) {
					mergeLocNodes(mother, child, false);
					mLogger.debug(mother + " gets absorbed by " + child);
				} else {
					mergeLocNodes(child, mother, true);
					mLogger.debug(child + " gets absorbed by " + mother);
				}
				return true;
			}
			if (allowMultiplicationOfEdges) {
				mother.removeOutgoing(gotoEdge);
				gotoEdge.setSource(null);
				gotoEdge.setTarget(null);
				child.removeIncoming(gotoEdge);
				// Not allowed to merge mother and child in this case
				mLogger.debug(child + " has " + child.getIncomingEdges().size() + " predecessors," + " namely "
						+ child.getIncomingNodes());
				mLogger.debug(mother + " has " + mother.getIncomingEdges().size() + " successors" + ", namely "
						+ mother.getOutgoingNodes());
				mLogger.debug("Adding for every successor transition of " + child
						+ " a copy of that transition as successor of " + mother);
				for (final IcfgEdge grandchild : child.getOutgoingEdges()) {
					final BoogieIcfgLocation target = (BoogieIcfgLocation) grandchild.getTarget();
					final CodeBlock edge = mCbf.copyCodeBlock((CodeBlock) grandchild, mother, target);
					// transfer goto-loop annotations to the duplicated edges
					ModelUtils.copyAnnotations(gotoEdge, edge, LoopEntryAnnotation.class);
					ModelUtils.copyAnnotations(gotoEdge, edge, LoopExitAnnotation.class);
					if (edge instanceof GotoEdge) {
						mGotoEdges.add((GotoEdge) edge);
					} else {
						mEdges.add(edge);
					}
				}
				return true;
			}
			return false;
		}

		/**
		 * Assert the ensures clause. For each ensures clause expr
		 * <ul>
		 * <li>append {@code assume (expr)} between the finalNode and the exitNode of
		 * the procedure</li> add an edge labeled with {@code assume (not expr)} from
		 * the final Node to the errorNode
		 */
		private void assertAndAssumeEnsures() {
			// Assume the ensures specification at the end of the procedure.
			List<EnsuresSpecification> ensures = mBoogieDeclarations.getEnsures().get(mCurrentProcedureName);
			if (ensures == null || ensures.isEmpty()) {
				final Procedure proc = mBoogieDeclarations.getProcSpecification().get(mCurrentProcedureName);
				ensures = getDummyEnsuresSpecifications(proc.getLocation());
			}
			final BoogieIcfgLocation exitNode = mIcfg.getProcedureExitNodes().get(mCurrentProcedureName);
			mLastLabelName = exitNode.getDebugIdentifier();
			mProcLocNodes.put(mLastLabelName, exitNode);
			// mlocSuffix = 0;
			mCurrent = exitNode;

			for (final EnsuresSpecification spec : ensures) {
				final AssumeStatement st = new AssumeStatement(spec.getLocation(), spec.getFormula());
				ModelUtils.copyAnnotations(spec, st);
				mIcfgBacktranslator.putAux(st, new BoogieASTNode[] { spec });
				mCurrent = buildAssuAssiHavoc((IIcfgElement) mCurrent, st, Origin.ENSURES);
			}
			final BoogieIcfgLocation finalNode = mIcfg.mFinalNode.get(mCurrentProcedureName);
			mLastLabelName = finalNode.getDebugIdentifier();
			mProcLocNodes.put(mLastLabelName, finalNode);
			if (mCurrent instanceof BoogieIcfgLocation) {
				mergeLocNodes((BoogieIcfgLocation) mCurrent, finalNode, false);
			} else {
				((CodeBlock) mCurrent).connectSource(finalNode);
			}

			// Violations against the ensures part of the procedure
			// specification
			final List<EnsuresSpecification> ensuresNonFree = mBoogieDeclarations.getEnsuresNonFree()
					.get(mCurrentProcedureName);
			if (ensuresNonFree != null && !ensuresNonFree.isEmpty()) {
				for (final EnsuresSpecification spec : ensuresNonFree) {
					final Expression specExpr = spec.getFormula();
					AssumeStatement assumeSt;
					assumeSt = new AssumeStatement(spec.getLocation(), getNegation(specExpr));
					final Statement st = assumeSt;
					ModelUtils.copyAnnotations(spec, st);
					mIcfgBacktranslator.putAux(assumeSt, new BoogieASTNode[] { spec });
					final BoogieIcfgLocation errorLocNode = addErrorNode(mCurrentProcedureName, spec, mProcLocNodes);
					final CodeBlock assumeEdge = mCbf.constructStatementSequence(finalNode, errorLocNode, assumeSt,
							Origin.ENSURES);
					ModelUtils.copyAnnotations(spec, assumeEdge);
					ModelUtils.copyAnnotations(spec, errorLocNode);
					mEdges.add(assumeEdge);
				}
			}
		}

		/**
		 * Assume the requires clause. If the requires clause is empty and
		 * dummyRequiresIfEmpty is true add an dummy requires specification.
		 */
		private BoogieIcfgLocation assumeRequires(final BoogieIcfgLocation startNode,
				final boolean dummyRequiresIfEmpty) {
			// Assume everything mentioned in the requires specification
			List<RequiresSpecification> requires = mBoogieDeclarations.getRequires().get(mCurrentProcedureName);
			if ((requires == null || requires.isEmpty()) && dummyRequiresIfEmpty) {
				requires = getDummyRequiresSpecifications();
			}
			IIcfgElement currentElement = startNode;
			if (requires != null && !requires.isEmpty()) {
				for (int i = requires.size() - 1; i >= 0; i--) {
					final RequiresSpecification spec = requires.get(i);
					final AssumeStatement st = new AssumeStatement(spec.getLocation(), spec.getFormula());
					ModelUtils.copyAnnotations(spec, st);
					mIcfgBacktranslator.putAux(st, new BoogieASTNode[] { spec });
					currentElement = buildAssuAssiHavoc(currentElement, st, Origin.REQUIRES);
				}
			}
			if (currentElement instanceof StatementSequence) {
				return endStatementSequence((StatementSequence) currentElement);
			}
			return (BoogieIcfgLocation) currentElement;

		}

		private DebugIdentifier constructLocDebugIdentifier(final Statement stmt) {
			final ILocation location = stmt.getLocation();
			final int startLine = location.getStartLine();
			Integer value = mNameCache.get(startLine);
			if (value == null) {
				value = 0;
			} else {
				value = value + 1;
			}
			mNameCache.put(startLine, value);
			final LoopEntryAnnotation lea = LoopEntryAnnotation.getAnnotation(stmt);
			if (lea != null && lea.getLoopEntryType() == LoopEntryType.WHILE) {
				return new LoopEntryDebugIdentifier(startLine, value);
			}
			return new OrdinaryDebugIdentifier(startLine, value);
		}

		/**
		 * Get the LocNode that represents a label. If there is already a LocNode that
		 * represents this Label return this representative. Otherwise construct a new
		 * LocNode that becomes the representative for this label.
		 *
		 * @param labelId {@link DebugIdentifier} of the Label for which you want the
		 *                corresponding LocNode.
		 * @param st      Statement whose (Ultimate) Location should be added to this
		 *                LocNode. If this method is called while processing a
		 *                GotoStatement the Statement can be set to null, since the
		 *                Location will be overwritten, when this method is called with
		 *                the correct Label as second parameter.
		 * @return LocNode that is the representative for labelName.
		 */
		private BoogieIcfgLocation getLocNodeForLabel(final DebugIdentifier labelId, final Statement st) {
			final ILocation loc = st.getLocation();
			// final LoopEntryAnnotation lea = LoopEntryAnnotation.getAnnotation(st);
			BoogieIcfgLocation locNode = mLabel2LocNodes.get(labelId);
			if (locNode != null) {
				// The locNode to which labelId points may have been replaced
				// by another locNode. Lets follow this map transitively.
				while (locNode != mLabel2LocNodes.get(locNode.getDebugIdentifier())) {
					locNode = mLabel2LocNodes.get(locNode.getDebugIdentifier());
				}
				if (mLogger.isDebugEnabled()) {
					mLogger.debug("LocNode for " + labelId + " already" + " constructed, namely: " + locNode);
				}
				if (st instanceof Label && locNode.getDebugIdentifier() == labelId) {
					loc.annotate(locNode);
				}
				ModelUtils.copyAnnotations(st, locNode);
				return locNode;
			}
			locNode = new BoogieIcfgLocation(labelId, mCurrentProcedureName, false, st);
			mLabel2LocNodes.put(labelId, locNode);
			mProcLocNodes.put(labelId, locNode);
			if (mLogger.isDebugEnabled()) {
				mLogger.debug("LocNode for " + labelId + " has not" + " existed yet. Constructed it");
			}
			return locNode;
		}

		private boolean isIntraproceduralBranchFreeStatement(final Statement st) {
			if (st instanceof AssumeStatement) {
				return true;
			}
			if (st instanceof AssignmentStatement) {
				return true;
			}
			if (st instanceof HavocStatement) {
				return true;
			}
			if (!(st instanceof CallStatement)) {
				return false;
			}
			final CallStatement call = (CallStatement) st;
			if (mBoogieDeclarations.getProcImplementation().containsKey(call.getMethodName())) {
				// procedure has implementation
				return false;
			}
			if (mBoogieDeclarations.getRequiresNonFree().get(call.getMethodName()) == null
					|| mBoogieDeclarations.getRequiresNonFree().get(call.getMethodName()).isEmpty()) {
				// procedure does not have non-free requires
				// and hence does not require an additional branch into an error location
				return true;
			}
			return false;
		}

		/**
		 * Merge one LocNode into another. The oldLocNode will be merged into the
		 * newLocNode. The newLocNode gets connected to all incoming/outgoing
		 * transitions of the oldLocNode. The oldLocNode looses connections to all
		 * incoming/outgoing transitions. If the oldLocNode was representative for a
		 * Label the new location will from now on be the representative of this Label.
		 *
		 * @param oldLocNode         LocNode that gets merged into the newLocNode. Must
		 *                           not represent an error location.
		 * @param newLocNode         LocNode that absorbes the oldLocNode.
		 * @param copyAllAnnotations If `true` then we copy all annotations from the old
		 *                           node to the new node, if `false` we copy all
		 *                           annotations by the {@link ILocation}.
		 */
		private void mergeLocNodes(final BoogieIcfgLocation oldLocNode, final BoogieIcfgLocation newLocNode,
				final boolean copyAllAnnotations) {
			// oldLocNode must not represent an error location
			assert !oldLocNode.isErrorLocation();
			if (oldLocNode == newLocNode) {
				return;
			}

			for (final IcfgEdge transEdge : oldLocNode.getIncomingEdges()) {
				transEdge.setTarget(newLocNode);
				newLocNode.addIncoming(transEdge);
			}
			oldLocNode.clearIncoming();
			for (final IcfgEdge transEdge : oldLocNode.getOutgoingEdges()) {
				transEdge.setSource(newLocNode);
				newLocNode.addOutgoing(transEdge);
			}
			oldLocNode.clearOutgoing();

			mProcLocNodes.remove(oldLocNode.getDebugIdentifier());

			// If the LocNode that should be replaced was constructed for a
			// label it is in mlocNodeOf and the representative for this label
			// should be updated accordingly.
			if (mLabel2LocNodes.containsKey(oldLocNode.getDebugIdentifier())) {
				mLabel2LocNodes.put(oldLocNode.getDebugIdentifier(), newLocNode);
			}

			assert oldLocNode != mIcfg.getProcedureExitNodes().get(mCurrentProcedureName);
			if (oldLocNode == mIcfg.getProcedureEntryNodes().get(mCurrentProcedureName)) {
				mIcfg.getProcedureEntryNodes().put(mCurrentProcedureName, newLocNode);
			}
			if (mIcfg.getLoopLocations().remove(oldLocNode)) {
				// if the old location was a loop location, the new one is also
				mIcfg.getLoopLocations().add(newLocNode);
			}
			if (copyAllAnnotations) {
				ModelUtils.copyAnnotations(oldLocNode, newLocNode);
			} else {
				ModelUtils.copyAnnotationsExcept(oldLocNode, newLocNode, ILocation.class);
			}
		}
	}
}
