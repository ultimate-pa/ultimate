/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2010-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2018 Lars Nitzke (lars.nitzke@mailfence.com)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE RCFGBuilder plug-in.
 *
 * The ULTIMATE RCFGBuilder plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE RCFGBuilder plug-in is distributed in the hope that it will be useful,
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg;

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
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AtomicStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.EnsuresSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ForkStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.GotoStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.JoinStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Label;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.RequiresSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ReturnStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WhileStatement;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.AtomicBlockInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.LoopEntryAnnotation;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.LoopEntryAnnotation.LoopEntryType;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.LoopExitAnnotation;
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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadOther;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgJoinTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgJoinTransitionThreadOther;
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
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.RCFGBacktranslator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.WeakestPrecondition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence.Origin;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.RcfgPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.RcfgPreferenceInitializer.CodeBlockSize;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.TransFormulaAdder;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

/**
 * This class generates a recursive control flow graph (in the style of POPL'10 - Heizmann, Hoenicke, Podelski - Nested
 * Interpolants) from an Boogie AST which contains only unstructured Code (i.e., no while (and others??) statements).
 * The input for this classs has to be unstructured Boogie Code (e.g., no while loops) for example the output of the
 * BoogiePreprocessor.
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
	 * Root Node of this Ultimate model. I use this to store information that should be passed to the next plugin. The
	 * Successors of this node are exactly the entry nodes of procedures.
	 */
	private final BoogieIcfgContainer mIcfg;

	private final Boogie2SMT mBoogie2Smt;
	private final BoogieDeclarations mBoogieDeclarations;
	private TransFormulaAdder mTransFormulaAdder;

	private final Collection<Summary> mImplementationSummarys = new LinkedHashSet<>();

	private final Map<IIcfgForkTransitionThreadCurrent<IcfgLocation>, List<ThreadInstance>> mForks = new HashMap<>();
	private final List<IIcfgJoinTransitionThreadCurrent<IcfgLocation>> mJoins = new ArrayList<>();

	private final RCFGBacktranslator mRcfgBacktranslator;

	private final CodeBlockSize mCodeBlockSize;

	private final IUltimateServiceProvider mServices;

	private final boolean mAddAssumeForEachAssert;

	private final CodeBlockFactory mCbf;

	private int mRemovedAssumeTrueStatements = 0;

	private final SimplificationTechnique mSimplificationTechnique = SimplificationTechnique.SIMPLIFY_DDA;
	private final XnfConversionTechnique mXnfConversionTechnique =
			XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION;

	private final Set<String> mAllGotoTargets;

	private final boolean mRemoveAssumeTrueStmt;

	public CfgBuilder(final Unit unit, final IUltimateServiceProvider services) throws IOException {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		final IPreferenceProvider prefs = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
		mAddAssumeForEachAssert = prefs.getBoolean(RcfgPreferenceInitializer.LABEL_ASSUME_FOR_ASSERT);
		mRemoveAssumeTrueStmt = prefs.getBoolean(RcfgPreferenceInitializer.LABEL_REMOVE_ASSUME_TRUE);

		final String pathAndFilename = ILocation.getAnnotation(unit).getFileName();
		final String filename = new File(pathAndFilename).getName();
		final Script script = constructAndInitializeSolver(services, filename);
		final ManagedScript mgdScript = new ManagedScript(mServices, script);

		mBoogieDeclarations = new BoogieDeclarations(unit, mLogger);
		final boolean bitvectorInsteadInt = prefs.getBoolean(RcfgPreferenceInitializer.LABEL_BITVECTOR_WORKAROUND);
		final boolean simplePartialSkolemization =
				prefs.getBoolean(RcfgPreferenceInitializer.LABEL_SIMPLE_PARTIAL_SKOLEMIZATION);
		final ForkAndGotoInformation fgInfo = new ForkAndGotoInformation(mBoogieDeclarations);
		mAllGotoTargets = fgInfo.getAllGotoTargets();

		final CodeBlockSize userDefineCodeBlockSize =
				prefs.getEnum(RcfgPreferenceInitializer.LABEL_CODE_BLOCK_SIZE, CodeBlockSize.class);
		if (userDefineCodeBlockSize != CodeBlockSize.SingleStatement && fgInfo.hasSomeForkEdge()) {
			mCodeBlockSize = CodeBlockSize.SingleStatement;
			mLogger.warn("User set CodeBlockSize to " + userDefineCodeBlockSize
					+ " but program contains fork statements. Overwriting the user preferences and setting CodeBlockSize to "
					+ mCodeBlockSize);
		} else {
			mCodeBlockSize = userDefineCodeBlockSize;
		}

		mBoogie2Smt = new Boogie2SMT(mgdScript, mBoogieDeclarations, bitvectorInsteadInt, mServices,
				simplePartialSkolemization);
		final RCFGBacktranslator backtranslator = new RCFGBacktranslator(mLogger);
		backtranslator.setTerm2Expression(mBoogie2Smt.getTerm2Expression());
		mRcfgBacktranslator = backtranslator;

		final ConcurrencyInformation ci = new ConcurrencyInformation(mForks, Collections.emptyMap(), mJoins);
		mIcfg = new BoogieIcfgContainer(mServices, mBoogieDeclarations, mBoogie2Smt, ci);
		mCbf = mIcfg.getCodeBlockFactory();
		mCbf.storeFactory(mServices.getStorage());
	}

	/**
	 * Build a recursive control flow graph for an unstructured boogie program.
	 *
	 * @param Unit
	 *            that encodes a program.
	 * @return RootNode of a recursive control flow graph.
	 */
	public IIcfg<BoogieIcfgLocation> createIcfg(final Unit unit) {

		mTransFormulaAdder = new TransFormulaAdder(mBoogie2Smt, mServices);

		// Build entry, final and exit node for all procedures that have an
		// implementation
		final BoogieIcfgContainer icfg = mIcfg;
		for (final String procName : mBoogieDeclarations.getProcImplementation().keySet()) {
			final Body body = mBoogieDeclarations.getProcImplementation().get(procName).getBody();
			final Statement firstStatement = body.getBlock()[0];
			final BoogieIcfgLocation entryNode = new BoogieIcfgLocation(new ProcedureEntryDebugIdentifier(procName),
					procName, false, firstStatement);
			// We have to use some ASTNode for final and exit node. Let's take
			// the procedure implementation.
			final Procedure impl = mBoogieDeclarations.getProcImplementation().get(procName);
			icfg.getProcedureEntryNodes().put(procName, entryNode);
			final BoogieIcfgLocation finalNode =
					new BoogieIcfgLocation(new ProcedureFinalDebugIdentifier(procName), procName, false, impl);
			icfg.mFinalNode.put(procName, finalNode);
			final BoogieIcfgLocation exitNode =
					new BoogieIcfgLocation(new ProcedureExitDebugIdentifier(procName), procName, false, impl);
			icfg.getProcedureExitNodes().put(procName, exitNode);

			// new RootEdge(mGraphroot, mRootAnnot.mentryNode.get(procName));
		}

		// Build a control flow graph for each procedure
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
			addCallTransitionAndReturnTransition(se, mSimplificationTechnique);
		}

		switch (mCodeBlockSize) {
		case LoopFreeBlock:
			new LargeBlockEncoding(InternalLbeMode.ALL);
			break;
		case SequenceOfStatements: // handled in ProcedureCfgBuilder
		case SingleStatement:
			new LargeBlockEncoding(InternalLbeMode.ONLY_ATOMIC_BLOCK);
			break;
		default:
			throw new AssertionError("unknown value: " + mCodeBlockSize);
		}

		final Set<BoogieIcfgLocation> initialNodes = icfg.getProcedureEntryNodes().entrySet().stream()
				.filter(a -> a.getKey().equals(ULTIMATE_START)).map(a -> a.getValue()).collect(Collectors.toSet());
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

		if (!isAtomicCompositionComplete()) {
			throw new UnsupportedOperationException(
					"Large block encoding incomplete: Is there illegal control flow (e.g. loops) within an atomic block?");
		}

		return icfg;
	}

	private Stream<BoogieIcfgLocation> getAllLocations() {
		return mIcfg.getProgramPoints().entrySet().stream().flatMap(e -> e.getValue().values().stream());
	}

	private boolean isAtomicCompositionComplete() {
		return getAllLocations().allMatch(this::isAtomicCompositionComplete);
	}

	private boolean isAtomicCompositionComplete(final BoogieIcfgLocation pp) {
		if (isStartOfAtomicBlock(pp)) {
			return pp.getOutgoingNodes().stream().allMatch(successor -> {
				if (isEndOfAtomicBlock(successor) || ((BoogieIcfgLocation) successor).isErrorLocation()) {
					return true;
				}

				// We tolerate nodes without successors, such as thread exit locations.
				final boolean successorIsSink = successor.getOutgoingEdges().isEmpty();
				if (successorIsSink) {
					mLogger.warn(
							"Unexpected successor node of atomic block begin: %s is neither atomic block end nor error location.",
							successor);
				} else {
					mLogger.error(
							"Unexpected successor node of atomic block begin: %s is neither atomic block end nor a sink node.",
							successor);
				}
				return successorIsSink;
			});
		} else {
			return true;
		}

		// Dominik 2020-09-18:
		// There is no corresponding check for end-points of atomic blocks.
		// The reason is that such points may be reached in other ways than through the atomic block.
		// For instance, consider a loop whose body is an atomic block.
		// The end point of the body is also the loop head, and thus has a predecessor outside the atomic block.
		// A second (but less important) effect is that orphaned __VERIFIER_atomic_end() statements do not cause an error.
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

		final SolverMode solverMode = prefs.getEnum(RcfgPreferenceInitializer.LABEL_SOLVER, SolverMode.class);

		final boolean fakeNonIncrementalScript =
				prefs.getBoolean(RcfgPreferenceInitializer.LABEL_FAKE_NON_INCREMENTAL_SCRIPT);

		final boolean dumpSmtScriptToFile = prefs.getBoolean(RcfgPreferenceInitializer.LABEL_DUMP_TO_FILE);
		final boolean compressSmtScript = prefs.getBoolean(RcfgPreferenceInitializer.LABEL_COMPRESS_SMT_DUMP_FILE);
		final String pathOfDumpedScript = prefs.getString(RcfgPreferenceInitializer.LABEL_DUMP_PATH);

		final String commandExternalSolver = prefs.getString(RcfgPreferenceInitializer.LABEL_EXT_SOLVER_COMMAND);

		final boolean dumpUnsatCoreTrackBenchmark =
				prefs.getBoolean(RcfgPreferenceInitializer.LABEL_DUMP_UNSAT_CORE_BENCHMARK);

		final boolean dumpMainTrackBenchmark =
				prefs.getBoolean(RcfgPreferenceInitializer.LABEL_DUMP_MAIN_TRACK_BENCHMARK);

		final Map<String, String> additionalSmtOptions =
				prefs.getKeyValueMap(RcfgPreferenceInitializer.LABEL_ADDITIONAL_SMT_OPTIONS);

		final Logics logicForExternalSolver =
				Logics.valueOf(prefs.getString(RcfgPreferenceInitializer.LABEL_EXT_SOLVER_LOGIC));
		final SolverSettings solverSettings =
				SolverBuilder.constructSolverSettings().setUseFakeIncrementalScript(fakeNonIncrementalScript)
						.setDumpSmtScriptToFile(dumpSmtScriptToFile, pathOfDumpedScript, filename, compressSmtScript)
						.setDumpUnsatCoreTrackBenchmark(dumpUnsatCoreTrackBenchmark)
						.setDumpMainTrackBenchmark(dumpMainTrackBenchmark)
						.setUseExternalSolver(true, commandExternalSolver, logicForExternalSolver)
						.setSolverMode(solverMode).setAdditionalOptions(additionalSmtOptions);

		return SolverBuilder.buildAndInitializeSolver(services, solverSettings, "CfgBuilderScript");
	}

	private static Expression getNegation(final Expression expr) {
		if (expr == null) {
			return null;
		}
		return new UnaryExpression(expr.getLocation(), BoogieType.TYPE_BOOL, UnaryExpression.Operator.LOGICNEG, expr);
	}

	/**
	 * Add CallEdge from SummaryEdge source to the entry location of the called procedure. Add ReturnEdge from the
	 * called procedures exit node to the summary edges target.
	 *
	 * @param simplificationTechnique
	 *
	 * @param SummaryEdge
	 *            that summarizes execution of an implemented procedure.
	 */
	private void addCallTransitionAndReturnTransition(final Summary edge,
			final SimplificationTechnique simplificationTechnique) {
		final CallStatement st = edge.getCallStatement();
		final String callee = st.getMethodName();
		assert mIcfg.getProcedureEntryNodes().containsKey(callee) : "Source code contains" + " call of " + callee
				+ " but no such procedure.";

		// Add call transition from callerNode to procedures entry node
		final BoogieIcfgLocation callerNode = (BoogieIcfgLocation) edge.getSource();
		final BoogieIcfgLocation calleeEntryLoc = mIcfg.getProcedureEntryNodes().get(callee);

		final String caller = callerNode.getProcedure();

		final TranslationResult arguments2InParams =
				mIcfg.getBoogie2SMT().getStatements2TransFormula().inParamAssignment(st, simplificationTechnique);
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
	 * construct error location BoogieASTNode in procedure procName add constructed location to mprocLocNodes and
	 * mErrorNodes.
	 *
	 * @return
	 */
	private BoogieIcfgLocation addErrorNode(final String procName, final BoogieASTNode boogieASTNode,
			final Map<DebugIdentifier, BoogieIcfgLocation> procLocNodes) {
		Set<BoogieIcfgLocation> errorNodes = mIcfg.getProcedureErrorNodes().get(procName);
		final int locNodeNumber;
		if (errorNodes == null) {
			errorNodes = new HashSet<>();
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
		} else if (boogieASTNode instanceof CallStatement) {
			type = ProcedureErrorType.REQUIRES_VIOLATION;
		} else if (boogieASTNode instanceof ForkStatement) {
			type = ProcedureErrorType.INUSE_VIOLATION;
		} else {
			throw new IllegalArgumentException();
		}

		final ProcedureErrorDebugIdentifier errorLocLabel;
		final Check check = Check.getAnnotation(boogieASTNode);
		if (check != null) {
			errorLocLabel = new ProcedureErrorWithCheckDebugIdentifier(procName, locNodeNumber, type, check);
		} else {
			errorLocLabel = new ProcedureErrorDebugIdentifier(procName, locNodeNumber, type);
		}
		final BoogieIcfgLocation errorLocNode = new BoogieIcfgLocation(errorLocLabel, procName, true, boogieASTNode);
		if (check != null) {
			check.annotate(errorLocNode);
		}
		procLocNodes.put(errorLocLabel, errorLocNode);
		errorNodes.add(errorLocNode);
		return errorLocNode;
	}

	public ITranslator<IIcfgTransition<IcfgLocation>, BoogieASTNode, Term, Expression, IcfgLocation, String>
			getBacktranslator() {
		return mRcfgBacktranslator;
	}

	private boolean isAssumeTrueStatement(final Statement st) {
		if (mRemoveAssumeTrueStmt && st instanceof AssumeStatement) {
			final AssumeStatement as = (AssumeStatement) st;
			if (as.getFormula() instanceof BooleanLiteral) {
				final BooleanLiteral bl = (BooleanLiteral) as.getFormula();
				if (bl.getValue()) {
					return true;
				}
			}
		}
		return false;
	}

	private static boolean isOverapproximation(final Statement st) {
		final Overapprox oa = Overapprox.getAnnotation(st);
		return oa != null;
	}

	private static boolean isStartOfAtomicBlock(final IcfgLocation node) {
		return AtomicBlockInfo.isStartOfAtomicBlock(node);
	}

	private static boolean isEndOfAtomicBlock(final IcfgLocation node) {
		return AtomicBlockInfo.isEndOfAtomicBlock(node);
	}

	/**
	 * Provides two informations that can be obtained by traversing all statements.
	 * <ul>
	 * <li>information whether some {@link ForkStatement} occurs.
	 * <li>the identifiers of all {@link Label}s that are target of some {@link GotoStatement}
	 * </ul>
	 * Expects that the input has been "unstructured", i.e., all {@link WhileStatement}s and {@link IfStatement}s have
	 * been removed.
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
						|| st instanceof CallStatement || st instanceof ReturnStatement
						|| st instanceof AssertStatement) {
					// do nothing
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
		 * Maps a position identifier to the LocNode that represents this position in the CFG.
		 */
		private Map<DebugIdentifier, BoogieIcfgLocation> mProcLocNodes;

		/**
		 * Maps a Label identifier to the LocNode that represents this Label in the CFG.
		 */
		private Map<DebugIdentifier, BoogieIcfgLocation> mLabel2LocNodes;

		/**
		 * Set of all labels that occurred in the procedure. If an element is inserted twice this is an error.
		 */
		private Set<String> mLabels;

		/**
		 * Name of that last Label for which we constructed a LocNode
		 */
		private DebugIdentifier mLastLabelName;

		/**
		 * Distance to the last LocNode that was constructed as representative of a label.
		 */
		// int mlocSuffix;

		/**
		 * Element at which we continue building the CFG. This should be a - LocNode if the last processed Statement was
		 * a Label or a CallStatement - TransEdge if the last processed Statement was Assume, Assignment, Havoc or
		 * Assert. - null if the last processed Statement was Goto or Return.
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
		 * TODO: document this variable (Daniel Dietsch?)
		 */
		Map<Integer, Integer> mNameCache;

		/**
		 * Builds the control flow graph of a single procedure according to a given implementation.
		 *
		 * @param Identifier
		 *            of the procedure for which the CFG will be build.
		 */
		private void buildProcedureCfgFromImplementation(final String procName) {
			mCurrentProcedureName = procName;
			mEdges = new HashSet<>();
			mGotoEdges = new LinkedList<>();
			mLabels = new HashSet<>();
			mNameCache = new HashMap<>();

			final Statement[] statements =
					mBoogieDeclarations.getProcImplementation().get(procName).getBody().getBlock();
			if (statements.length == 0) {
				throw new UnsupportedOperationException("Procedure contains no statement");
			}

			mLabel2LocNodes = new HashMap<>();

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
			assumeRequires(false);

			boolean precedingStatementWasControlFlowDead = false;
			Statement precedingStatement = null;

			for (final Statement st : statements) {

				if (!mServices.getProgressMonitorService().continueProcessing()) {
					mLogger.warn("Timeout while constructing control flow graph");
					throw new ToolchainCanceledException(this.getClass(),
							"constructing CFG for procedure with " + statements.length + "statements");
				}

				if (isAssumeTrueStatement(st) && !isOverapproximation(st)) {
					mRemovedAssumeTrueStatements++;
					continue;
				}

				assert st.getLocation() != null : "location of the following statement is null " + st;

				final boolean currentStatementIsControlFlowDead = statementIsControlFlowDead(
						precedingStatementWasControlFlowDead, precedingStatement, st, mAllGotoTargets);
				if (!currentStatementIsControlFlowDead || st instanceof AtomicStatement) {
					processStatement(procName, st, precedingStatement);
				}
				precedingStatementWasControlFlowDead = currentStatementIsControlFlowDead;
				precedingStatement = st;
			}

			// If there is no ReturnStatement at the end of the procedure act
			// like there would have been one.
			if (!(precedingStatement instanceof ReturnStatement) && !(precedingStatement instanceof GotoStatement)
					&& !precedingStatementWasControlFlowDead) {
				processReturnStatement();
			}

			assertAndAssumeEnsures();

			// Remove auxiliary GotoTransitions
			final boolean removeGotoEdges = mServices.getPreferenceProvider(Activator.PLUGIN_ID)
					.getBoolean(RcfgPreferenceInitializer.LABEL_REMOVE_GOTO_EDGES);
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
				mTransFormulaAdder.addTransitionFormulas(transEdge, procName, mXnfConversionTechnique,
						mSimplificationTechnique);
			}

			// Remove unreachable nodes and unreachable edges

			final BoogieIcfgLocation initial = mIcfg.getProcedureEntryNodes().get(procName);
			final Set<BoogieIcfgLocation> reachablePPs = computeReachableLocations(initial);
			final BoogieIcfgLocation exit = mIcfg.getProcedureExitNodes().get(procName);
			final Map<DebugIdentifier, BoogieIcfgLocation> constructedPPs = mProcLocNodes;
			removeUnreachableProgramPoints(reachablePPs, constructedPPs, exit);

		}

		/**
		 * Given constructed and reachable {@link BoogieIcfgLocation}s. Remove the ones that are not reachable (and the
		 * adjacent edges) from the CFG. Only exception is the exit node of the procedure. (exit node is kept even if
		 * unreachable).
		 */
		private void removeUnreachableProgramPoints(final Set<BoogieIcfgLocation> reachablePPs,
				final Map<DebugIdentifier, BoogieIcfgLocation> constructedPPs, final BoogieIcfgLocation exitPP) {
			final Iterator<Entry<DebugIdentifier, BoogieIcfgLocation>> it = constructedPPs.entrySet().iterator();
			while (it.hasNext()) {
				final Entry<DebugIdentifier, BoogieIcfgLocation> entry = it.next();
				if (reachablePPs.contains(entry.getValue())) {
					// do nothing
				} else {
					if (exitPP == entry.getValue()) {
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
		}

		/**
		 * Compute set of {@link BoogieIcfgLocation}s that a reachable from a given starting {@link BoogieIcfgLocation}
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

		private void processStatement(final String procName, final Statement st, final Statement precedingSt) {
			if (st instanceof Label) {
				if (mCurrent instanceof BoogieIcfgLocation) {
					assert mCurrent == mIcfg.getProcedureEntryNodes().get(procName)
							|| precedingSt instanceof Label : "If st is Label"
									+ " and mcurrent is LocNode lastSt is Label";
					mLogger.debug("Two Labels in a row: " + mCurrent + " and " + ((Label) st).getName() + "."
							+ " I am expecting that at least one was" + " introduced by the user (or vcc). In the"
							+ " CFG only the first label of those two (or" + " more) will be used");
				}
				if (mCurrent instanceof CodeBlock) {
					assert precedingSt instanceof AssumeStatement || precedingSt instanceof AssignmentStatement
							|| precedingSt instanceof HavocStatement || precedingSt instanceof AssertStatement
							|| precedingSt instanceof CallStatement || precedingSt instanceof AtomicStatement
							|| precedingSt == null : "If st is a Label and the last constructed node"
									+ " was a TransEdge, then the last" + " Statement must not be a Label, Return or"
									+ " Goto";
					mLogger.warn("Label in the middle of a codeblock.");
				}

				processLabel((Label) st);
			}

			else if (st instanceof AssumeStatement || st instanceof AssignmentStatement
					|| st instanceof HavocStatement) {
				if (mCurrent instanceof CodeBlock) {
					assert precedingSt instanceof AssumeStatement || precedingSt instanceof AssignmentStatement
							|| precedingSt instanceof HavocStatement || precedingSt instanceof AssertStatement
							|| precedingSt instanceof CallStatement || precedingSt instanceof AtomicStatement : "If the"
									+ " last constructed node is a TransEdge, then"
									+ " the last Statement must not be a Label,"
									+ " Return or Goto. (i.e. this is not the first" + " Statement of the block)";
				}
				processAssuAssiHavoStatement(st, Origin.IMPLEMENTATION);
			}

			else if (st instanceof AssertStatement) {
				if (mCurrent instanceof CodeBlock) {
					assert precedingSt instanceof AssumeStatement || precedingSt instanceof AssignmentStatement
							|| precedingSt instanceof HavocStatement || precedingSt instanceof AssertStatement
							|| precedingSt instanceof CallStatement || precedingSt instanceof AtomicStatement : "If the"
									+ " last constructed node is a TransEdge, then"
									+ " the last Statement must not be a Label,"
									+ " Return or Goto. (i.e. this is not the first" + " Statement of the block)";
				}
				processAssertStatement((AssertStatement) st);
			}

			else if (st instanceof GotoStatement) {
				// assert (! (mLastSt instanceof GotoStatement)) :
				// "Two Gotos in a row";
				if (precedingSt instanceof GotoStatement) {
					mLogger.warn("Two Gotos in a row! There was dead code");
				} else {
					processGotoStatement((GotoStatement) st);
				}
			}

			else if (st instanceof CallStatement) {
				if (mCurrent instanceof CodeBlock) {
					assert precedingSt instanceof AssumeStatement || precedingSt instanceof AssignmentStatement
							|| precedingSt instanceof HavocStatement || precedingSt instanceof AssertStatement
							|| precedingSt instanceof CallStatement
							|| precedingSt instanceof AtomicStatement : "If mcurrent is a TransEdge, then lastSt"
									+ " must not be a Label, Return or Goto." + " (i.e. this is not the first Statement"
									+ " of the block)";
				}
				if (mCurrent instanceof BoogieIcfgLocation) {
					assert precedingSt instanceof Label || precedingSt instanceof CallStatement
							|| precedingSt instanceof ForkStatement || precedingSt instanceof JoinStatement
							|| isEndOfAtomicBlock((IcfgLocation) mCurrent) : "If mcurrent is LocNode, then st is first "
									+ "statement of a block; first statement after a call, fork, or join; or follows an atomic block";
				}
				processCallStatement((CallStatement) st);
			}

			else if (st instanceof ReturnStatement) {
				processReturnStatement();
			} else if (st instanceof ForkStatement) {
				processForkStatement((ForkStatement) st);
			} else if (st instanceof JoinStatement) {
				processJoinStatement((JoinStatement) st);
			} else if (st instanceof AtomicStatement) {
				processAtomicStatement(procName, (AtomicStatement) st, precedingSt);
			} else {
				throw new UnsupportedOperationException("At the moment"
						+ " only Labels, Assert, Assume, Assignment, Havoc" + " and Goto statements are supported");
			}
		}

		private boolean statementIsControlFlowDead(final boolean lastStatementWasControlFlowDead,
				final Statement lastStmt, final Statement st, final Set<String> allGotoTargets) {
			final boolean lastStatementWasGotoOrReturn =
					lastStmt instanceof GotoStatement || lastStmt instanceof ReturnStatement;
			if (lastStatementWasControlFlowDead || lastStatementWasGotoOrReturn) {
				if (st instanceof Label) {
					final Label label = (Label) st;
					return !allGotoTargets.contains(label.getName());
				}
				return true;
			}
			return false;
		}

		/**
		 * @return List of {@code EnsuresSpecification}s that contains only one {@code EnsuresSpecification} which is
		 *         true.
		 */
		private List<EnsuresSpecification> getDummyEnsuresSpecifications(final ILocation loc) {
			final Expression dummyExpr = new BooleanLiteral(loc, BoogieType.TYPE_BOOL, true);
			final EnsuresSpecification dummySpec = new EnsuresSpecification(loc, false, dummyExpr);
			final ArrayList<EnsuresSpecification> dummySpecs = new ArrayList<>(1);
			dummySpecs.add(dummySpec);
			return dummySpecs;
		}

		/**
		 * @return List of {@code RequiresSpecification}s that contains only one {@code RequiresSpecification} which is
		 *         true.
		 */
		private List<RequiresSpecification> getDummyRequiresSpecifications() {
			final Expression dummyExpr = new BooleanLiteral(null, BoogieType.TYPE_BOOL, true);
			final RequiresSpecification dummySpec = new RequiresSpecification(null, false, dummyExpr);
			final ArrayList<RequiresSpecification> dummySpecs = new ArrayList<>(1);
			dummySpecs.add(dummySpec);
			return dummySpecs;
		}

		/**
		 * Remove GotoEdge from a CFG. If allowMultiplicationOfEdges is false, we try to remove the goto by only merging
		 * locations. This is not always possible hence there is no guarantee that the goto is removed. If
		 * allowMultiplicationOfEdges is true, we guarantee that the goto is removed but in some cases will not only
		 * merge locations but also multiply existing edges.
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

				mLogger.debug(mother + " has no sucessors any more or " + child + "has no predecessors any more.");
				mLogger.debug(child + " gets absorbed by " + mother);
				mergeLocNodes(child, mother);
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
		 * <li>append {@code assume (expr)} between the finalNode and the exitNode of the procedure</li> add an edge
		 * labeled with {@code assume (not expr)} from the final Node to the errorNode
		 */
		private void assertAndAssumeEnsures() {
			// Assume the ensures specification at the end of the procedure.
			List<EnsuresSpecification> ensures = mBoogieDeclarations.getEnsures().get(mCurrentProcedureName);
			if (ensures == null || ensures.isEmpty()) {
				final Procedure proc = mBoogieDeclarations.getProcSpecification().get(mCurrentProcedureName);
				ensures = getDummyEnsuresSpecifications(proc.getLocation());
			}
			final BoogieIcfgLocation finalNode = mIcfg.mFinalNode.get(mCurrentProcedureName);
			mLastLabelName = finalNode.getDebugIdentifier();
			mProcLocNodes.put(mLastLabelName, finalNode);
			// mlocSuffix = 0;
			mCurrent = finalNode;

			for (final EnsuresSpecification spec : ensures) {
				final AssumeStatement st = new AssumeStatement(spec.getLocation(), spec.getFormula());
				ModelUtils.copyAnnotations(spec, st);
				mRcfgBacktranslator.putAux(st, new BoogieASTNode[] { spec });
				processAssuAssiHavoStatement(st, Origin.ENSURES);
			}
			final BoogieIcfgLocation exitNode = mIcfg.getProcedureExitNodes().get(mCurrentProcedureName);
			mLastLabelName = exitNode.getDebugIdentifier();
			mProcLocNodes.put(mLastLabelName, exitNode);
			((CodeBlock) mCurrent).connectTarget(exitNode);

			// Violations against the ensures part of the procedure
			// specification
			final List<EnsuresSpecification> ensuresNonFree =
					mBoogieDeclarations.getEnsuresNonFree().get(mCurrentProcedureName);
			if (ensuresNonFree != null && !ensuresNonFree.isEmpty()) {
				for (final EnsuresSpecification spec : ensuresNonFree) {
					final Expression specExpr = spec.getFormula();
					AssumeStatement assumeSt;
					assumeSt = new AssumeStatement(spec.getLocation(), getNegation(specExpr));
					final Statement st = assumeSt;
					ModelUtils.copyAnnotations(spec, st);
					mRcfgBacktranslator.putAux(assumeSt, new BoogieASTNode[] { spec });
					final BoogieIcfgLocation errorLocNode = addErrorNode(mCurrentProcedureName, spec, mProcLocNodes);
					final CodeBlock assumeEdge =
							mCbf.constructStatementSequence(finalNode, errorLocNode, assumeSt, Origin.ENSURES);
					ModelUtils.copyAnnotations(spec, assumeEdge);
					ModelUtils.copyAnnotations(spec, errorLocNode);
					mEdges.add(assumeEdge);
				}
			}
		}

		/**
		 * Assume the requires clause. If the requires clause is empty and dummyRequiresIfEmpty is true add an dummy
		 * requires specification.
		 */
		private void assumeRequires(final boolean dummyRequiresIfEmpty) {
			// Assume everything mentioned in the requires specification
			List<RequiresSpecification> requires = mBoogieDeclarations.getRequires().get(mCurrentProcedureName);
			if ((requires == null || requires.isEmpty()) && dummyRequiresIfEmpty) {
				requires = getDummyRequiresSpecifications();
			}
			if (requires != null && !requires.isEmpty()) {
				for (final RequiresSpecification spec : requires) {
					final AssumeStatement st = new AssumeStatement(spec.getLocation(), spec.getFormula());
					ModelUtils.copyAnnotations(spec, st);
					mRcfgBacktranslator.putAux(st, new BoogieASTNode[] { spec });
					processAssuAssiHavoStatement(st, Origin.REQUIRES);
				}
			}
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
				return new LoopEntryDebugIdentifier(startLine, value.intValue());
			}
			return new OrdinaryDebugIdentifier(startLine, value.intValue());
		}

		/**
		 * Get the LocNode that represents a label. If there is already a LocNode that represents this Label return this
		 * representative. Otherwise construct a new LocNode that becomes the representative for this label.
		 *
		 * @param labelId
		 *            {@link DebugIdentifier} of the Label for which you want the corresponding LocNode.
		 * @param st
		 *            Statement whose (Ultimate) Location should be added to this LocNode. If this method is called
		 *            while processing a GotoStatement the Statement can be set to null, since the Location will be
		 *            overwritten, when this method is called with the correct Label as second parameter.
		 * @return LocNode that is the representative for labelName.
		 */
		private BoogieIcfgLocation getLocNodeForLabel(final DebugIdentifier labelId, final Statement st) {
			final ILocation loc = st.getLocation();
			final LoopEntryAnnotation lea = LoopEntryAnnotation.getAnnotation(st);
			BoogieIcfgLocation locNode = mLabel2LocNodes.get(labelId);
			if (locNode != null) {
				if (mLogger.isDebugEnabled()) {
					mLogger.debug("LocNode for " + labelId + " already" + " constructed, namely: " + locNode);
				}
				if (st instanceof Label && locNode.getDebugIdentifier() == labelId) {

					loc.annotate(locNode);
					if (lea != null && lea.getLoopEntryType() == LoopEntryType.WHILE) {
						if (mLogger.isDebugEnabled()) {
							mLogger.debug("LocNode does not have to Location of the while loop" + st.getLocation());
						}
						mIcfg.getLoopLocations().add(locNode);
					}
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
			if (lea != null && lea.getLoopEntryType() == LoopEntryType.WHILE) {
				mIcfg.getLoopLocations().add(locNode);
			}
			return locNode;
		}

		private void processLabel(final Label st) {
			final String labelName = st.getName();
			final boolean existsAlready = !mLabels.add(labelName);
			if (existsAlready) {
				throw new AssertionError("Label " + labelName + " occurred twice");
			}
			final StringDebugIdentifier tmpLabelIdentifier = new StringDebugIdentifier(labelName);
			if (mCurrent instanceof BoogieIcfgLocation) {
				// from now on this label is represented by mcurrent

				final BoogieIcfgLocation oldNodeForLabel = mLabel2LocNodes.get(tmpLabelIdentifier);
				if (oldNodeForLabel != null) {
					mergeLocNodes(oldNodeForLabel, (BoogieIcfgLocation) mCurrent);
				}
				mLabel2LocNodes.put(tmpLabelIdentifier, (BoogieIcfgLocation) mCurrent);
			} else {
				mLastLabelName = tmpLabelIdentifier;
				// mlocSuffix = 0;

				// is there already a LocNode that represents this
				// label? (This can be the case if this label was destination
				// of a goto statement) If not construct the LocNode.
				// If yes, add the Location Object to the existing LocNode.
				final BoogieIcfgLocation locNode = getLocNodeForLabel(tmpLabelIdentifier, st);

				if (mCurrent instanceof CodeBlock) {
					((IcfgEdge) mCurrent).setTarget(locNode);
					locNode.addIncoming((CodeBlock) mCurrent);
				}
				mCurrent = locNode;
			}
		}

		private void processAssuAssiHavoStatement(final Statement st, final Origin origin) {
			if (mCurrent instanceof BoogieIcfgLocation) {
				startNewStatementSequenceAndAddStatement(st, origin);
			} else if (mCurrent instanceof CodeBlock) {
				if (mCodeBlockSize == CodeBlockSize.SequenceOfStatements
						|| mCodeBlockSize == CodeBlockSize.LoopFreeBlock) {
					addStatementToStatementSequenceThatIsCurrentlyBuilt(st);
				} else {
					endCurrentStatementSequence(st);
					startNewStatementSequenceAndAddStatement(st, origin);
				}
			} else {
				// mcurrent must either be LocNode or TransEdge
				throw new IllegalArgumentException();
			}

		}

		private void endCurrentStatementSequence(final Statement nextSt) {
			final DebugIdentifier locName = constructLocDebugIdentifier(nextSt);
			final BoogieIcfgLocation locNode = new BoogieIcfgLocation(locName, mCurrentProcedureName, false, nextSt);
			((CodeBlock) mCurrent).connectTarget(locNode);
			mCurrent = locNode;
			mProcLocNodes.put(locName, locNode);
		}

		private void startNewStatementSequenceAndAddStatement(final Statement st, final Origin origin) {
			assert isIntraproceduralBranchFreeStatement(st) : "cannot add statement to code block " + st;
			final StatementSequence codeBlock =
					mCbf.constructStatementSequence((BoogieIcfgLocation) mCurrent, null, st, origin);
			ModelUtils.copyAnnotations(st, codeBlock);
			mEdges.add(codeBlock);
			mCurrent = codeBlock;
		}

		private void addStatementToStatementSequenceThatIsCurrentlyBuilt(final Statement st) {
			assert isIntraproceduralBranchFreeStatement(st) : "cannot add statement to code block " + st;
			final StatementSequence stSeq = (StatementSequence) mCurrent;
			stSeq.addStatement(st);
			ModelUtils.copyAnnotations(st, stSeq);
		}

		private boolean isIntraproceduralBranchFreeStatement(final Statement st) {
			if (st instanceof AssumeStatement) {
				return true;
			} else if (st instanceof AssignmentStatement) {
				return true;
			} else if (st instanceof HavocStatement) {
				return true;
			} else if (st instanceof CallStatement) {
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
			} else {
				return false;
			}
		}

		private void processAssertStatement(final AssertStatement st) {
			if (mCurrent instanceof CodeBlock) {
				endCurrentStatementSequence(st);
			}
			final BoogieIcfgLocation locNode = (BoogieIcfgLocation) mCurrent;
			final Expression assertion = st.getFormula();
			final AssumeStatement assumeError = new AssumeStatement(st.getLocation(), getNegation(assertion));
			ModelUtils.copyAnnotations(st, assumeError);
			mRcfgBacktranslator.putAux(assumeError, new BoogieASTNode[] { st });
			final BoogieIcfgLocation errorLocNode = addErrorNode(mCurrentProcedureName, st, mProcLocNodes);
			final StatementSequence assumeErrorCB =
					mCbf.constructStatementSequence(locNode, errorLocNode, assumeError, Origin.ASSERT);
			ModelUtils.copyAnnotations(st, errorLocNode);
			ModelUtils.copyAnnotations(st, assumeErrorCB);
			mEdges.add(assumeErrorCB);
			AssumeStatement assumeSafe = new AssumeStatement(st.getLocation(), assertion);
			if (mAddAssumeForEachAssert) {
				assumeSafe = new AssumeStatement(st.getLocation(), assertion);
			} else {
				// we cannot omit this assume(true) because if the assert is
				// the last node of the procedure the final location will be
				// merged with the last location. In this case this would be
				// the predecessor of the assume(!expression).
				// Hence the error location would be erroneously reachable from
				// the final location.
				assumeSafe = new AssumeStatement(st.getLocation(),
						new BooleanLiteral(st.getLocation(), BoogieType.TYPE_BOOL, true));
			}
			final Statement st1 = assumeSafe;
			ModelUtils.copyAnnotations(st, st1);
			mRcfgBacktranslator.putAux(assumeSafe, new BoogieASTNode[] { st });
			final StatementSequence assumeSafeCB =
					mCbf.constructStatementSequence(locNode, null, assumeSafe, Origin.ASSERT);
			ModelUtils.copyAnnotations(st, assumeSafeCB);
			// add a new TransEdge labeled with st as successor of the
			// last constructed LocNode
			mEdges.add(assumeSafeCB);
			mCurrent = assumeSafeCB;
		}

		private void processGotoStatement(final GotoStatement st) {
			final String[] targets = st.getLabels();
			assert targets.length != 0 : "Goto must have at least one target";
			mLogger.debug("Goto statement with " + targets.length + " targets.");
			BoogieIcfgLocation locNode;
			if (mCurrent instanceof CodeBlock) {
				final DebugIdentifier locName = constructLocDebugIdentifier(st);
				locNode = new BoogieIcfgLocation(locName, mCurrentProcedureName, false, st);
				((CodeBlock) mCurrent).connectTarget(locNode);
				mProcLocNodes.put(locName, locNode);
			} else if (mCurrent instanceof BoogieIcfgLocation) {
				locNode = (BoogieIcfgLocation) mCurrent;
			} else {
				// mcurrent must either LocNode or TransEdge
				throw new IllegalArgumentException();

			}
			for (final String label : targets) {
				// Add an auxiliary GotoEdge and a LocNode
				// for each target of the GotoStatement.
				final BoogieIcfgLocation targetLocNode = getLocNodeForLabel(new StringDebugIdentifier(label), st);
				final GotoEdge newGotoEdge = mCbf.constructGotoEdge(locNode, targetLocNode);
				ModelUtils.copyAnnotations(st, newGotoEdge);
				mGotoEdges.add(newGotoEdge);
			}
			// We have not constructed a new node that should be used in the
			// next iteration step, therefore setting mcurrent to null.
			mCurrent = null;
		}

		private void processCallStatement(final CallStatement st) {
			final String callee = st.getMethodName();
			if ("__VERIFIER_atomic_begin".equals(callee)) {
				beginAtomicBlock(st);
				return;
			}
			if ("__VERIFIER_atomic_end".equals(callee)) {
				endAtomicBlock(st);
				return;
			}
			final List<RequiresSpecification> requiresNonFree = mBoogieDeclarations.getRequiresNonFree().get(callee);
			// Check first for a special case.
			// If the called procedure neither has an implementation nor a non-free requires
			// specification the call is considered as a summary and we may add it to
			// a statement sequence. (Note that this will not work if there is a
			// non-free requires because in this case the control-flow has to
			// branch to an error location.)
			final boolean procedureHasImplementation = mBoogieDeclarations.getProcImplementation().containsKey(callee);
			final boolean nonFreeRequiresIsEmpty = requiresNonFree == null || requiresNonFree.isEmpty();

			if ((mCodeBlockSize == CodeBlockSize.SequenceOfStatements || mCodeBlockSize == CodeBlockSize.LoopFreeBlock)
					&& !procedureHasImplementation && nonFreeRequiresIsEmpty) {
				if (mCurrent instanceof BoogieIcfgLocation) {
					startNewStatementSequenceAndAddStatement(st, Origin.IMPLEMENTATION);
				} else if (mCurrent instanceof CodeBlock) {
					addStatementToStatementSequenceThatIsCurrentlyBuilt(st);
				} else {
					throw new AssertionError("mCurrent must be CodeBlock or BoogieIcfgLocation");
				}
				return;
			}

			BoogieIcfgLocation locNode;
			if (mCurrent instanceof CodeBlock) {
				final DebugIdentifier locName = constructLocDebugIdentifier(st);
				locNode = new BoogieIcfgLocation(locName, mCurrentProcedureName, false, st);
				((CodeBlock) mCurrent).connectTarget(locNode);
				mProcLocNodes.put(locName, locNode);
			} else if (mCurrent instanceof BoogieIcfgLocation) {
				locNode = (BoogieIcfgLocation) mCurrent;
			} else {
				// mcurrent must be either LocNode or TransEdge
				throw new IllegalArgumentException();
			}
			final DebugIdentifier locName = constructLocDebugIdentifier(st);
			final BoogieIcfgLocation returnNode = new BoogieIcfgLocation(locName, mCurrentProcedureName, false, st);
			mProcLocNodes.put(locName, returnNode);
			// add summary edge
			Summary summaryEdge;
			if (mBoogieDeclarations.getProcImplementation().containsKey(callee)) {
				summaryEdge = mCbf.constructSummary(locNode, returnNode, st, true);
				final IIcfgElement cb = summaryEdge;
				ModelUtils.copyAnnotations(st, cb);
				mImplementationSummarys.add(summaryEdge);
			} else {
				summaryEdge = mCbf.constructSummary(locNode, returnNode, st, false);
				final IIcfgElement cb = summaryEdge;
				ModelUtils.copyAnnotations(st, cb);
			}
			mEdges.add(summaryEdge);
			mCurrent = returnNode;

			// Violations against the requires part of the procedure
			// specification. Omit intruduction of these additional auxiliary
			// assert statements if current procedure is START_PROCEDURE.
			//

			// in fork throw unsuportedOperationException
			if (requiresNonFree != null && !requiresNonFree.isEmpty()) {
				for (final RequiresSpecification spec : requiresNonFree) {
					// use implementation if available and specification
					// otherwise. To use the implementation is important in
					// cases where signature of procedure and implementation are
					// different.
					Procedure proc;
					if (mBoogieDeclarations.getProcImplementation().containsKey(callee)) {
						proc = mBoogieDeclarations.getProcImplementation().get(callee);
					} else {
						proc = mBoogieDeclarations.getProcSpecification().get(callee);
					}
					final Expression violatedRequires =
							getNegation(new WeakestPrecondition(spec.getFormula(), st, proc).getResult());
					AssumeStatement assumeSt;
					assumeSt = new AssumeStatement(st.getLocation(), violatedRequires);
					final Statement st1 = assumeSt;
					ModelUtils.copyAnnotations(st, st1);
					mRcfgBacktranslator.putAux(assumeSt, new BoogieASTNode[] { st, spec });
					final BoogieIcfgLocation errorLocNode = addErrorNode(mCurrentProcedureName, st, mProcLocNodes);
					final StatementSequence errorCB =
							mCbf.constructStatementSequence(locNode, errorLocNode, assumeSt, Origin.REQUIRES);
					ModelUtils.copyAnnotations(spec, errorCB);
					ModelUtils.copyAnnotations(spec, errorLocNode);
					mEdges.add(errorCB);
				}
			}
		}

		// FIXME problem if last statement is goto
		// fixed on 16.05.2011 - still needs to be tested
		private void processReturnStatement() {
			// If mcurrent is a transition add as successor the final Node
			// of this procedure.
			// If mcurrent is a location replace it with the final Node of
			// this procedure.
			final BoogieIcfgLocation finalNode = mIcfg.mFinalNode.get(mCurrentProcedureName);
			if (mCurrent instanceof CodeBlock) {
				final CodeBlock transEdge = (CodeBlock) mCurrent;
				transEdge.connectTarget(finalNode);
				if (mLogger.isDebugEnabled()) {
					mLogger.debug("Constructed TransEdge " + transEdge + "as predecessr of " + mIcfg.mFinalNode);
				}
			} else if (mCurrent instanceof BoogieIcfgLocation) {
				mergeLocNodes((BoogieIcfgLocation) mCurrent, finalNode);
				if (mLogger.isDebugEnabled()) {
					mLogger.debug("Replacing " + mCurrent + " by " + finalNode);
				}
			} else {
				// mcurrent must be either LocNode or TransEdge
				// s_Logger.warn("Last location of " + mcurrentProcedureName +
				// "not reachable");
				throw new IllegalArgumentException();
			}
			// No new nodes created, set mcurrent to null
			mCurrent = null;
		}

		/**
		 * This function creates a new location in the cfg and connects it with a forkCurrentThread transition.
		 *
		 * @param st
		 */
		private void processForkStatement(final ForkStatement st) {
			BoogieIcfgLocation locNode;
			if (mCurrent instanceof CodeBlock) {
				final DebugIdentifier locName = constructLocDebugIdentifier(st);
				locNode = new BoogieIcfgLocation(locName, mCurrentProcedureName, false, st);
				((CodeBlock) mCurrent).connectTarget(locNode);
				mProcLocNodes.put(locName, locNode);
			} else if (mCurrent instanceof BoogieIcfgLocation) {
				locNode = (BoogieIcfgLocation) mCurrent;
			} else {
				throw new IllegalArgumentException();
			}
			final DebugIdentifier locName = constructLocDebugIdentifier(st);

			final BoogieIcfgLocation forkCurrentNode =
					new BoogieIcfgLocation(locName, mCurrentProcedureName, false, st);
			mProcLocNodes.put(locName, forkCurrentNode);

			final String callee = st.getProcedureName();
			ForkThreadCurrent forkCurrentThreadEdge;
			if (mBoogieDeclarations.getProcImplementation().containsKey(callee)) {
				forkCurrentThreadEdge = mCbf.constructForkCurrentThread(locNode, forkCurrentNode, st, true);
				final IIcfgElement cb = forkCurrentThreadEdge;
				ModelUtils.copyAnnotations(st, cb);
				mForks.put(forkCurrentThreadEdge, null);
			} else {
				forkCurrentThreadEdge = mCbf.constructForkCurrentThread(locNode, forkCurrentNode, st, false);
				final IIcfgElement cb = forkCurrentThreadEdge;
				ModelUtils.copyAnnotations(st, cb);
			}
			mEdges.add(forkCurrentThreadEdge);
			mCurrent = forkCurrentNode;
		}

		/**
		 * This function creates a new location in the cfg and connects it with a joinCurrentThread transition.
		 *
		 * @param st
		 */
		private void processJoinStatement(final JoinStatement st) {
			BoogieIcfgLocation locNode;
			if (mCurrent instanceof CodeBlock) {
				final DebugIdentifier locName = constructLocDebugIdentifier(st);
				locNode = new BoogieIcfgLocation(locName, mCurrentProcedureName, false, st);
				((CodeBlock) mCurrent).connectTarget(locNode);
				mProcLocNodes.put(locName, locNode);
			} else if (mCurrent instanceof BoogieIcfgLocation) {
				locNode = (BoogieIcfgLocation) mCurrent;
			} else {
				throw new IllegalArgumentException();
			}
			final DebugIdentifier locName = constructLocDebugIdentifier(st);

			final BoogieIcfgLocation joinCurrentNode =
					new BoogieIcfgLocation(locName, mCurrentProcedureName, false, st);
			mProcLocNodes.put(locName, joinCurrentNode);

			final JoinThreadCurrent joinCurrentThreadEdge =
					mCbf.constructJoinCurrentThread(locNode, joinCurrentNode, st);
			final IIcfgElement cb = joinCurrentThreadEdge;
			ModelUtils.copyAnnotations(st, cb);
			mJoins.add(joinCurrentThreadEdge);

			mEdges.add(joinCurrentThreadEdge);
			mCurrent = joinCurrentNode;
		}

		private void beginAtomicBlock(final Statement st) {
			if (mCurrent instanceof CodeBlock) {
				endCurrentStatementSequence(st);
			}
			assert mCurrent instanceof BoogieIcfgLocation : "Atomic section must begin with ICFG location";
			AtomicBlockInfo.addBeginAnnotation(mCurrent);
		}

		private void endAtomicBlock(final Statement st) {
			if (mCurrent instanceof CodeBlock) {
				endCurrentStatementSequence(st);
			}
			assert mCurrent instanceof BoogieIcfgLocation : "Atomic section must end with ICFG location";
			AtomicBlockInfo.addEndAnnotation(mCurrent);
		}

		private void processAtomicStatement(final String procName, final AtomicStatement atomicStatement,
				final Statement precedingSt) {
			beginAtomicBlock(atomicStatement);

			for (int i = 0; i < atomicStatement.getBody().length; i++) {
				final Statement st = atomicStatement.getBody()[i];
				final Statement prevStmt = i == 0 ? precedingSt : atomicStatement.getBody()[i - 1];
				processStatement(procName, st, prevStmt);
			}

			endAtomicBlock(atomicStatement);
		}

		/**
		 * Merge one LocNode into another. The oldLocNode will be merged into the newLocNode. The newLocNode gets
		 * connected to all incoming/outgoing transitions of the oldLocNode. The oldLocNode looses connections to all
		 * incoming/outgoing transitions. If the oldLocNode was representative for a Label the new location will from
		 * now on be the representative of this Label.
		 *
		 * @param oldLocNode
		 *            LocNode that gets merged into the newLocNode. Must not represent an error location.
		 * @param newLocNode
		 *            LocNode that absorbes the oldLocNode.
		 */
		private void mergeLocNodes(final BoogieIcfgLocation oldLocNode, final BoogieIcfgLocation newLocNode) {
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
			ModelUtils.copyAnnotations(oldLocNode, newLocNode);
		}
	}

	/**
	 * Defines which statements will be composed.
	 */
	private enum InternalLbeMode {
		ONLY_ATOMIC_BLOCK, ATOMIC_BLOCK_AND_INBETWEEN_SEQUENCE_POINTS, ALL
	}

	private enum SequentialCompositionType {
		NONE, STRAIGHTLINE, Y2V
	}

	private class LargeBlockEncoding {
		private final InternalLbeMode mInternalLbeMode;
		final boolean mSimplifyCodeBlocks;
		private final Set<BoogieIcfgLocation> mAtomicPoints = new HashSet<>();

		// straight-line sequential composition points
		private final Set<BoogieIcfgLocation> mSequentialQueue = new HashSet<>();

		// Y-to-V and upside-down Y-to-V composition points
		private final Set<BoogieIcfgLocation> mComplexSequentialQueue = new HashSet<>();

		private final Map<BoogieIcfgLocation, List<CodeBlock>> mParallelQueue = new HashMap<>();

		public LargeBlockEncoding(final InternalLbeMode internalLbeMode) {
			mInternalLbeMode = internalLbeMode;
			mSimplifyCodeBlocks = mServices.getPreferenceProvider(Activator.PLUGIN_ID)
					.getBoolean(RcfgPreferenceInitializer.LABEL_SIMPLIFY);
			if (mInternalLbeMode == InternalLbeMode.ATOMIC_BLOCK_AND_INBETWEEN_SEQUENCE_POINTS
					|| mInternalLbeMode == InternalLbeMode.ONLY_ATOMIC_BLOCK) {
				collectAtomicPoints();
			}

			getAllLocations().forEach(pp -> considerCompositionCandidate(pp, true));

			// We distinguish 3 types of compositions: straight-line sequential compositions, parallel compositions, and
			// Y-to-V sequential compositions. We employ Y-to-V compositions extremely sparingly, as they can lead to
			// the creation of an exponential number of edges for complex branching code. Often, all these edges are
			// later reduced through parallel composition to very few edges (but a timeout occurs before this happens).
			while (!mSequentialQueue.isEmpty() || !mParallelQueue.isEmpty() || !mComplexSequentialQueue.isEmpty()) {
				while (mSequentialQueue.isEmpty() && mParallelQueue.isEmpty() && !mComplexSequentialQueue.isEmpty()) {
					final BoogieIcfgLocation superfluousPP = mComplexSequentialQueue.iterator().next();
					mComplexSequentialQueue.remove(superfluousPP);
					composeSequential(superfluousPP);
					mLogger.debug("Y2V composition at %s", superfluousPP);
				}

				while (mSequentialQueue.isEmpty() && !mParallelQueue.isEmpty()) {
					final Entry<BoogieIcfgLocation, List<CodeBlock>> superfluous =
							mParallelQueue.entrySet().iterator().next();
					final BoogieIcfgLocation pp = superfluous.getKey();
					final List<CodeBlock> outgoing = superfluous.getValue();
					mParallelQueue.remove(pp);
					composeParallel(pp, outgoing);
					mLogger.debug("parallel composition at %s", pp);
				}

				while (!mSequentialQueue.isEmpty()) {
					final BoogieIcfgLocation superfluousPP = mSequentialQueue.iterator().next();
					mSequentialQueue.remove(superfluousPP);
					composeSequential(superfluousPP);
					mLogger.debug("sequential composition at %s", superfluousPP);
				}

				mComplexSequentialQueue.clear();
				mParallelQueue.clear();
				mSequentialQueue.clear();

				getAllLocations().forEach(pp -> considerCompositionCandidate(pp, true));
			}
		}

		/**
		 * Identifies all nodes that are inside an atomic block (start and end of the block do not count).
		 */
		private void collectAtomicPoints() {
			final ArrayDeque<BoogieIcfgLocation> worklist = new ArrayDeque<>();
			final Set<BoogieIcfgLocation> visited = new HashSet<>();

			// Begin at start nodes of atomic blocks
			getAllLocations().filter(CfgBuilder::isStartOfAtomicBlock).forEach(worklist::add);

			while (!worklist.isEmpty()) {
				final BoogieIcfgLocation pp = worklist.poll();
				if (visited.contains(pp)) {
					continue;
				}
				visited.add(pp);

				if (!isStartOfAtomicBlock(pp) && !isEndOfAtomicBlock(pp)) {
					mAtomicPoints.add(pp);
				}
				if (!isEndOfAtomicBlock(pp) || isStartOfAtomicBlock(pp)) {
					for (final IcfgEdge edge : pp.getOutgoingEdges()) {
						worklist.add((BoogieIcfgLocation) edge.getTarget());
					}
				}
			}

			assert getAllLocations().allMatch(pp -> !mAtomicPoints.contains(pp)
					|| allPredecessorsAtomic(pp)) : "Atomic point with unexpected non-atomic predecessor!";
			assert getAllLocations().allMatch(pp -> !mAtomicPoints.contains(pp)
					|| allSuccessorsAtomic(pp)) : "Atomic point with unexpected non-atomic successor!";
		}

		private boolean allPredecessorsAtomic(final BoogieIcfgLocation pp) {
			return pp.getIncomingEdges().stream().map(IcfgEdge::getSource)
					.allMatch(pre -> mAtomicPoints.contains(pre) || isStartOfAtomicBlock(pre));
		}

		private boolean allSuccessorsAtomic(final BoogieIcfgLocation pp) {
			return pp.getOutgoingEdges().stream().map(IcfgEdge::getTarget)
					.allMatch(suc -> mAtomicPoints.contains(suc) || isEndOfAtomicBlock(suc));
		}

		/**
		 * Determines if the given node is a composition candidate. If so, it is placed in the appropriate queue,
		 * depending on what kind of composition is to be performed.
		 */
		private void considerCompositionCandidate(final BoogieIcfgLocation pp, final boolean allowY2V) {
			final SequentialCompositionType seq = classifySequentialCompositionNode(pp);
			if (seq == SequentialCompositionType.STRAIGHTLINE) {
				mSequentialQueue.add(pp);
				return;
			}

			// As mentioned above, we prefer parallel over Y-to-V compositions.
			final List<CodeBlock> list = computeOutgoingCandidatesForParallelComposition(pp);
			if (list != null) {
				mParallelQueue.put(pp, list);
			} else if (seq == SequentialCompositionType.Y2V && allowY2V) {
				mComplexSequentialQueue.add(pp);
			}
		}

		/**
		 * Performs a (straight-line or Y-to-V) sequential composition. Afterwards, the new predecessors and successors
		 * are again considered for further compositions.
		 */
		private void composeSequential(final BoogieIcfgLocation pp) {
			assert !pp.getIncomingEdges().isEmpty();
			assert !pp.getOutgoingEdges().isEmpty();

			final List<IcfgEdge> incomingEdges = new ArrayList<>(pp.getIncomingEdges());
			final List<IcfgEdge> outgoingEdges = new ArrayList<>(pp.getOutgoingEdges());
			final List<IcfgEdge> newEdges = new ArrayList<>();

			for (final IcfgEdge incoming : incomingEdges) {
				for (final IcfgEdge outgoing : outgoingEdges) {
					final BoogieIcfgLocation predecessor = (BoogieIcfgLocation) incoming.getSource();
					final BoogieIcfgLocation successor = (BoogieIcfgLocation) outgoing.getTarget();
					final List<CodeBlock> sequence = Arrays.asList((CodeBlock) incoming, (CodeBlock) outgoing);

					final SequentialComposition comp = mCbf.constructSequentialComposition(predecessor, successor,
							mSimplifyCodeBlocks, false, sequence, mXnfConversionTechnique, mSimplificationTechnique);
					ModelUtils.copyAnnotations(incoming, comp);
					ModelUtils.copyAnnotations(outgoing, comp);
					newEdges.add(comp);
				}
			}

			// remove composed edges from Icfg
			for (final IcfgEdge currentCodeblock : incomingEdges) {
				currentCodeblock.disconnectSource();
				currentCodeblock.disconnectTarget();
			}
			for (final IcfgEdge currentCodeblock : outgoingEdges) {
				currentCodeblock.disconnectSource();
				currentCodeblock.disconnectTarget();
			}

			// Continue composition where needed.
			// For correct detection, this must happen after edge removal.
			final Set<BoogieIcfgLocation> candidates = new HashSet<>();
			newEdges.forEach(e -> candidates.add((BoogieIcfgLocation) e.getSource()));
			newEdges.forEach(e -> candidates.add((BoogieIcfgLocation) e.getTarget()));
			for (final BoogieIcfgLocation candidate : candidates) {
				considerCompositionCandidate(candidate, false);
			}

			// remove location from Icfg
			final Map<DebugIdentifier, BoogieIcfgLocation> id2loc = mIcfg.getProgramPoints().get(pp.getProcedure());
			id2loc.remove(pp.getDebugIdentifier());
			mAtomicPoints.remove(pp);
		}

		/**
		 * Performs a parallel composition. Afterwards, the predecessor and successor are again considered for further
		 * compositions.
		 */
		private void composeParallel(final BoogieIcfgLocation pp, final List<CodeBlock> outgoing) {
			final BoogieIcfgLocation successor = (BoogieIcfgLocation) outgoing.get(0).getTarget();
			mCbf.constructParallelComposition(pp, successor, Collections.unmodifiableList(outgoing),
					mXnfConversionTechnique, mSimplificationTechnique);
			considerCompositionCandidate(pp, false);
			considerCompositionCandidate(successor, false);
		}

		/**
		 * Determines what kind of sequential composition (if any) should be performed at this node.
		 */
		private SequentialCompositionType classifySequentialCompositionNode(final BoogieIcfgLocation pp) {
			if (pp.getIncomingEdges().isEmpty() || pp.getOutgoingEdges().isEmpty()) {
				return SequentialCompositionType.NONE;
			}
			if (DataStructureUtils.haveNonEmptyIntersection(new HashSet<>(pp.getIncomingEdges()),
					new HashSet<>(pp.getOutgoingEdges()))) {
				// do not allow loops
				return SequentialCompositionType.NONE;
			}

			final boolean edgesComposable = pp.getIncomingEdges().stream().allMatch(this::isComposableEdge)
					&& pp.getOutgoingEdges().stream().allMatch(this::isComposableEdge);
			if (!edgesComposable) {
				return SequentialCompositionType.NONE;
			}

			final boolean isStraightline = pp.getIncomingEdges().size() == 1 && pp.getOutgoingEdges().size() == 1;
			final boolean isBetweenSequencePoints = false; // TODO #FaultLocalization

			final boolean isInAtomicBlock = mAtomicPoints.contains(pp);
			if (isInAtomicBlock) {
				assert allPredecessorsAtomic(pp) : "Atomic point " + pp + " has non-atomic predecessors";
				assert allSuccessorsAtomic(pp) : "Atomic point " + pp + " has non-atomic successors";
			}

			switch (mInternalLbeMode) {
			case ALL:
				if (isStraightline) {
					return SequentialCompositionType.STRAIGHTLINE;
				} else if (isInAtomicBlock || isBetweenSequencePoints) {
					// Y-V currently unsupported outside atomic blocks (implementation cannot handle loops properly)
					// TODO (Dominik 2020-09-16) Check if above comment still holds after Y-to-V fix, may work now (as
					// loop entry is reverse Y-to-V).
					return SequentialCompositionType.Y2V;
				}
				return SequentialCompositionType.NONE;
			case ATOMIC_BLOCK_AND_INBETWEEN_SEQUENCE_POINTS:
				// TODO #FaultLocalization
				// return isInAtomicBlock || isBetweenSequencePoints;
				throw new UnsupportedOperationException();
			case ONLY_ATOMIC_BLOCK:
				if (!isInAtomicBlock) {
					return SequentialCompositionType.NONE;
				} else if (isStraightline) {
					return SequentialCompositionType.STRAIGHTLINE;
				} else {
					return SequentialCompositionType.Y2V;
				}
			default:
				throw new AssertionError("unknown value " + mInternalLbeMode);
			}
		}

		private boolean isComposableEdge(final IcfgEdge edge) {
			if (edge instanceof RootEdge || edge instanceof Call || edge instanceof Return) {
				return false;
			}
			if (edge instanceof IIcfgForkTransitionThreadCurrent || edge instanceof IIcfgForkTransitionThreadOther
					|| edge instanceof IIcfgJoinTransitionThreadCurrent
					|| edge instanceof IIcfgJoinTransitionThreadOther) {
				return false;
			}
			assert edge instanceof StatementSequence || edge instanceof SequentialComposition
					|| edge instanceof ParallelComposition || edge instanceof Summary
					|| edge instanceof GotoEdge : "unexpected type of edge: "
							+ edge.getClass().getSimpleName();
			return true;
		}

		/**
		 * Check if ProgramPoint pp has several outgoing edges whose target is the same ProgramPoint.
		 *
		 * @return For some successor ProgramPoint the list of all outgoing edges whose target is this (successor)
		 *         ProgramPoint, if there can be such a list with more than one element. Otherwise (each outgoing edge
		 *         leads to a different ProgramPoint) return null.
		 */
		private List<CodeBlock> computeOutgoingCandidatesForParallelComposition(final BoogieIcfgLocation pp) {
			if (!canBePredecessorOfParallelComposition(pp)) {
				return null;
			}
			List<CodeBlock> result = null;
			final Map<BoogieIcfgLocation, List<CodeBlock>> succ2edge = new HashMap<>();
			for (final IcfgEdge edge : pp.getOutgoingEdges()) {
				if (!(edge instanceof Return) && !(edge instanceof Summary)) {
					final CodeBlock cb = (CodeBlock) edge;
					final BoogieIcfgLocation succ = (BoogieIcfgLocation) cb.getTarget();
					if (canBeSuccessorOfParallelComposition(succ)) {
						List<CodeBlock> edges = succ2edge.get(succ);
						if (edges == null) {
							edges = new ArrayList<>();
							succ2edge.put(succ, edges);
						}
						edges.add(cb);
						if (result == null && edges.size() > 1) {
							result = edges;
						}
					}
				}
			}
			return result;
		}

		private boolean canBePredecessorOfParallelComposition(final BoogieIcfgLocation pp) {
			switch (mInternalLbeMode) {
			case ALL:
				return true;
			case ATOMIC_BLOCK_AND_INBETWEEN_SEQUENCE_POINTS:
				// TODO #FaultLocalization
				throw new UnsupportedOperationException();
			case ONLY_ATOMIC_BLOCK:
				// In order to only perform compositions within atomic blocks, we have this condition.
				// It would also be sound to return true, as more parallel compositions are not a threat to soundness.
				return isStartOfAtomicBlock(pp) || mAtomicPoints.contains(pp);
			default:
				throw new AssertionError("unknown value " + mInternalLbeMode);
			}
		}

		private boolean canBeSuccessorOfParallelComposition(final BoogieIcfgLocation pp) {
			switch (mInternalLbeMode) {
			case ALL:
				return true;
			case ATOMIC_BLOCK_AND_INBETWEEN_SEQUENCE_POINTS:
				// TODO #FaultLocalization
				throw new UnsupportedOperationException();
			case ONLY_ATOMIC_BLOCK:
				// In order to only perform compositions within atomic blocks, we have this condition.
				// It would also be sound to return true, as more parallel compositions are not a threat to soundness.
				//
				// In order to catch all possible compositions within atomic blocks,
				// we would also have to allow error locations and possibly (see atomicModeCorrect) return / exit nodes.
				// However, this is not strictly necessary, as less parallel compositions are not a threat to soundness.
				return mAtomicPoints.contains(pp) || isEndOfAtomicBlock(pp);
			default:
				throw new AssertionError("unknown value " + mInternalLbeMode);
			}
		}
	}
}
