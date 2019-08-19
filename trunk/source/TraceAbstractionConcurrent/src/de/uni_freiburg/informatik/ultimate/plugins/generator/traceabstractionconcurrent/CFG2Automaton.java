/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2011-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstractionConcurrent plug-in.
 *
 * The ULTIMATE TraceAbstractionConcurrent plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstractionConcurrent plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstractionConcurrent plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstractionConcurrent plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstractionConcurrent plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstractionconcurrent;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocationIterator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.RcfgPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.RcfgPreferenceInitializer.CodeBlockSize;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;

public abstract class CFG2Automaton<LETTER extends IIcfgTransition<?>, RESULT> {

	private static final String INIT_PROCEDURE = "~init";

	protected final ILogger mLogger;
	protected final IUltimateServiceProvider mServices;
	private final SimplificationTechnique mSimplificationTechnique;
	private final XnfConversionTechnique mXnfConversionTechnique;

	private final IIcfg<?> mIcfg;
	private final CfgSmtToolkit mCsToolkit;
	private final PredicateFactory mPredicateFactory;
	private final IEmptyStackStateFactory<IPredicate> mContentFactory;
	protected List<INestedWordAutomaton<LETTER, IPredicate>> mAutomata;

	private LETTER mSharedVarsInit;

	public CFG2Automaton(final IIcfg<?> icfg, final IEmptyStackStateFactory<IPredicate> contentFactory,
			final CfgSmtToolkit csToolkit, final PredicateFactory predicateFactory,
			final IUltimateServiceProvider services, final SimplificationTechnique simplificationTechnique,
			final XnfConversionTechnique xnfConversionTechnique) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mSimplificationTechnique = simplificationTechnique;
		mXnfConversionTechnique = xnfConversionTechnique;
		mIcfg = icfg;
		mContentFactory = contentFactory;
		mCsToolkit = csToolkit;
		mPredicateFactory = predicateFactory;
	}

	public abstract RESULT getResult();

	protected void constructProcedureAutomata() {
		final CodeBlockSize codeBlockSize = RcfgPreferenceInitializer.getPreferences(mServices)
				.getEnum(RcfgPreferenceInitializer.LABEL_CODE_BLOCK_SIZE, RcfgPreferenceInitializer.CodeBlockSize.class);
		if (codeBlockSize != CodeBlockSize.SingleStatement) {
			throw new IllegalArgumentException("Concurrent programs reqire" + "atomic block encoding.");
		}

		if (!mIcfg.getProcedureEntryNodes().containsKey(INIT_PROCEDURE)) {
			throw new IllegalArgumentException(
					"Concurrent program needs procedure " + INIT_PROCEDURE + " to initialize shared variables");
		}

		final int numberOfProcedures = mIcfg.getProcedureEntryNodes().size() - 1;
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Program has procedure to initialize shared variables");
			mLogger.debug("Found " + numberOfProcedures + "Procedures");
		}
		mAutomata = new ArrayList<>(numberOfProcedures);
		mSharedVarsInit = extractPrecondition();

		mIcfg.getProcedureEntryNodes().entrySet().stream().filter(a -> !a.getKey().equals(INIT_PROCEDURE))
				.map(a -> getNestedWordAutomaton(a.getValue())).forEach(mAutomata::add);
		assert mAutomata.size() == numberOfProcedures;
	}

	private LETTER extractPrecondition() {
		assert mIcfg.getProcedureEntryNodes().containsKey(INIT_PROCEDURE);

		if (!(mIcfg instanceof BoogieIcfgContainer)) {
			// TODO: Remove this dirty hack when refactoring is complete
			throw new UnsupportedOperationException();
		}
		final BoogieIcfgContainer boogieIcfg = (BoogieIcfgContainer) mIcfg;

		final BoogieIcfgLocation entry = boogieIcfg.getProcedureEntryNodes().get(INIT_PROCEDURE);
		final BoogieIcfgLocation exit = boogieIcfg.getProcedureExitNodes().get(INIT_PROCEDURE);
		final List<CodeBlock> codeBlocks = new ArrayList<>();

		IcfgLocation current = entry;
		while (current != exit) {
			assert current.getOutgoingEdges().size() == 1;
			assert current.getOutgoingEdges().get(0) instanceof StatementSequence;
			// TODO: Statement sequences are no longer guaranteed here
			final StatementSequence succSS = (StatementSequence) current.getOutgoingEdges().get(0);
			assert succSS.getStatements().size() == 1;
			codeBlocks.add(succSS);
			current = succSS.getTarget();
		}

		// TODO: This cast to letter will probably not fail if nothing in this method failed before
		return (LETTER) boogieIcfg.getCodeBlockFactory().constructSequentialComposition(entry, exit, true, false,
				codeBlocks, mXnfConversionTechnique, mSimplificationTechnique);
	}

	/**
	 * Build NestedWordAutomaton for all code reachable from initial Node which is in the same procedure as initial
	 * Node. Initial Node does not have to be the entry Node of a procedure.
	 */
	@SuppressWarnings("unchecked")
	private INestedWordAutomaton<LETTER, IPredicate> getNestedWordAutomaton(final IcfgLocation initialNode) {

		mLogger.debug("Step: Collect all LocNodes corresponding to" + " this procedure");
		final Set<IcfgLocation> allNodes =
				new IcfgLocationIterator<>(initialNode).asStream().collect(Collectors.toSet());

		mLogger.debug("Step: determine the alphabet");
		// determine the alphabet
		final Set<LETTER> internalAlphabet = new HashSet<>();

		// add transAnnot from sharedVars initialization
		internalAlphabet.add(mSharedVarsInit);

		allNodes.stream().flatMap(a -> a.getOutgoingEdges().stream()).forEach(edge -> {
			if (edge instanceof Summary || edge instanceof IIcfgCallTransition<?>
					|| edge instanceof IIcfgReturnTransition<?, ?>) {
				throw new IllegalArgumentException("Procedure calls not supported by concurrent trace abstraction");
			}
			internalAlphabet.add((LETTER) edge);
		});

		mLogger.debug("Step: construct the automaton");
		// construct the automaton
		final NestedWordAutomaton<LETTER, IPredicate> nwa = new NestedWordAutomaton<>(
				new AutomataLibraryServices(mServices), new VpAlphabet<LETTER>(internalAlphabet), mContentFactory);

		IPredicate procedureInitialState = null;

		mLogger.debug("Step: add states");
		final Map<IcfgLocation, IPredicate> nodes2States = new HashMap<>();
		// add states
		for (final IcfgLocation locNode : allNodes) {
			final boolean isErrorLocation = isErrorLocation(locNode);
			final Term trueTerm = mCsToolkit.getManagedScript().getScript().term("true");
			final IPredicate automatonState = mPredicateFactory.newSPredicate(locNode, trueTerm);
			nwa.addState(false, isErrorLocation, automatonState);
			nodes2States.put(locNode, automatonState);
			if (locNode == initialNode) {
				assert procedureInitialState == null : "Procedure must have" + "only one initial state";
				procedureInitialState = automatonState;
			}
		}

		mLogger.debug("Step: add transitions");
		// add transitions
		for (final IcfgLocation locNode : allNodes) {
			final IPredicate state = nodes2States.get(locNode);
			if (locNode.getOutgoingNodes() != null) {
				for (final IcfgEdge edge : locNode.getOutgoingEdges()) {
					final IcfgLocation succLoc = edge.getTarget();
					final IPredicate succState = nodes2States.get(succLoc);
					nwa.addInternalTransition(state, (LETTER) edge, succState);
				}
			}
		}

		mLogger.debug("Step: SharedVarsInit part");
		final BoogieIcfgLocation entryOfInitProc = (BoogieIcfgLocation) mSharedVarsInit.getSource();
		final Term trueTerm = mCsToolkit.getManagedScript().getScript().term("true");
		final IPredicate initialContent = mPredicateFactory.newSPredicate(entryOfInitProc, trueTerm);
		nwa.addState(true, false, initialContent);
		IPredicate automatonSuccState;
		automatonSuccState = procedureInitialState;
		nwa.addInternalTransition(initialContent, mSharedVarsInit, automatonSuccState);

		return nwa;
	}

	private boolean isErrorLocation(final IcfgLocation locNode) {
		if (locNode == null) {
			return false;
		}
		final String proc = locNode.getProcedure();
		final Set<?> errorLocsForProc = mIcfg.getProcedureErrorNodes().get(proc);
		if (errorLocsForProc == null) {
			return false;
		}
		return errorLocsForProc.contains(locNode);
	}

}
