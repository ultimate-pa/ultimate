/*
 * Copyright (C) 2023 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE TreeAutomizer plug-in.
 *
 * The ULTIMATE TreeAutomizer plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TreeAutomizer plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TreeAutomizer plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE RCFGBuilder plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TreeAutomizer plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.treeautomizer;

import java.util.ArrayDeque;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.tree.Tree;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TimeoutResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TreeAutomizerSatResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TreeAutomizerUnsatResult;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.chc.Derivation;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.chc.HornAnnot;
import de.uni_freiburg.informatik.ultimate.lib.chc.HornClause;
import de.uni_freiburg.informatik.ultimate.lib.chc.IChcScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Model;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.treeautomizer.graph.TreeAutomizerCEGAR;

public class TreeAutomizerChcScript implements IChcScript {
	private static final String DUMMY_FILENAME = TreeAutomizerChcScript.class.getSimpleName();

	private final IUltimateServiceProvider mServices;
	private final ManagedScript mMgdScript;
	private final TAPreferences mPrefs;
	private final ILogger mLogger;

	private boolean mProduceUnsatCores = false;

	private Set<HornClause> mUnsatCore;

	public TreeAutomizerChcScript(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final TAPreferences prefs) {
		mServices = services;
		mMgdScript = mgdScript;
		mPrefs = prefs;

		mLogger = mServices.getLoggingService().getLogger(TreeAutomizerChcScript.class);
	}

	@Override
	public Script getScript() {
		return mMgdScript.getScript();
	}

	@Override
	public LBool solve(final HcSymbolTable symbolTable, final List<HornClause> system) {
		reset();

		// TODO missing parameter: category info
		final var annot = new HornAnnot(DUMMY_FILENAME, mMgdScript, symbolTable, system, true, null);
		final var cegar = new TreeAutomizerCEGAR(mServices, annot, mPrefs, mLogger);
		try {
			final var result = cegar.iterate();
			return resultToLBool(result);
		} catch (final AutomataLibraryException e) {
			throw new IllegalStateException(e);
		}
	}

	private LBool resultToLBool(final IResult result) {
		if (result instanceof TreeAutomizerSatResult) {
			return LBool.SAT;
		}
		if (result instanceof TreeAutomizerUnsatResult) {
			if (mProduceUnsatCores) {
				final var tree = (Tree<HornClause>) ((TreeAutomizerUnsatResult) result).getWitness();
				mUnsatCore = extractUnsatCore(tree);
			}
			return LBool.UNSAT;
		}
		if (result instanceof TimeoutResult) {
			return LBool.UNKNOWN;
		}
		throw new IllegalArgumentException("Unknown result type: " + result.getClass());
	}

	@Override
	public boolean supportsModelProduction() {
		// TODO TreeAutomizer seems to produce some kind model, but just logs it (instead of returning it)
		return false;
	}

	@Override
	public void produceModels(final boolean enable) {
		throw new UnsupportedOperationException();
	}

	@Override
	public Model getModel() {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean supportsDerivationProduction() {
		return false;
	}

	@Override
	public void produceDerivations(final boolean enable) {
		throw new UnsupportedOperationException();
	}

	@Override
	public Derivation getDerivation() {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean supportsUnsatCores() {
		return true;
	}

	@Override
	public void produceUnsatCores(final boolean enable) {
		mProduceUnsatCores = enable;
	}

	@Override
	public Set<HornClause> getUnsatCore() {
		if (mUnsatCore == null) {
			throw new UnsupportedOperationException(
					"No UNSAT core known. Was the last query SAT, or did you forget to enable UNSAT cores?");
		}
		return mUnsatCore;
	}

	private static Set<HornClause> extractUnsatCore(final Tree<HornClause> tree) {
		final var worklist = new ArrayDeque<Tree<HornClause>>();
		worklist.add(tree);

		final var result = new HashSet<HornClause>();
		while (!worklist.isEmpty()) {
			final var node = worklist.pop();
			result.add(node.getSymbol());
			worklist.addAll(node.getChildren());
		}

		return result;
	}

	private void reset() {
		mUnsatCore = null;
	}
}
