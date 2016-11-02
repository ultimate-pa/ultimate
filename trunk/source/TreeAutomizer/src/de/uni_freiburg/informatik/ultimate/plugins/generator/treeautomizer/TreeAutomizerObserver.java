/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2010-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE HornClauseGraphBuilder plug-in.
 * 
 * The ULTIMATE HornClauseGraphBuilder plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE HornClauseGraphBuilder plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE HornClauseGraphBuilder plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE HornClauseGraphBuilder plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE HornClauseGraphBuilder plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.treeautomizer;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.treeautomizer.hornutil.HCTransFormula;
import de.uni_freiburg.informatik.ultimate.plugins.generator.treeautomizer.hornutil.HornClause;
import de.uni_freiburg.informatik.ultimate.plugins.generator.treeautomizer.hornutil.HornClausePredicateSymbol;
import de.uni_freiburg.informatik.ultimate.plugins.generator.treeautomizer.script.HornAnnot;

/**
 * import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonBU; /**
 * Auto-Generated Stub for the plug-in's Observer
 */
public class TreeAutomizerObserver implements IUnmanagedObserver {

	private final IUltimateServiceProvider mServices;
	private final IToolchainStorage mToolchainStorage;
	private final ILogger mLogger;
	
	public TreeAutomizerObserver(final IUltimateServiceProvider services, final IToolchainStorage toolchainStorage) {
		mServices = services;
		mToolchainStorage = toolchainStorage;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}

	@Override
	public void init(final ModelType modelType, final int currentModelIndex, final int numberOfModels) throws Throwable {
		// TODO Auto-generated method stub

	}

	@Override
	public void finish() throws Throwable {
		// TODO Auto-generated method stub

	}

	@Override
	public boolean performedChanges() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean process(final IElement root) throws Throwable {
		
		final RootNode rootNode = (RootNode) root;
		rootNode.getRootAnnot().getScript();
		
		final Map<String, IAnnotations> st = root.getPayload().getAnnotations();
		final HornAnnot annot = (HornAnnot) st.get("HoRNClauses");
		final List<HornClause> hornClauses = (List<HornClause>) annot.getAnnotationsAsMap().get("HoRNClauses");

		final TreeAutomatonBU<HCTransFormula, HornClausePredicateSymbol> tree = new TreeAutomatonBU<>();
		
		for (final HornClause clause : hornClauses) {
			final List<HornClausePredicateSymbol> tail = new ArrayList<HornClausePredicateSymbol>();
			tail.addAll(clause.getTailPredicates());
			tree.addRule(clause.getTransitionFormula(), tail, clause.getHeadPredicate());
		}
		
		// TODO(mostafa): Add initial and final states.
		tree.addFinalState(new HornClausePredicateSymbol.HornClauseFalsePredicateSymbol());
		//tree.addFinalState(state);
		//tree.addInitialState(state);
//		TreeAutomizerCEGAR cegar = new TreeAutomizerCEGAR(mServices,
//				mToolchainStorage, "name", rootNode, csToolkit, taPrefs, errorLocs, mLogger, script);
		return false;
	}

}
