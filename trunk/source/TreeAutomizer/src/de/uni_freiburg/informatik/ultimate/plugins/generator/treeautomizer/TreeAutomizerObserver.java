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

import javax.xml.parsers.FactoryConfigurationError;

import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.treeautomizer.hornutil.HCTransFormula;
import de.uni_freiburg.informatik.ultimate.plugins.generator.treeautomizer.hornutil.HornClause;
import de.uni_freiburg.informatik.ultimate.plugins.generator.treeautomizer.hornutil.HornClausePredicateSymbol;
import de.uni_freiburg.informatik.ultimate.plugins.generator.treeautomizer.script.HornAnnot;

/**
 * import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonBU; /**
 * Auto-Generated Stub for the plug-in's Observer
 */
public class TreeAutomizerObserver implements IUnmanagedObserver {

	@Override
	public void init(ModelType modelType, int currentModelIndex, int numberOfModels) throws Throwable {
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
	public boolean process(IElement root) throws Throwable {
		
		Map<String, IAnnotations> st = root.getPayload().getAnnotations();
		HornAnnot annot = (HornAnnot) st.get("HoRNClauses");
		List<HornClause> hornClauses = (List<HornClause>) annot.getAnnotationsAsMap().get("HoRNClauses");

		TreeAutomatonBU<HCTransFormula, HornClausePredicateSymbol> tree = new TreeAutomatonBU<>();
		
		for (HornClause clause : hornClauses) {
			List<HornClausePredicateSymbol> tail = new ArrayList<HornClausePredicateSymbol>();
			tail.addAll(clause.getTailPredicates());
			tree.addRule(clause.getTransitionFormula(), tail, clause.getHeadPredicate());
		}
		
		// TODO(mostafa): Add initial and final states.
		tree.addFinalState(new HornClausePredicateSymbol.HornClauseFalsePredicateSymbol());
		//tree.addFinalState(state);
		//tree.addInitialState(state);
		return false;
	}

}
