/*
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.ModelCheckerUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalStore;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.LexicographicCounter;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 *
 * 
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class ElimStorePlain {

	private final int mQuantifier;
	private final Script mScript;
	private final ManagedScript mMgdScript;
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final SimplificationTechnique mSimplificationTechnique;
	private final static String s_FreshVariableString = "arrayElim";

	public ElimStorePlain(final Script script, final ManagedScript mgdScript, final IUltimateServiceProvider services,
			final SimplificationTechnique simplificationTechnique) {
		super();
		mQuantifier = QuantifiedFormula.EXISTS;
		mScript = script;
		mMgdScript = mgdScript;
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(ModelCheckerUtils.PLUGIN_ID);
		mSimplificationTechnique = simplificationTechnique;
	}

	void elim1(final TermVariable eliminatee, final Term term) {
		final List<MultiDimensionalStore> stores = extractStores(eliminatee, term);
		if (stores.size() > 1) {
			throw new AssertionError("not yet supported");
		}
		final MultiDimensionalStore store = stores.iterator().next();
		final List<MultiDimensionalSelect> selects = extractSelects(eliminatee, term);
		
		final HashRelation<Term, MultiDimensionalSelect> equivalentIndex = null;
		final HashRelation<Term, MultiDimensionalSelect> distinctIndex = null;
		final HashRelation<Term, MultiDimensionalSelect> unknownIndex = null;
		
		final Map<MultiDimensionalSelect, TermVariable> oldCellMapping = null;
		final List<Term> unk = new ArrayList<Term>(unknownIndex.getDomain());
		final int[] numberOfValues = new int[unknownIndex.size()];
		Arrays.fill(numberOfValues, 2);
		final LexicographicCounter lc = new LexicographicCounter(numberOfValues);
		final TermVariable newAuxArray = null;
		final Map<Term, Term> indexMapping = new HashMap<>();
		do {
			final Map<Term, Term> substitutionMapping = new HashMap<>();
			for (final Entry<Term, MultiDimensionalSelect> entry : equivalentIndex.entrySet()) {
				substitutionMapping.put(entry.getValue().getSelectTerm(), oldCellMapping.get(entry.getValue()));
			}
			for (final Entry<Term, MultiDimensionalSelect> entry : distinctIndex.entrySet()) {
				substitutionMapping.put(entry.getValue().getSelectTerm(), mMgdScript.getScript().term("select", newAuxArray, indexMapping.get(entry.getValue().getIndex())));
			}
			int offset = 0;
			for (final Term u : unk) {
				if (lc.getCurrentValue()[offset] == 0) {
					// equal
				} else {
					// different
				}
				offset++;
			}
			
			new Substitution(mMgdScript, substitutionMapping);
			
		} while (lc.isZero());
		
	}

	private List<MultiDimensionalStore> extractStores(final TermVariable eliminatee, final Term term) {
		final List<MultiDimensionalStore> result = new ArrayList<>();
		final Set<ApplicationTerm> stores = new ApplicationTermFinder("store", false).findMatchingSubterms(term);
		for (final ApplicationTerm appTerm : stores) {
			if (appTerm.getParameters()[0].equals(eliminatee)) {
				result.add(new MultiDimensionalStore(appTerm));
			}
		}
		return result;
	}
	
	private List<MultiDimensionalSelect> extractSelects(final TermVariable eliminatee, final Term term) {
		final List<MultiDimensionalSelect> result = new ArrayList<>();
		final Set<ApplicationTerm> stores = new ApplicationTermFinder("select", false).findMatchingSubterms(term);
		for (final ApplicationTerm appTerm : stores) {
			if (appTerm.getParameters()[0].equals(eliminatee)) {
				result.add(new MultiDimensionalSelect(appTerm));
			}
		}
		return result;
	}

}
